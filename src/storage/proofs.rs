use crate::{
    account::Account,
    context::TransactionContext,
    node::{
        encode_branch,
        Node::{self, AccountLeaf, Branch},
        TrieValue,
    },
    page::{PageManager, SlottedPage},
    path::{AddressPath, StoragePath, ADDRESS_PATH_LENGTH},
    pointer::Pointer,
};

use alloy_primitives::{Bytes, StorageValue, B256};
use alloy_rlp::BytesMut;
use alloy_trie::{nybbles::common_prefix_length, Nibbles, TrieMask};

use reth_trie_common::{MultiProof, StorageMultiProof};

use super::engine::Error;

use super::engine::StorageEngine;

impl<P: PageManager> StorageEngine<P> {
    pub fn get_account_with_proof(
        &self,
        context: &TransactionContext,
        address_path: AddressPath,
    ) -> Result<Option<(Account, MultiProof)>, Error> {
        let result = self.get_value_with_proof(context, address_path.into())?;
        match result {
            Some((TrieValue::Account(account), proof)) => Ok(Some((account, proof))),
            Some((TrieValue::Storage(_), _)) => panic!("storage proof found for account path"),
            None => Ok(None),
        }
    }

    pub fn get_storage_with_proof(
        &self,
        context: &TransactionContext,
        storage_path: StoragePath,
    ) -> Result<Option<(StorageValue, MultiProof)>, Error> {
        let result = self.get_value_with_proof(context, storage_path.into())?;
        match result {
            Some((TrieValue::Storage(storage_value), proof)) => Ok(Some((storage_value, proof))),
            Some((TrieValue::Account(_), _)) => panic!("account proof found for storage path"),
            None => Ok(None),
        }
    }

    fn get_value_with_proof(
        &self,
        context: &TransactionContext,
        path: Nibbles,
    ) -> Result<Option<(TrieValue, MultiProof)>, Error> {
        if context.metadata.root_subtrie_page_id == 0 {
            return Ok(None);
        }

        let slotted_page = self.get_slotted_page(context, context.metadata.root_subtrie_page_id)?;
        let mut proof = MultiProof::default();
        let value =
            self.get_value_with_proof_from_page(context, &path, 0, slotted_page, 0, &mut proof)?;
        Ok(value.map(|value| (value, proof)))
    }

    /// Retrieves a [TrieValue] from the given page or any of its descendants.
    /// Returns [None] if the path is not found.
    fn get_value_with_proof_from_page(
        &self,
        context: &TransactionContext,
        original_path: &Nibbles,
        path_offset: usize,
        slotted_page: SlottedPage<'_>,
        page_index: u8,
        proof: &mut MultiProof,
    ) -> Result<Option<TrieValue>, Error> {
        let node: Node = slotted_page.get_value(page_index)?;

        let common_prefix_length =
            common_prefix_length(&original_path[path_offset..], node.prefix());
        if common_prefix_length < node.prefix().len() {
            return Ok(None);
        }

        let proof_node = node.rlp_encode();
        let full_node_path = original_path.slice(..path_offset);
        proof.account_subtree.insert(full_node_path.clone(), Bytes::from(proof_node.to_vec()));

        let remaining_path = original_path.slice(path_offset + common_prefix_length..);
        if remaining_path.is_empty() {
            return Ok(Some(node.value()?));
        }

        assert!(path_offset <= 64);

        match node {
            AccountLeaf { ref storage_root, .. } => {
                assert_eq!(path_offset + common_prefix_length, ADDRESS_PATH_LENGTH);

                if let Some(storage_root) = storage_root {
                    let mut storage_proof = StorageMultiProof::empty();
                    storage_proof.root = storage_root.rlp().as_hash().unwrap();
                    let storage_location = storage_root.location();
                    let storage_value = if storage_location.cell_index().is_some() {
                        self.get_storage_proof_from_page(
                            context,
                            &remaining_path,
                            0,
                            slotted_page,
                            storage_location.cell_index().unwrap(),
                            &mut storage_proof,
                        )?
                    } else {
                        let child_page_id = storage_location.page_id().unwrap();
                        let child_slotted_page = self.get_slotted_page(context, child_page_id)?;
                        self.get_storage_proof_from_page(
                            context,
                            &remaining_path,
                            0,
                            child_slotted_page,
                            0,
                            &mut storage_proof,
                        )?
                    };
                    let account_path = original_path.slice(..path_offset + common_prefix_length);
                    proof.storages.insert(B256::from_slice(&account_path.pack()), storage_proof);
                    return Ok(storage_value);
                }
                Ok(None)
            }
            Branch { ref prefix, ref children, .. } => {
                if prefix.is_empty() {
                    // true branch node
                    proof
                        .branch_node_hash_masks
                        .insert(full_node_path.clone(), Self::hash_mask(children));
                    proof.branch_node_tree_masks.insert(full_node_path, Self::tree_mask(children));
                } else {
                    // extension + branch
                    let branch_path = original_path.slice(..path_offset + common_prefix_length);
                    let mut branch_rlp = BytesMut::new();
                    encode_branch(children, &mut branch_rlp);
                    proof.account_subtree.insert(branch_path.clone(), branch_rlp.freeze().into());
                    proof
                        .branch_node_hash_masks
                        .insert(branch_path.clone(), Self::hash_mask(children));
                    proof.branch_node_tree_masks.insert(branch_path, Self::tree_mask(children));
                }

                // go down the trie
                let child_pointer = children[remaining_path[0] as usize].as_ref();
                let new_path_offset = path_offset + common_prefix_length + 1;

                match child_pointer {
                    Some(child_pointer) => {
                        let child_location = child_pointer.location();
                        if child_location.cell_index().is_some() {
                            self.get_value_with_proof_from_page(
                                context,
                                original_path,
                                new_path_offset,
                                slotted_page,
                                child_location.cell_index().unwrap(),
                                proof,
                            )
                        } else {
                            let child_page_id = child_location.page_id().unwrap();
                            let child_slotted_page =
                                self.get_slotted_page(context, child_page_id)?;
                            self.get_value_with_proof_from_page(
                                context,
                                original_path,
                                new_path_offset,
                                child_slotted_page,
                                0,
                                proof,
                            )
                        }
                    }
                    None => Ok(None),
                }
            }
            _ => unreachable!(),
        }
    }

    fn get_storage_proof_from_page(
        &self,
        context: &TransactionContext,
        original_path: &Nibbles,
        path_offset: usize,
        slotted_page: SlottedPage<'_>,
        page_index: u8,
        proof: &mut StorageMultiProof,
    ) -> Result<Option<TrieValue>, Error> {
        let node: Node = slotted_page.get_value(page_index)?;

        let common_prefix_length =
            common_prefix_length(&original_path[path_offset..], node.prefix());
        if common_prefix_length < node.prefix().len() {
            return Ok(None);
        }

        let remaining_path = original_path.slice(path_offset + common_prefix_length..);
        if remaining_path.is_empty() {
            let full_node_path = original_path.slice(..path_offset);
            let proof_node = node.rlp_encode();
            proof.subtree.insert(full_node_path, Bytes::from(proof_node.to_vec()));
            return Ok(Some(node.value()?));
        }

        assert!(path_offset <= 64);

        match node {
            Branch { ref prefix, ref children, .. } => {
                // update account subtree for branch node or branch+extension node
                let full_node_path = original_path.slice(..path_offset);
                let proof_node = node.rlp_encode();
                proof.subtree.insert(full_node_path.clone(), Bytes::from(proof_node.to_vec()));

                if prefix.is_empty() {
                    // true branch node
                    proof
                        .branch_node_hash_masks
                        .insert(full_node_path.clone(), Self::hash_mask(children));
                    proof.branch_node_tree_masks.insert(full_node_path, Self::tree_mask(children));
                } else {
                    // extension + branch
                    let branch_path = original_path.slice(..path_offset + common_prefix_length);
                    let mut branch_rlp = BytesMut::new();
                    encode_branch(children, &mut branch_rlp);
                    proof.subtree.insert(branch_path.clone(), branch_rlp.freeze().into());
                    proof
                        .branch_node_hash_masks
                        .insert(branch_path.clone(), Self::hash_mask(children));
                    proof.branch_node_tree_masks.insert(branch_path, Self::tree_mask(children));
                }

                let child_pointer = children[remaining_path[0] as usize].as_ref();
                let new_path_offset = path_offset + common_prefix_length + 1;

                match child_pointer {
                    Some(child_pointer) => {
                        let child_location = child_pointer.location();
                        if child_location.cell_index().is_some() {
                            self.get_storage_proof_from_page(
                                context,
                                original_path,
                                new_path_offset,
                                slotted_page,
                                child_location.cell_index().unwrap(),
                                proof,
                            )
                        } else {
                            let child_page_id = child_location.page_id().unwrap();
                            let child_slotted_page =
                                self.get_slotted_page(context, child_page_id)?;
                            self.get_storage_proof_from_page(
                                context,
                                original_path,
                                new_path_offset,
                                child_slotted_page,
                                0,
                                proof,
                            )
                        }
                    }
                    None => Ok(None),
                }
            }
            _ => unreachable!(),
        }
    }

    fn tree_mask(children: &[Option<Pointer>]) -> TrieMask {
        let mut mask = TrieMask::default();
        children.iter().enumerate().filter(|(_, child)| child.is_some()).for_each(|(i, _)| {
            mask.set_bit(i as u8);
        });
        mask
    }

    fn hash_mask(children: &[Option<Pointer>]) -> TrieMask {
        let mut mask = TrieMask::default();
        children
            .iter()
            .enumerate()
            .filter(
                |(_, child)| {
                    if let Some(child) = child {
                        child.rlp().as_hash().is_some()
                    } else {
                        false
                    }
                },
            )
            .for_each(|(i, _)| {
                mask.set_bit(i as u8);
            });
        mask
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{address, b256, hex, U256};
    use alloy_trie::{TrieMask, EMPTY_ROOT_HASH};

    use super::*;
    use crate::storage::test_utils::test_utils::{create_test_account, create_test_engine};

    #[test]
    fn test_get_proof() {
        let (storage_engine, mut context) = create_test_engine(2000);

        // insert a single account

        let address = address!("0x0000000000000000000000000000000000000001");
        let path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);

        storage_engine
            .set_values(
                &mut context,
                vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        let (read_account, proof) =
            storage_engine.get_account_with_proof(&context, path.clone()).unwrap().unwrap();
        assert_eq!(read_account.nonce, account.nonce);
        assert_eq!(read_account.balance, account.balance);
        assert_eq!(read_account.code_hash, account.code_hash);
        assert_eq!(read_account.storage_root, EMPTY_ROOT_HASH);

        assert_eq!(proof.account_subtree.len(), 1);
        assert!(proof.account_subtree.contains_key(&Nibbles::default()));
        let leaf_node_proof = proof.account_subtree.get(&Nibbles::default()).unwrap();
        assert_eq!(leaf_node_proof, &Bytes::from(hex!("0xf86aa1201468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357db846f8440101a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")));

        assert_eq!(proof.branch_node_hash_masks.len(), 0);
        assert_eq!(proof.branch_node_tree_masks.len(), 0);
        assert_eq!(proof.storages.len(), 0);

        let account_proof = proof.account_proof(address, &[]).unwrap();
        account_proof.verify(context.metadata.state_root).unwrap();

        // insert a new account so that both accounts are under the same top-level branch node

        let address2 = address!("0x0000000000000000000000000000000000000002");
        let path2 = AddressPath::for_address(address2);
        let account2 = create_test_account(2, 2);

        storage_engine
            .set_values(&mut context, vec![(path2.clone().into(), Some(account2.into()))].as_mut())
            .unwrap();

        let (read_account, proof) =
            storage_engine.get_account_with_proof(&context, path.clone()).unwrap().unwrap();
        assert_eq!(read_account.nonce, account.nonce);
        assert_eq!(read_account.balance, account.balance);
        assert_eq!(read_account.code_hash, account.code_hash);
        assert_eq!(read_account.storage_root, EMPTY_ROOT_HASH);

        assert_eq!(proof.account_subtree.len(), 2, "Proof should contain a branch and a leaf");
        assert!(proof.account_subtree.contains_key(&Nibbles::default()));
        let branch_node_proof = proof.account_subtree.get(&Nibbles::default()).unwrap();
        assert_eq!(branch_node_proof, &Bytes::from(hex!("0xf85180a0bf57afd571ba1e3c86b9109b8e1f3ea231a24a298029b7bc804ed53788918a5f8080808080808080808080a0687b2ec5bde2a80c990485ab23c35513c3180ddc6e7fea67986bbce7eee06a47808080")));
        let leaf_node_proof = proof.account_subtree.get(&Nibbles::from_nibbles([1])).unwrap();
        assert_eq!(leaf_node_proof, &Bytes::from(hex!("0xf869a03468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357db846f8440101a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")));

        assert_eq!(proof.branch_node_hash_masks.len(), 1);
        let hash_mask = proof.branch_node_hash_masks.get(&Nibbles::default()).unwrap();
        assert_eq!(hash_mask, &TrieMask::new(0b0010000000000010));
        assert_eq!(proof.branch_node_tree_masks.len(), 1);
        let tree_mask = proof.branch_node_tree_masks.get(&Nibbles::default()).unwrap();
        assert_eq!(tree_mask, &TrieMask::new(0b0010000000000010));
        assert_eq!(proof.storages.len(), 0);

        let account_proof = proof.account_proof(address, &[]).unwrap();
        account_proof.verify(context.metadata.state_root).unwrap();

        // insert a new storage slot for the first account

        let storage_path = StoragePath::for_address_and_slot(
            address,
            b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
        );
        let storage_value = U256::from(0xdeadbeefu64);

        storage_engine
            .set_values(
                &mut context,
                vec![(storage_path.clone().into(), Some(TrieValue::from(storage_value)))].as_mut(),
            )
            .unwrap();

        let (read_account, account_proof) =
            storage_engine.get_account_with_proof(&context, path.clone()).unwrap().unwrap();
        assert_eq!(read_account.nonce, account.nonce);
        assert_eq!(read_account.balance, account.balance);
        assert_eq!(read_account.code_hash, account.code_hash);
        assert_eq!(
            read_account.storage_root,
            b256!("0x2a2ec95a7e5360e7e4bee7c204bbdfdb16ad550f1e3e53d2ee2fafa31dfb4013")
        );

        let (read_storage, storage_proof) =
            storage_engine.get_storage_with_proof(&context, storage_path.clone()).unwrap().unwrap();
        assert_eq!(read_storage, storage_value);

        // both proofs should be the same except for the storage proof
        assert_eq!(account_proof.account_subtree, storage_proof.account_subtree);
        assert_eq!(account_proof.branch_node_hash_masks, storage_proof.branch_node_hash_masks);
        assert_eq!(account_proof.branch_node_tree_masks, storage_proof.branch_node_tree_masks);
        assert_eq!(account_proof.storages.len(), 0);

        // account-level proof should be the same as before, except with new hashes due to the new
        // storage value

        assert_eq!(
            storage_proof.account_subtree.len(),
            2,
            "Proof should contain a branch and a leaf"
        );
        assert!(storage_proof.account_subtree.contains_key(&Nibbles::default()));
        let branch_node_proof = storage_proof.account_subtree.get(&Nibbles::default()).unwrap();
        assert_eq!(branch_node_proof, &Bytes::from(hex!("0xf85180a057f0c70887b1c7a8e0e1b7c8945a3e9c2a28e82ac5594b10786171f4e30748f08080808080808080808080a0687b2ec5bde2a80c990485ab23c35513c3180ddc6e7fea67986bbce7eee06a47808080")));
        let leaf_node_proof =
            storage_proof.account_subtree.get(&Nibbles::from_nibbles([1])).unwrap();
        assert_eq!(leaf_node_proof, &Bytes::from(hex!("0xf869a03468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357db846f8440101a02a2ec95a7e5360e7e4bee7c204bbdfdb16ad550f1e3e53d2ee2fafa31dfb4013a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")));

        assert_eq!(storage_proof.branch_node_hash_masks.len(), 1);
        let hash_mask = storage_proof.branch_node_hash_masks.get(&Nibbles::default()).unwrap();
        assert_eq!(hash_mask, &TrieMask::new(0b0010000000000010));
        assert_eq!(storage_proof.branch_node_tree_masks.len(), 1);
        let tree_mask = storage_proof.branch_node_tree_masks.get(&Nibbles::default()).unwrap();
        assert_eq!(tree_mask, &TrieMask::new(0b0010000000000010));

        assert_eq!(storage_proof.storages.len(), 1);
        let storage_slot_proof = storage_proof
            .storages
            .get(&B256::from_slice(&storage_path.get_address().to_nibbles().pack()))
            .unwrap();
        assert_eq!(
            storage_slot_proof.root,
            b256!("0x2a2ec95a7e5360e7e4bee7c204bbdfdb16ad550f1e3e53d2ee2fafa31dfb4013")
        );
        assert_eq!(storage_slot_proof.subtree.len(), 1);
        let storage_proof_node = storage_slot_proof.subtree.get(&Nibbles::default()).unwrap();
        assert_eq!(storage_proof_node, &Bytes::from(hex!("0xe8a120b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf68584deadbeef")));
        assert_eq!(storage_slot_proof.branch_node_hash_masks.len(), 0);
        assert_eq!(storage_slot_proof.branch_node_tree_masks.len(), 0);

        let storage_slot_proof = storage_slot_proof
            .storage_proof(b256!(
                "0x0000000000000000000000000000000000000000000000000000000000000001"
            ))
            .unwrap();
        assert_eq!(
            storage_slot_proof.key,
            b256!("0x0000000000000000000000000000000000000000000000000000000000000001")
        );
        assert_eq!(&storage_slot_proof.nibbles, storage_path.get_slot());
        assert_eq!(storage_slot_proof.value, U256::from(0xdeadbeefu64));
        assert_eq!(storage_slot_proof.proof.len(), 1);
        assert_eq!(storage_slot_proof.proof[0], Bytes::from(hex!("0xe8a120b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf68584deadbeef")));
        storage_slot_proof
            .verify(b256!("0x2a2ec95a7e5360e7e4bee7c204bbdfdb16ad550f1e3e53d2ee2fafa31dfb4013"))
            .unwrap();
    }

    #[test]
    fn test_get_nonexistent_proof() {
        let (storage_engine, mut context) = create_test_engine(2000);

        let address = address!("0x0000000000000000000000000000000000000001");
        let path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        let proof = storage_engine.get_account_with_proof(&context, path.clone()).unwrap();
        assert!(proof.is_none());

        let storage_path = StoragePath::for_address_and_slot(
            address,
            b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
        );
        let proof = storage_engine.get_storage_with_proof(&context, storage_path.clone()).unwrap();
        assert!(proof.is_none());

        // insert the account
        storage_engine
            .set_values(
                &mut context,
                vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        // storage proof is still none

        let proof = storage_engine.get_storage_with_proof(&context, storage_path.clone()).unwrap();
        assert!(proof.is_none());

        // proof of another account is still none

        let address2 = address!("0x0000000000000000000000000000000000000002");
        let path2 = AddressPath::for_address(address2);
        let proof = storage_engine.get_account_with_proof(&context, path2.clone()).unwrap();
        assert!(proof.is_none());
    }
}
