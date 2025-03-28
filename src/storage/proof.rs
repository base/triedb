use std::cell;

use alloy_primitives::{Bytes, StorageValue, B256};
use alloy_rlp::BytesMut;
use alloy_trie::{Nibbles, TrieMask};
use reth_trie_common::{MultiProof, StorageMultiProof};

use crate::{
    account::{self, Account},
    context::TransactionContext,
    node::{encode_branch, Node, TrieValue},
    page::{PageManager, SlottedPage},
    path::{AddressPath, StoragePath, ADDRESS_PATH_LENGTH},
    pointer::Pointer,
    transaction::RO,
};

use super::engine::{Error, StorageEngine};

impl<P: PageManager> StorageEngine<P> {
    pub fn get_account_with_proof(
        &self,
        context: &TransactionContext,
        address_path: AddressPath,
    ) -> Result<Option<(Account, MultiProof)>, Error> {
        let result = self.get_value_with_proof(context, address_path.into())?;
        match result {
            Some((TrieValue::Account(account), proof)) => Ok(Some((account, proof))),
            Some((TrieValue::Storage(_), _)) => {
                panic!("storage node found for account path")
            }
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
            Some((TrieValue::Storage(storage), proof)) => Ok(Some((storage, proof))),
            Some((TrieValue::Account(_), _)) => panic!("account node found for storage path"),
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

    fn get_value_with_proof_from_page(
        &self,
        context: &TransactionContext,
        original_path: &Nibbles,
        path_offset: usize,
        slotted_page: SlottedPage<'_>,
        page_index: u8,
        proof: &mut MultiProof,
    ) -> Result<Option<TrieValue>, Error> {
        let node = slotted_page.get_value::<Node>(page_index)?;

        let common_prefix_length =
            original_path.slice(path_offset..).common_prefix_length(node.prefix());
        if common_prefix_length < node.prefix().len() {
            return Ok(None);
        }

        let node_proof = node.to_rlp_node();
        let full_node_path = original_path.slice(..path_offset);
        // update account subtree for leaf, or branch/branch+extension
        proof.account_subtree.insert(full_node_path.clone(), Bytes::from(node_proof.to_vec()));

        let remaining_path = original_path.slice(path_offset + common_prefix_length..);
        if remaining_path.is_empty() {
            return Ok(Some(node.value()));
        }

        match node {
            Node::AccountLeaf { ref storage_root, .. } => {
                assert_eq!(path_offset + common_prefix_length, ADDRESS_PATH_LENGTH);

                if let Some(storage_root) = storage_root {
                    let storage_location = storage_root.location();
                    let mut storage_proof = StorageMultiProof::empty();

                    let storage_value = match storage_location.cell_index() {
                        Some(cell_index) => self.get_storage_proof_from_page(
                            context,
                            &remaining_path,
                            0,
                            slotted_page,
                            cell_index,
                            &mut storage_proof,
                        )?,
                        None => {
                            let child_page_id = storage_location.page_id().unwrap();
                            let child_slotted_page =
                                self.get_slotted_page(context, child_page_id)?;
                            self.get_storage_proof_from_page(
                                context,
                                &remaining_path,
                                0,
                                child_slotted_page,
                                0,
                                &mut storage_proof,
                            )?
                        }
                    };
                    let account_path = original_path.slice(..path_offset + common_prefix_length);
                    proof.storages.insert(B256::from_slice(&account_path.pack()), storage_proof);

                    return Ok(storage_value);
                }
                Ok(None)
            }
            Node::Branch { ref children, ref prefix, .. } => {
                if prefix.is_empty() {
                    // node is a branch, update hash mask and tree mask for the branch
                    proof
                        .branch_node_hash_masks
                        .insert(full_node_path.clone(), Self::hash_mask(children));
                    proof.branch_node_tree_masks.insert(full_node_path, Self::tree_mask(children));
                } else {
                    // node is an extension + branch, update account subtree for the branch (the
                    // extension node added before with full_node_path), update hash mask and tree
                    // mask for the branch
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
                    None => Ok(None),
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
        todo!()
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
    use alloy_primitives::{address, b256, hex, Bytes, B256, U256};
    use alloy_trie::{Nibbles, EMPTY_ROOT_HASH, KECCAK_EMPTY};

    use crate::storage::test_common::test_common::{create_test_account, create_test_engine};

    use super::*;

    #[test]
    fn test_get_nonexistent_account_with_proof() {
        let (storage_engine, mut context) = create_test_engine(2000);
        let address = address!("0x0000000000000000000000000000000000000001");
        let path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        let storage_key =
            b256!("0x0000000000000000000000000000000000000000000000000000000000000000");
        let storage_path = StoragePath::for_address_and_slot(address, storage_key);

        // the account and storage are not present
        let proof = storage_engine.get_account_with_proof(&context, path.clone()).unwrap();
        assert!(proof.is_none());

        let proof = storage_engine.get_storage_with_proof(&context, storage_path.clone()).unwrap();
        assert!(proof.is_none());

        // insert account
        storage_engine
            .set_values(&mut context, vec![(path.clone().into(), Some(account.into()))].as_mut())
            .unwrap();

        // storage is not present
        let proof = storage_engine.get_storage_with_proof(&context, storage_path.clone()).unwrap();
        assert!(proof.is_none());

        // another account is not present
        let address1 = address!("0x0000000000000000000000000000000000000002");
        let path1 = AddressPath::for_address(address1);
        let proof = storage_engine.get_account_with_proof(&context, path1.clone()).unwrap();
        assert!(proof.is_none());
    }

    #[test]
    fn test_get_account_with_proof() {
        let (storage_engine, mut context) = create_test_engine(2000);
        let address = address!("0x0000000000000000000000000000000000000001");
        let path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);
        // let storage_key =
        //     b256!("0x0000000000000000000000000000000000000000000000000000000000000000");
        // let storage_path = StoragePath::for_address_and_slot(address, storage_key);

        storage_engine
            .set_values(&mut context, vec![(path.clone().into(), Some(account.into()))].as_mut())
            .unwrap();

        let (account, proof) =
            storage_engine.get_account_with_proof(&context, path.clone()).unwrap().unwrap();
        assert_eq!(account, Account::new(1, U256::from(1), EMPTY_ROOT_HASH, KECCAK_EMPTY));

        assert_eq!(proof.account_subtree.len(), 1);
        assert!(proof.account_subtree.contains_key(&Nibbles::default()));
        let leaf_node_proof = proof.account_subtree.get(&Nibbles::default()).unwrap();
        assert_eq!(leaf_node_proof, &Bytes::from(hex!("0xf86aa1201468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357db846f8440101a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")));

        assert_eq!(proof.branch_node_hash_masks.len(), 0);
        assert_eq!(proof.branch_node_tree_masks.len(), 0);
        assert_eq!(proof.storages.len(), 0);

        // todo: test storage proof
    }

    #[test]
    fn test_get_storage_with_proof() {
        todo!()
    }

    #[test]
    fn test_get_nonexistent_storage_with_proof() {
        todo!()
    }
}
