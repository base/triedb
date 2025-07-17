use std::collections::BTreeMap;

use crate::{
    account::Account,
    context::TransactionContext,
    node::{
        encode_branch, Node, NodeError,
        NodeKind::{AccountLeaf, Branch},
        TrieValue,
    },
    page::SlottedPage,
    path::{AddressPath, StoragePath, ADDRESS_PATH_LENGTH, STORAGE_PATH_LENGTH},
};

use alloy_primitives::{map::B256Map, Bytes, B256, U256};
use alloy_rlp::{decode_exact, BytesMut};
use alloy_trie::{nybbles::common_prefix_length, Nibbles, EMPTY_ROOT_HASH};

use super::engine::{Error, StorageEngine};

/// A Merkle proof of an account and select storage slots.
#[derive(Default, Debug)]
pub struct AccountProof {
    pub hashed_address: Nibbles,
    pub account: Account,
    pub proof: BTreeMap<Nibbles, Bytes>,
    pub storage_proofs: B256Map<StorageProof>,
}

/// A Merkle proof of a storage slot.
#[derive(Default, Debug)]
pub struct StorageProof {
    pub hashed_slot: Nibbles,
    pub value: U256,
    pub proof: BTreeMap<Nibbles, Bytes>,
}

impl StorageEngine {
    /// Retrieves an [AccountProof] from the storage engine, identified by the given
    /// [AddressPath]. Returns [None] if the path is not found.
    pub fn get_account_with_proof(
        &self,
        context: &TransactionContext,
        address_path: AddressPath,
    ) -> Result<Option<AccountProof>, Error> {
        self.get_value_with_proof(context, address_path.into())
    }

    /// Retrieves an [AccountProof] from the storage engine, containing the storage proof for the
    /// given [StoragePath]. Returns [None] if the path is not found.
    pub fn get_storage_with_proof(
        &self,
        context: &TransactionContext,
        storage_path: StoragePath,
    ) -> Result<Option<AccountProof>, Error> {
        self.get_value_with_proof(context, storage_path.into())
    }

    fn get_value_with_proof(
        &self,
        context: &TransactionContext,
        path: Nibbles,
    ) -> Result<Option<AccountProof>, Error> {
        assert!(
            path.len() == ADDRESS_PATH_LENGTH || path.len() == STORAGE_PATH_LENGTH,
            "path must be exactly {ADDRESS_PATH_LENGTH} or {STORAGE_PATH_LENGTH} nibbles"
        );

        let root_node_page_id = match context.root_node_page_id {
            None => return Ok(None),
            Some(page_id) => page_id,
        };

        let account_proof = AccountProof {
            hashed_address: path.slice(..ADDRESS_PATH_LENGTH).clone(),
            ..Default::default()
        };
        let slotted_page = self.get_slotted_page(context, root_node_page_id)?;
        let proof =
            self.get_value_with_proof_from_page(context, &path, 0, slotted_page, 0, account_proof)?;
        Ok(proof)
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
        mut proof: AccountProof,
    ) -> Result<Option<AccountProof>, Error> {
        let node: Node = slotted_page.get_value(page_index)?;

        let common_prefix_length =
            common_prefix_length(&original_path[path_offset..], node.prefix());
        if common_prefix_length < node.prefix().len() {
            return Ok(None);
        }

        let proof_node = node.rlp_encode();
        let full_node_path = original_path.slice(..path_offset);
        proof.proof.insert(full_node_path.clone(), Bytes::from(proof_node.to_vec()));

        let remaining_path = original_path.slice(path_offset + common_prefix_length..);
        if remaining_path.is_empty() {
            match node.value() {
                Ok(TrieValue::Account(account)) => {
                    proof.account = account;
                    return Ok(Some(proof));
                }
                Ok(TrieValue::Storage(_)) => {
                    return Err(Error::ProofError(
                        "storage value found for account path".to_string(),
                    ));
                }
                Err(NodeError::NoValue) => {
                    return Err(Error::ProofError("no value found for account path".to_string()));
                }
                Err(_) => {
                    return Err(Error::ProofError("unexpected error".to_string()));
                }
            }
        }

        assert!(path_offset <= 64);

        let prefix = node.prefix();
        match node.kind() {
            AccountLeaf { ref nonce_rlp, ref balance_rlp, ref code_hash, ref storage_root } => {
                assert_eq!(path_offset + common_prefix_length, ADDRESS_PATH_LENGTH);

                let nonce: u64 = decode_exact(nonce_rlp)
                    .map_err(|e| Error::ProofError(format!("Failed to decode nonce: {e}")))?;
                let balance: U256 = decode_exact(balance_rlp)
                    .map_err(|e| Error::ProofError(format!("Failed to decode balance: {e}")))?;
                proof.account = Account::new(nonce, balance, EMPTY_ROOT_HASH, *code_hash);

                if let Some(storage_root) = storage_root {
                    proof.account.storage_root = storage_root.rlp().as_hash().unwrap();
                    let storage_proof =
                        StorageProof { hashed_slot: remaining_path.clone(), ..Default::default() };
                    let storage_location = storage_root.location();
                    let storage_proof = if storage_location.cell_index().is_some() {
                        self.get_storage_proof_from_page(
                            context,
                            &remaining_path,
                            0,
                            slotted_page,
                            storage_location.cell_index().unwrap(),
                            storage_proof,
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
                            storage_proof,
                        )?
                    };
                    match storage_proof {
                        Some(storage_proof) => {
                            proof.storage_proofs.insert(
                                B256::from_slice(&storage_proof.hashed_slot.pack()),
                                storage_proof,
                            );
                            return Ok(Some(proof));
                        }
                        None => {
                            return Ok(None);
                        }
                    }
                }
                Ok(None)
            }
            Branch { ref children } => {
                if !prefix.is_empty() {
                    // extension + branch
                    let branch_path = original_path.slice(..path_offset + common_prefix_length);
                    let mut branch_rlp = BytesMut::new();
                    encode_branch(children, &mut branch_rlp);
                    proof.proof.insert(branch_path.clone(), branch_rlp.freeze().into());
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
        mut proof: StorageProof,
    ) -> Result<Option<StorageProof>, Error> {
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
            proof.proof.insert(full_node_path, Bytes::from(proof_node.to_vec()));
            match node.value() {
                Ok(TrieValue::Storage(storage_value)) => {
                    proof.value = storage_value;
                    return Ok(Some(proof));
                }
                Ok(TrieValue::Account(_)) => {
                    return Err(Error::ProofError(
                        "account value found for storage path".to_string(),
                    ));
                }
                Err(NodeError::NoValue) => {
                    return Err(Error::ProofError("no value found for storage path".to_string()));
                }
                Err(_) => {
                    return Err(Error::ProofError("unexpected error".to_string()));
                }
            }
        }

        assert!(path_offset <= 64);

        let prefix = node.prefix();
        match node.kind() {
            Branch { ref children } => {
                // update account subtree for branch node or branch+extension node
                let full_node_path = original_path.slice(..path_offset);
                let proof_node = node.rlp_encode();
                proof.proof.insert(full_node_path, Bytes::from(proof_node.to_vec()));

                if !prefix.is_empty() {
                    // extension + branch
                    let branch_path = original_path.slice(..path_offset + common_prefix_length);
                    let mut branch_rlp = BytesMut::new();
                    encode_branch(children, &mut branch_rlp);
                    proof.proof.insert(branch_path.clone(), branch_rlp.freeze().into());
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
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{address, b256, hex, U256};
    use alloy_rlp::encode;
    use alloy_trie::{proof::verify_proof, TrieAccount, KECCAK_EMPTY};

    use super::*;
    use crate::storage::test_utils::{create_test_account, create_test_cache, create_test_engine};

    fn verify_account_proof(proof: &AccountProof, root: B256) {
        let expected = Some(encode(TrieAccount {
            nonce: proof.account.nonce,
            balance: proof.account.balance,
            storage_root: proof.account.storage_root,
            code_hash: proof.account.code_hash,
        }));
        verify_proof(root, proof.hashed_address.clone(), expected, proof.proof.values())
            .expect("failed to verify account proof");

        for storage_proof in proof.storage_proofs.values() {
            verify_storage_proof(storage_proof, proof.account.storage_root);
        }
    }

    fn verify_storage_proof(proof: &StorageProof, root: B256) {
        verify_proof(
            root,
            proof.hashed_slot.clone(),
            Some(alloy_rlp::encode(proof.value)),
            proof.proof.values(),
        )
        .expect("failed to verify storage proof");
    }

    #[test]
    fn test_get_nonexistent_proof() {
        let (storage_engine, mut context) = create_test_engine(2000);
        let cache = create_test_cache();

        // the account and storage slot are not present in the trie
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
                &cache,
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

    #[test]
    fn test_get_proof() {
        let (storage_engine, mut context) = create_test_engine(2000);
        let cache = create_test_cache();

        // 1. insert a single account
        let address = address!("0x0000000000000000000000000000000000000001");
        let path = AddressPath::for_address(address);
        let account = create_test_account(1, 1);

        storage_engine
            .set_values(
                &mut context,
                &cache,
                vec![(path.clone().into(), Some(account.clone().into()))].as_mut(),
            )
            .unwrap();

        let proof = storage_engine.get_account_with_proof(&context, path.clone()).unwrap().unwrap();
        assert_eq!(proof.account, account);

        assert_eq!(proof.proof.len(), 1);
        assert!(proof.proof.contains_key(&Nibbles::default()));
        let leaf_node_proof = proof.proof.get(&Nibbles::default()).unwrap();
        assert_eq!(leaf_node_proof, &Bytes::from(hex!("0xf86aa1201468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357db846f8440101a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")));

        assert_eq!(proof.storage_proofs.len(), 0);

        verify_account_proof(&proof, context.root_node_hash);

        // 2. insert a new account so that both accounts are under the same top-level branch node
        let address2 = address!("0x0000000000000000000000000000000000000002");
        let path2 = AddressPath::for_address(address2);
        let account2 = create_test_account(2, 2);

        storage_engine
            .set_values(
                &mut context,
                &cache,
                vec![(path2.clone().into(), Some(account2.into()))].as_mut(),
            )
            .unwrap();

        let proof = storage_engine.get_account_with_proof(&context, path.clone()).unwrap().unwrap();
        assert_eq!(proof.account, account);

        assert_eq!(proof.proof.len(), 2, "Proof should contain a branch and a leaf");
        assert!(proof.proof.contains_key(&Nibbles::default()));
        let branch_node_proof = proof.proof.get(&Nibbles::default()).unwrap();
        assert_eq!(branch_node_proof, &Bytes::from(hex!("0xf85180a0bf57afd571ba1e3c86b9109b8e1f3ea231a24a298029b7bc804ed53788918a5f8080808080808080808080a0687b2ec5bde2a80c990485ab23c35513c3180ddc6e7fea67986bbce7eee06a47808080")));
        let leaf_node_proof = proof.proof.get(&Nibbles::from_nibbles([1])).unwrap();
        assert_eq!(leaf_node_proof, &Bytes::from(hex!("0xf869a03468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357db846f8440101a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")));

        assert_eq!(proof.storage_proofs.len(), 0);

        verify_account_proof(&proof, context.root_node_hash);

        // 3. insert a new storage slot for the first account
        let storage_path = StoragePath::for_address_and_slot(
            address,
            b256!("0x0000000000000000000000000000000000000000000000000000000000000001"),
        );
        let storage_value = U256::from(0xdeadbeefu64);

        storage_engine
            .set_values(
                &mut context,
                &cache,
                vec![(storage_path.clone().into(), Some(TrieValue::from(storage_value)))].as_mut(),
            )
            .unwrap();

        let account_proof =
            storage_engine.get_account_with_proof(&context, path.clone()).unwrap().unwrap();
        assert_eq!(
            account_proof.account,
            Account::new(
                1,
                U256::from(1),
                b256!("0x2a2ec95a7e5360e7e4bee7c204bbdfdb16ad550f1e3e53d2ee2fafa31dfb4013"),
                KECCAK_EMPTY
            )
        );

        let storage_proof =
            storage_engine.get_storage_with_proof(&context, storage_path.clone()).unwrap().unwrap();
        assert_eq!(storage_proof.storage_proofs.len(), 1);

        // both proofs should be the same except for the storage proof
        assert_eq!(account_proof.account, storage_proof.account);
        assert_eq!(account_proof.proof, storage_proof.proof);
        assert_eq!(account_proof.storage_proofs.len(), 0);

        // account-level proof should be the same as before, except with new hashes due to the new
        // storage value
        assert_eq!(storage_proof.proof.len(), 2, "Proof should contain a branch and a leaf");
        let branch_node_proof = storage_proof.proof.get(&Nibbles::default()).unwrap();
        assert_eq!(branch_node_proof, &Bytes::from(hex!("0xf85180a057f0c70887b1c7a8e0e1b7c8945a3e9c2a28e82ac5594b10786171f4e30748f08080808080808080808080a0687b2ec5bde2a80c990485ab23c35513c3180ddc6e7fea67986bbce7eee06a47808080")));
        let leaf_node_proof = storage_proof.proof.get(&Nibbles::from_nibbles([1])).unwrap();
        assert_eq!(leaf_node_proof, &Bytes::from(hex!("0xf869a03468288056310c82aa4c01a7e12a10f8111a0560e72b700555479031b86c357db846f8440101a02a2ec95a7e5360e7e4bee7c204bbdfdb16ad550f1e3e53d2ee2fafa31dfb4013a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")));

        let storage_slot_proof = storage_proof
            .storage_proofs
            .get(&B256::from_slice(&storage_path.get_slot().pack()))
            .unwrap();
        assert_eq!(
            account_proof.account.storage_root,
            b256!("0x2a2ec95a7e5360e7e4bee7c204bbdfdb16ad550f1e3e53d2ee2fafa31dfb4013")
        );
        assert_eq!(storage_slot_proof.proof.len(), 1);
        let storage_proof_node = storage_slot_proof.proof.get(&Nibbles::default()).unwrap();
        assert_eq!(storage_proof_node, &Bytes::from(hex!("0xe8a120b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf68584deadbeef")));

        verify_storage_proof(storage_slot_proof, account_proof.account.storage_root);

        verify_account_proof(&storage_proof, context.root_node_hash);
    }
}
