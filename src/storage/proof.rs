use alloy_primitives::StorageValue;
use reth_trie_common::MultiProof;

use crate::{
    account::Account,
    context::TransactionContext,
    database::Error,
    page::PageManager,
    path::{AddressPath, StoragePath},
};

use super::engine::StorageEngine;

impl<P: PageManager> StorageEngine<P> {
    pub fn get_account_with_proof(
        &self,
        context: &TransactionContext,
        address_path: AddressPath,
    ) -> Result<Option<(Account, MultiProof)>, Error> {
        todo!()
    }

    pub fn get_storage_with_proof(
        &self,
        context: &TransactionContext,
        storage_path: StoragePath,
    ) -> Result<Option<(StorageValue, MultiProof)>, Error> {
        todo!()
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
