use reth_trie_common::MultiProof;

use crate::{
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
    ) -> Result<Option<MultiProof>, Error> {
        todo!()
    }

    pub fn get_storage_with_proof(
        &self,
        context: &TransactionContext,
        storage_path: StoragePath,
    ) -> Result<Option<MultiProof>, Error> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_nonexistent_account_with_proof() {
        let (storage_engine, context) = create_test_engine(2000);

        todo!()
    }

    #[test]
    fn test_get_account_with_proof() {
        todo!()
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
