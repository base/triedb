use crate::{
    context::TransactionContext,
    meta::{MetadataManager, OpenMetadataError},
    metrics::DatabaseMetrics,
    page::{PageError, PageManager},
    storage::engine::{self, StorageEngine},
    transaction::{Transaction, TransactionError, TransactionManager, RO, RW},
};
use alloy_primitives::B256;
use parking_lot::RwLock;
use std::{io, path::Path};

#[derive(Debug)]
pub struct Database {
    pub(crate) inner: Inner,
    metrics: DatabaseMetrics,
}

#[derive(Debug)]
pub(crate) struct Inner {
    pub(crate) storage_engine: RwLock<StorageEngine>,
    pub(crate) transaction_manager: RwLock<TransactionManager>,
}

#[derive(Debug)]
pub enum Error {
    PageError(PageError),
    EngineError(engine::Error),
}

#[derive(Debug)]
pub enum OpenError {
    PageError(PageError),
    MetadataError(OpenMetadataError),
    IO(io::Error),
}

impl Database {
    pub fn create(path: impl AsRef<Path>) -> Result<Self, OpenError> {
        let db_file_path = path.as_ref();

        let mut meta_file_path = db_file_path.to_path_buf();
        meta_file_path.as_mut_os_string().push(".meta");
        let mut meta_manager =
            MetadataManager::open(meta_file_path).map_err(OpenError::MetadataError)?;

        let mut page_manager = PageManager::options()
            .create_new(true)
            .open(db_file_path)
            .map_err(OpenError::PageError)?;

        // TODO: Allocate the first 256 pages because the existing code requires them. Remove this
        // later.
        for i in 0..256 {
            let page = page_manager.allocate(0).map_err(OpenError::PageError)?;
            assert_eq!(page.id(), i);
        }
        meta_manager.dirty_slot_mut().set_page_count(256);

        page_manager.commit().map_err(OpenError::PageError)?;
        meta_manager.commit().map_err(OpenError::IO)?;

        Ok(Self::new(StorageEngine::new(page_manager, meta_manager)))
    }

    pub fn open(path: impl AsRef<Path>) -> Result<Self, OpenError> {
        let db_file_path = path.as_ref();

        let mut meta_file_path = db_file_path.to_path_buf();
        meta_file_path.as_mut_os_string().push(".meta");
        let meta_manager =
            MetadataManager::open(meta_file_path).map_err(OpenError::MetadataError)?;

        let page_count = meta_manager.active_slot().page_count();
        let page_manager = PageManager::options()
            .create(false)
            .page_count(page_count)
            .open(db_file_path)
            .map_err(OpenError::PageError)?;

        Ok(Self::new(StorageEngine::new(page_manager, meta_manager)))
    }

    pub fn new(storage_engine: StorageEngine) -> Self {
        Self {
            inner: Inner {
                storage_engine: RwLock::new(storage_engine),
                transaction_manager: RwLock::new(TransactionManager::new()),
            },
            metrics: DatabaseMetrics::default(),
        }
    }

    pub fn print_page<W: io::Write>(self, buf: W, page_id: Option<u32>) -> Result<(), Error> {
        let storage_engine = self.inner.storage_engine.read();
        let context = storage_engine.read_context();
        // TODO: Must use `expect()` because `storage::engine::Error` and `database::Error` are not
        // compatible. There's probably no reason to use two different error enums here, so maybe
        // we should unify them. Or maybe we could just rely on `std::io::Error`.
        storage_engine.print_page(&context, buf, page_id).expect("write failed");
        Ok(())
    }

    pub fn begin_rw(&self) -> Result<Transaction<'_, RW>, TransactionError> {
        let mut transaction_manager = self.inner.transaction_manager.write();
        let mut storage_engine = self.inner.storage_engine.write();
        let metadata = storage_engine.metadata().dirty_slot();
        let min_snapshot_id = transaction_manager.begin_rw(metadata.snapshot_id())?;
        if min_snapshot_id > 0 {
            storage_engine.unlock(min_snapshot_id - 1);
        }
        let context = storage_engine.write_context();
        Ok(Transaction::new(context, self))
    }

    pub fn begin_ro(&self) -> Result<Transaction<'_, RO>, TransactionError> {
        let mut transaction_manager = self.inner.transaction_manager.write();
        let storage_engine = self.inner.storage_engine.read();
        let metadata = storage_engine.metadata().active_slot();
        transaction_manager.begin_ro(metadata.snapshot_id())?;
        let context = storage_engine.read_context();
        Ok(Transaction::new(context, self))
    }

    pub fn state_root(&self) -> B256 {
        self.inner.storage_engine.read().metadata().active_slot().root_node_hash()
    }

    pub fn close(mut self) -> Result<(), Error> {
        self.commit()
    }

    fn commit(&mut self) -> Result<(), Error> {
        let mut storage_engine = self.inner.storage_engine.write();
        let context = storage_engine.write_context();
        storage_engine.commit(&context).map_err(Error::EngineError)
    }

    pub fn size(&self) -> u32 {
        let storage_engine = self.inner.storage_engine.read();
        storage_engine.size()
    }

    pub fn update_metrics_ro(&self, context: &TransactionContext) {
        self.metrics
            .ro_transaction_pages_read
            .record(context.transaction_metrics.take_pages_read() as f64);

        let (cache_storage_read_hit, cache_storage_read_miss) =
            context.transaction_metrics.take_cache_storage_read();
        self.metrics.cache_storage_read_hit.increment(cache_storage_read_hit as u64);
        self.metrics.cache_storage_read_miss.increment(cache_storage_read_miss as u64);
    }

    pub fn update_metrics_rw(&self, context: &TransactionContext) {
        self.metrics
            .rw_transaction_pages_read
            .record(context.transaction_metrics.take_pages_read() as f64);
        self.metrics
            .rw_transaction_pages_allocated
            .record(context.transaction_metrics.take_pages_allocated() as f64);
        self.metrics
            .rw_transaction_pages_reallocated
            .record(context.transaction_metrics.take_pages_reallocated() as f64);
        self.metrics
            .rw_transaction_pages_split
            .record(context.transaction_metrics.take_pages_split() as f64);
    }
}

impl Drop for Database {
    fn drop(&mut self) {
        self.commit().expect("failed to close database")
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::{address, U256};
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
    use std::fs::File;
    use tempdir::TempDir;

    use crate::{account::Account, page::Page, path::AddressPath};

    use super::*;

    #[test]
    fn test_set_get_account() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create(file_path).unwrap();

        let address = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");

        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(AddressPath::for_address(address), Some(account1.clone())).unwrap();

        tx.commit().unwrap();

        let account2 = Account::new(456, U256::from(123), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(AddressPath::for_address(address), Some(account2.clone())).unwrap();

        let mut ro_tx = db.begin_ro().unwrap();
        tx.commit().unwrap();

        // The read transaction was created before the write was committed, so it should not see the
        // changes.
        let read_account = ro_tx.get_account(AddressPath::for_address(address)).unwrap();

        assert_eq!(account1, read_account.unwrap());

        // The writer transaction is committed, so the read transaction should see the changes.
        let mut ro_tx = db.begin_ro().unwrap();

        let read_account = ro_tx.get_account(AddressPath::for_address(address)).unwrap();

        assert_eq!(account2, read_account.unwrap());

        // cleanup
        tmp_dir.close().unwrap();
    }

    #[test]
    fn test_open_resize() {
        // GIVEN: a database
        //
        // create the database on disk. currently this
        // will create a database with N pages (see 'create' for N).
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let _db = Database::create(&file_path).unwrap();

        // WHEN: the database is opened
        let db = Database::open(&file_path).unwrap();

        // THEN: the size of the database should be the
        // max_page_size + buffer
        let open_size = db.size();
        let max_page_size = 255; // fresh db has root pages + reserved orphan pages
        assert!(open_size >= max_page_size);

        // cleanup
        tmp_dir.close().unwrap();
    }

    #[test]
    fn test_close_resize() {
        // GIVEN: a database
        //
        // create the database on disk. currently this
        // will create a database with N pages (see 'create' for N).
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create(&file_path).unwrap();
        let create_size = db.size();
        assert!(create_size >= 256);

        // WHEN: the database is closed
        db.close().unwrap();

        // THEN: the size of the database should be at least large enough to contain
        // `max_page_size`
        let max_page_size = 256; // fresh db so at least 256 pages for the root pages + orphan pages
        let file = File::options().read(true).open(&file_path).unwrap();
        let file_len = file.metadata().unwrap().len();
        assert!(file_len >= max_page_size * Page::SIZE as u64);

        // cleanup
        tmp_dir.close().unwrap();
    }

    #[test]
    fn test_auto_close_database() {
        // GIVEN: a database
        //
        // create the database on disk. currently this
        // will create a database with N pages (see 'create' for N).
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");

        {
            let db = Database::create(&file_path).unwrap();

            let create_size = db.size();
            assert!(create_size >= 256);
        }

        // WHEN: the database is dropped from scope
        // THEN: the database should be closed and the file should be truncated
        let max_page_size = 256; // fresh db so at least 256 pages for the root pages + orphan pages
        let file = File::options().read(true).open(&file_path).unwrap();
        let file_len = file.metadata().unwrap().len();
        assert!(file_len >= max_page_size * Page::SIZE as u64);

        // cleanup
        tmp_dir.close().unwrap();
    }

    #[test]
    fn test_data_persistence() {
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create(&file_path).unwrap();

        let address1 = address!("0xd8da6bf26964af9d7eed9e03e53415d37aa96045");
        let account1 = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);

        let mut tx = db.begin_rw().unwrap();
        tx.set_account(AddressPath::for_address(address1), Some(account1.clone())).unwrap();

        tx.commit().unwrap();
        db.close().unwrap();

        let db = Database::open(&file_path).unwrap();
        let mut tx = db.begin_ro().unwrap();
        let account = tx.get_account(AddressPath::for_address(address1)).unwrap().unwrap();
        assert_eq!(account, account1);

        tx.commit().unwrap();

        let address2 = address!("0x1234567890abcdef1234567890abcdef12345678");
        let account2 = Account::new(2, U256::from(200), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(AddressPath::for_address(address2), Some(account2.clone())).unwrap();

        tx.commit().unwrap();
        db.close().unwrap();

        let db = Database::open(&file_path).unwrap();
        let mut tx = db.begin_ro().unwrap();

        let account = tx.get_account(AddressPath::for_address(address1)).unwrap().unwrap();
        assert_eq!(account, account1);

        let account = tx.get_account(AddressPath::for_address(address2)).unwrap().unwrap();
        assert_eq!(account, account2);
    }
}
