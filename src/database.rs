use crate::{
    context::TransactionContext,
    meta::{MetadataManager, OpenMetadataError},
    metrics::DatabaseMetrics,
    page::{PageError, PageId, PageManager},
    storage::engine::{self, StorageEngine},
    transaction::{Transaction, TransactionError, TransactionManager, RO, RW},
};
use alloy_primitives::B256;
use parking_lot::Mutex;
use std::{collections::HashSet, io, path::Path};

#[derive(Debug)]
pub struct Database {
    pub(crate) storage_engine: StorageEngine,
    pub(crate) transaction_manager: Mutex<TransactionManager>,
    metrics: DatabaseMetrics,
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

        let meta_manager =
            MetadataManager::open(meta_file_path).map_err(OpenError::MetadataError)?;
        let page_manager = PageManager::options()
            .create_new(true)
            .open(db_file_path)
            .map_err(OpenError::PageError)?;

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
            storage_engine,
            transaction_manager: Mutex::new(TransactionManager::new()),
            metrics: DatabaseMetrics::default(),
        }
    }

    pub fn close(self) -> io::Result<()> {
        self.storage_engine.close()
    }

    pub fn print_page<W: io::Write>(self, buf: W, page_id: Option<PageId>) -> Result<(), Error> {
        let context = self.storage_engine.read_context();
        // TODO: Must use `expect()` because `storage::engine::Error` and `database::Error` are not
        // compatible. There's probably no reason to use two different error enums here, so maybe
        // we should unify them. Or maybe we could just rely on `std::io::Error`.
        self.storage_engine.print_page(&context, buf, page_id).expect("write failed");
        Ok(())
    }

    pub fn root_page_info<W: io::Write>(
        self,
        mut buf: W,
        file_path: impl AsRef<Path>,
    ) -> Result<(), OpenError> {
        let db_file_path = file_path.as_ref();

        let mut meta_file_path = db_file_path.to_path_buf();
        meta_file_path.as_mut_os_string().push(".meta");
        let mut meta_manager =
            MetadataManager::open(meta_file_path).map_err(OpenError::MetadataError)?;

        let page_count = meta_manager.active_slot().page_count();
        let active_slot = meta_manager.active_slot();
        let root_node_page_id = active_slot.root_node_page_id();
        let orphaned_page_list = meta_manager.orphan_pages().iter().collect::<Vec<_>>();

        writeln!(buf, "Root Node Page ID: {:?}", root_node_page_id).expect("write failed");

        //root subtrie pageID
        writeln!(buf, "Total Page Count: {:?}", page_count).expect("write failed");

        //orphaned pages list (grouped by page)
        writeln!(buf, "Orphaned Pages: {:?}", orphaned_page_list).expect("write failed");

        Ok(())
    }

    pub fn print_statistics<W: io::Write>(self, buf: W) -> Result<(), Error> {
        let context = self.storage_engine.read_context();
        self.storage_engine.debug_statistics(&context, buf).expect("write failed");
        Ok(())
    }

    pub fn consistency_check<W: io::Write>(
        self,
        mut buf: W,
        file_path: impl AsRef<Path>,
    ) -> Result<(), OpenError> {
        let db_file_path = file_path.as_ref();

        let mut meta_file_path = db_file_path.to_path_buf();
        meta_file_path.as_mut_os_string().push(".meta");
        let mut meta_manager =
            MetadataManager::open(meta_file_path).map_err(OpenError::MetadataError)?;

        let context = self.storage_engine.read_context();
        let active_slot_page_id = meta_manager.active_slot().root_node_page_id();
        let dirty_slot_page_id = meta_manager.dirty_slot().root_node_page_id();

        let mut reachable_pages =
            self.storage_engine.consistency_check(active_slot_page_id, &context).expect("write failed");
        let dirty_slot_pages =
            self.storage_engine.consistency_check(dirty_slot_page_id, &context).expect("write failed");
        reachable_pages.extend(&dirty_slot_pages);

        let orphaned_pages = meta_manager.orphan_pages().iter().map(|orphan| orphan.page_id()).collect::<HashSet<_>>();

        let reachachable_orphaned_pages: HashSet<PageId> =
            orphaned_pages.intersection(&reachable_pages).cloned().collect();

        writeln!(buf, "Reachable Orphaned Pages: {:?}", reachachable_orphaned_pages)
            .expect("write failed");
        let page_count = self.storage_engine.size();

        let all_pages: HashSet<PageId> = (1..page_count)
            .map(|id| PageId::new(id).unwrap()) // Unwrap Option from new()
            .collect();

        let mut reachable_or_orphaned: HashSet<PageId> = reachable_pages.into_iter().collect();
        reachable_or_orphaned.extend(&orphaned_pages);

        // Unreachable pages = all_pages - reachable_or_orphaned
        let unreachable_pages: HashSet<PageId> =
            all_pages.difference(&reachable_or_orphaned).cloned().collect();

        // Print unreachable pages
        writeln!(buf, "Unreachable Pages: {:?}", unreachable_pages).expect("write failed");

        Ok(())
    }

    pub fn begin_rw(&self) -> Result<Transaction<'_, RW>, TransactionError> {
        let context = self.storage_engine.write_context();
        let min_snapshot_id = self.transaction_manager.lock().begin_rw(context.snapshot_id)?;
        if min_snapshot_id > 0 {
            self.storage_engine.unlock(min_snapshot_id - 1);
        }
        Ok(Transaction::new(context, self))
    }

    pub fn begin_ro(&self) -> Result<Transaction<'_, RO>, TransactionError> {
        let context = self.storage_engine.read_context();
        self.transaction_manager.lock().begin_ro(context.snapshot_id);
        Ok(Transaction::new(context, self))
    }

    pub fn state_root(&self) -> B256 {
        self.storage_engine.read_context().root_node_hash
    }

    pub fn size(&self) -> u32 {
        self.storage_engine.size()
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{account::Account, path::AddressPath};
    use alloy_primitives::{address, Address, U256};
    use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
    use tempdir::TempDir;

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
        // create the database on disk. currently this will create a database with 0 pages
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let _db = Database::create(&file_path).unwrap();

        // WHEN: the database is opened
        let db = Database::open(&file_path).unwrap();

        // THEN: the size of the database should be 0
        assert_eq!(db.size(), 0);

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

    #[test]
    fn test_orphan_page_recycling_safety() {
        fn random_accounts(count: usize) -> impl Iterator<Item = (AddressPath, Option<Account>)> {
            (0..count).map(|_| {
                let address = Address::random();
                let account = Account::new(1, U256::from(100), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                (AddressPath::for_address(address), Some(account))
            })
        }

        fn alive_page_ids(db: &Database) -> Vec<PageId> {
            let orphan_pages = db
                .storage_engine
                .meta_manager
                .lock()
                .orphan_pages()
                .iter()
                .map(|orphan| orphan.page_id())
                .collect::<Vec<_>>();
            let all_pages = (1..db.storage_engine.page_manager.size())
                .map(|page_id| PageId::new(page_id).unwrap());
            all_pages.filter(move |page_id| !orphan_pages.contains(page_id)).collect()
        }

        // Create a new database and verify it has no pages
        let tmp_dir = TempDir::new("test_db").unwrap();
        let file_path = tmp_dir.path().join("test.db");
        let db = Database::create(file_path).unwrap();
        assert_eq!(db.storage_engine.page_manager.size(), 0);

        // Add 1000 accounts
        let mut tx = db.begin_rw().expect("rw transaction creation failed");
        let initial_accounts = random_accounts(1000).collect::<Vec<_>>();
        for (address, account) in &initial_accounts {
            tx.set_account(address.clone(), account.clone()).expect("adding account failed");
        }
        tx.commit().expect("commit failed");

        // Verify that the 1000 accounts got recorded in more than 1 page at snapshot 1
        let page_ids = alive_page_ids(&db);
        assert!(page_ids.len() > 1, "storage has no pages");
        for page_id in &page_ids {
            assert_eq!(
                db.storage_engine
                    .page_manager
                    .get(1, *page_id)
                    .unwrap_or_else(|err| panic!("page {page_id} not found: {err:?}"))
                    .snapshot_id(),
                1
            );
        }

        // Add 1000 more accounts
        let mut tx = db.begin_rw().expect("rw transaction creation failed");
        let more_accounts = random_accounts(1000).collect::<Vec<_>>();
        for (address, account) in &more_accounts {
            tx.set_account(address.clone(), account.clone()).expect("adding account failed");
        }
        tx.commit().expect("commit failed");

        // Verify that the new accounts caused even more pages to get added, this time at snapshot
        // 2
        let old_page_ids = page_ids;
        let new_page_ids = alive_page_ids(&db);
        assert!(
            new_page_ids.len() > old_page_ids.len(),
            "number of pages did not increase: {} -> {}",
            old_page_ids.len(),
            new_page_ids.len()
        );
        for page_id in &new_page_ids {
            let page = db
                .storage_engine
                .page_manager
                .get(1, *page_id)
                .unwrap_or_else(|err| panic!("page {page_id} not found: {err:?}"));
            if old_page_ids.contains(page_id) {
                assert_eq!(page.snapshot_id(), 1);
            } else {
                assert_eq!(page.snapshot_id(), 2);
            }
        }

        // Obtain a read transaction, and verify that it can access all the initial accounts
        let mut read_tx = db.begin_ro().expect("ro transaction creation failed");
        for (address, account) in &initial_accounts {
            assert_eq!(
                read_tx.get_account(address.clone()).expect("error while reading account"),
                account.clone()
            );
        }

        // Delete the initial accounts
        let mut tx = db.begin_rw().expect("rw transaction creation failed");
        for (address, _) in &initial_accounts {
            tx.set_account(address.clone(), None).expect("deleting account failed");
        }
        tx.commit().expect("commit failed");

        // Verify that the read transaction that we created before the delete can still access the
        // initial accounts
        read_tx.clear_cache();
        for (address, account) in &initial_accounts {
            assert_eq!(
                read_tx.get_account(address.clone()).expect("error while reading account"),
                account.clone()
            );
        }
    }
}
