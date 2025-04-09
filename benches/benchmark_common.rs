use alloy_primitives::{Address, StorageKey, StorageValue, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use rand::prelude::*;
use tempdir::TempDir;
use triedb::{
    account::Account,
    path::{AddressPath, StoragePath},
    Database,
};

pub const BATCH_SIZE: usize = 10_000;

pub fn generate_random_address(rng: &mut StdRng) -> AddressPath {
    let addr = Address::random_with(rng);
    AddressPath::for_address(addr)
}

pub fn setup_database(size: usize) -> (TempDir, Database) {
    let dir = TempDir::new("triedb_bench").unwrap();
    let db_path = dir.path().join("db");
    let db = Database::create(db_path.to_str().unwrap()).unwrap();

    // Populate database with initial accounts
    let mut rng = StdRng::seed_from_u64(42);
    {
        let mut tx = db.begin_rw().unwrap();
        for i in 1..=size {
            let address = generate_random_address(&mut rng);
            let account =
                Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);

            tx.set_account(address, Some(account)).unwrap();
        }

        tx.commit().unwrap();
    }

    (dir, db)
}

pub fn setup_database_with_storage(size: usize) -> (TempDir, Database) {
    let dir = TempDir::new("triedb_bench_storage").unwrap();
    let db_path = dir.path().join("db");
    let db = Database::create(db_path.to_str().unwrap()).unwrap();

    // Populate database with initial accounts
    let mut rng = StdRng::seed_from_u64(42);
    {
        let mut tx = db.begin_rw().unwrap();
        let num_accounts_to_generate = size / BATCH_SIZE;
        for i in 1..=num_accounts_to_generate {
            let address = generate_random_address(&mut rng);
            let account =
                Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);

            tx.set_account(address.clone(), Some(account)).unwrap();

            // add random storage to each account
            for i in 0..=BATCH_SIZE {
                let storage_key = StorageKey::from(U256::from(i));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                let storage_value =
                    StorageValue::from_be_slice(storage_path.get_slot().pack().as_slice());

                tx.set_storage_slot(storage_path, Some(storage_value)).unwrap();
            }
        }

        tx.commit().unwrap();
    }
    (dir, db)
}

pub fn generate_storage_paths(
    addresses: &[AddressPath],
    storage_per_address: usize,
) -> Vec<StoragePath> {
    let capacity = addresses.len() * (storage_per_address + 1);
    let mut storage_paths: Vec<StoragePath> = Vec::with_capacity(capacity);
    addresses
        .iter()
        .flat_map(|address| {
            (0..=storage_per_address).map(|i| {
                StoragePath::for_address_path_and_slot(
                    address.clone(),
                    StorageKey::from(U256::from(i)),
                )
            })
        })
        .for_each(|path| storage_paths.push(path));
    storage_paths
}
