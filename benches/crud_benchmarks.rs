//! Option 1: Run with a provided database folder and file name:
//!
//! ```bash
//! BASE_DIR=/path/to/db/folder FILE_NAME=db_file cargo bench --bench crud_benchmarks
//! ```
//!
//! Option 2: Seed a new database for each benchmark with default size of 1M externally owned
//! accounts (EOA) and 100K contract accounts with 10 storage slots per contract:
//!
//! ```bash
//! cargo bench --bench crud_benchmarks
//! ```
//!
//! The database will be created in a temporary directory and deleted after the benchmarks are
//! finished.

use alloy_primitives::{Address, StorageKey, StorageValue, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::*;
use std::{
    fs, io,
    path::{Path, PathBuf},
};
use tempdir::TempDir;
use triedb::{
    account::Account,
    path::{AddressPath, StoragePath},
    transaction::TransactionError,
    Database,
};

#[derive(Debug)]
struct BaseDatabase {
    _base_dir: Option<TempDir>,
    main_file_name: String,
    file_name_path: PathBuf,
    meta_file_name: String,
    meta_file_name_path: PathBuf,
}

const DEFAULT_SETUP_DB_EOA_SIZE: usize = 1_000_000;
const DEFAULT_SETUP_DB_CONTRACT_SIZE: usize = 100_000;
const DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT: usize = 10;
const SEED_EOA: u64 = 42; // EOA seeding value
const SEED_CONTRACT: u64 = 43; // contract account seeding value
const SEED_NEW_EOA: u64 = 44; // new EOA seeding value
const BATCH_SIZE: usize = 10_000;

fn generate_random_address(rng: &mut StdRng) -> AddressPath {
    let addr = Address::random_with(rng);
    AddressPath::for_address(addr)
}

fn get_base_database(
    fallback_eoa_size: usize,
    fallback_contract_size: usize,
    fallback_storage_per_contract: usize,
) -> BaseDatabase {
    let base_dir = std::env::var("BASE_DIR").ok();
    if let Some(base_dir) = base_dir {
        let file_name =
            std::env::var("FILE_NAME").expect("FILE_NAME must be set when using BASE_DIR");
        let main_file_name = file_name.to_string();
        let meta_file_name = format!("{}.meta", file_name);
        let file_name_path = Path::new(&base_dir).join(&main_file_name);
        let meta_file_name_path = Path::new(&base_dir).join(&meta_file_name);

        return BaseDatabase {
            _base_dir: None,
            main_file_name,
            meta_file_name,
            file_name_path,
            meta_file_name_path,
        };
    }
    let dir = TempDir::new("triedb_bench_base").unwrap();

    let main_file_name_path = dir.path().join("triedb");
    let meta_file_name_path = dir.path().join("triedb.meta");
    let db = Database::create(main_file_name_path.to_str().unwrap()).unwrap();

    setup_database(&db, fallback_eoa_size, fallback_contract_size, fallback_storage_per_contract)
        .unwrap();

    BaseDatabase {
        _base_dir: Some(dir),
        main_file_name: "triedb".to_string(),
        file_name_path: main_file_name_path,
        meta_file_name: "triedb.meta".to_string(),
        meta_file_name_path,
    }
}

fn setup_database(
    db: &Database,
    eoa_count: usize,
    contract_count: usize,
    storage_per_contract: usize,
) -> Result<(), TransactionError> {
    // Populate database with initial accounts
    let mut eoa_rng = StdRng::seed_from_u64(SEED_EOA);
    let mut contract_rng = StdRng::seed_from_u64(SEED_CONTRACT);
    {
        let mut tx = db.begin_rw()?;
        for i in 1..=eoa_count {
            let address = generate_random_address(&mut eoa_rng);
            let account =
                Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);

            tx.set_account(address, Some(account))?;
        }

        for i in 1..=contract_count {
            let address = generate_random_address(&mut contract_rng);
            let account =
                Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);

            tx.set_account(address.clone(), Some(account))?;

            // add random storage to each account
            for key in 1..=storage_per_contract {
                let storage_key = StorageKey::from(U256::from(key));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                let storage_value =
                    StorageValue::from_be_slice(storage_path.get_slot().pack().as_slice());

                tx.set_storage_slot(storage_path, Some(storage_value))?;
            }
        }

        tx.commit()?;
    }

    Ok(())
}

fn copy_files(from: &BaseDatabase, to: &Path) -> Result<(), io::Error> {
    for (file, from_path) in [
        (&from.main_file_name, &from.file_name_path),
        (&from.meta_file_name, &from.meta_file_name_path),
    ] {
        let to_path = to.join(file);
        fs::copy(from_path, &to_path)?;
    }
    Ok(())
}

fn bench_account_reads(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );

    let dir = TempDir::new("triedb_bench_read").unwrap();
    let file_name = base_dir.main_file_name.clone();
    copy_files(&base_dir, dir.path()).unwrap();

    let mut rng = StdRng::seed_from_u64(SEED_EOA);
    let addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.bench_function(BenchmarkId::new("eoa_reads", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let db_path = dir.path().join(&file_name);
                Database::open(db_path.clone()).unwrap()
            },
            |db| {
                let mut tx = db.begin_ro().unwrap();
                for addr in &addresses {
                    let a = tx.get_account(addr.clone()).unwrap();
                    assert!(a.is_some());
                }
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_account_inserts(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );
    let file_name = base_dir.main_file_name.clone();

    let mut rng = StdRng::seed_from_u64(SEED_NEW_EOA);
    let addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.bench_function(BenchmarkId::new("eoa_inserts", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_insert").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                for addr in &addresses {
                    let account =
                        Account::new(1, U256::from(1000u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                    tx.set_account(addr.clone(), Some(account)).unwrap();
                }
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_account_updates(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );

    let dir = TempDir::new("triedb_bench_update").unwrap();
    let file_name = base_dir.main_file_name.clone();
    copy_files(&base_dir, dir.path()).unwrap();

    let mut rng = StdRng::seed_from_u64(SEED_EOA);
    let addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.bench_function(BenchmarkId::new("eoa_updates", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let db_path = dir.path().join(&file_name);
                Database::open(db_path.clone()).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                addresses.iter().enumerate().for_each(|(i, addr)| {
                    let new_account =
                        Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                    tx.set_account(addr.clone(), Some(new_account)).unwrap();
                });
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_account_deletes(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );

    let file_name = base_dir.main_file_name.clone();

    let mut rng = StdRng::seed_from_u64(SEED_EOA);
    let addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.bench_function(BenchmarkId::new("eoa_deletes", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_delete").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                addresses.iter().for_each(|addr| {
                    tx.set_account(addr.clone(), None).unwrap();
                });
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_mixed_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("mixed_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );
    let file_name = base_dir.main_file_name.clone();

    let mut eoa_rng = StdRng::seed_from_u64(SEED_EOA);
    let mut new_eoa_rng = StdRng::seed_from_u64(SEED_NEW_EOA);
    let mut contract_rng = StdRng::seed_from_u64(SEED_CONTRACT);

    let existing_addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut eoa_rng)).collect();
    let new_addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut new_eoa_rng)).collect();
    let existing_accounts_with_storage: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut contract_rng)).collect();

    let mut existing_storage_slots: Vec<(StoragePath, StorageValue)> =
        Vec::with_capacity(existing_accounts_with_storage.len() * 10);
    for address in &existing_accounts_with_storage {
        for i in 0..=10 {
            let storage_key = StorageKey::from(U256::from(i));
            let storage_path = StoragePath::for_address_path_and_slot(address.clone(), storage_key);
            let mut new_value = storage_path.get_slot().pack();
            new_value.reverse();
            let storage_value = StorageValue::from_be_slice(new_value.as_slice());
            existing_storage_slots.push((storage_path, storage_value));
        }
    }

    let mut new_storage_slots_in_existing_accounts_with_storage: Vec<(StoragePath, StorageValue)> =
        Vec::with_capacity(existing_accounts_with_storage.len() * 10);
    for address in &existing_accounts_with_storage {
        for i in 0..=10 {
            let storage_key =
                StorageKey::from(U256::from(i + DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT + 1));
            let storage_path = StoragePath::for_address_path_and_slot(address.clone(), storage_key);
            let mut new_value = storage_path.get_slot().pack();
            new_value.reverse();
            let storage_value = StorageValue::from_be_slice(new_value.as_slice());
            new_storage_slots_in_existing_accounts_with_storage.push((storage_path, storage_value));
        }
    }

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.bench_function(BenchmarkId::new("mixed_workload", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_mixed").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                for i in 0..BATCH_SIZE {
                    let op = eoa_rng.gen_range(0..=7);
                    match op {
                        0 => {
                            // Read
                            let address = existing_addresses[i].clone();
                            let account = tx.get_account(address.clone()).unwrap();
                            assert!(account.is_some());
                        }
                        1 => {
                            // Insert
                            let address = new_addresses[i].clone();
                            let account =
                                Account::new(1, U256::from(1000u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                            tx.set_account(address.clone(), Some(account)).unwrap();
                        }
                        2 => {
                            // Update
                            let address = existing_addresses[i].clone();
                            let new_account = Account::new(
                                123,
                                U256::from(999_999_999u64),
                                EMPTY_ROOT_HASH,
                                KECCAK_EMPTY,
                            );
                            tx.set_account(address.clone(), Some(new_account)).unwrap();
                        }
                        3 => {
                            // Delete
                            let address = existing_addresses[i].clone();
                            tx.set_account(address.clone(), None).unwrap();
                        }
                        4 => {
                            // Read storage
                            let (storage_path, _) = existing_storage_slots[i].clone();
                            let storage_value = tx.get_storage_slot(storage_path.clone()).unwrap();
                            assert!(storage_value.is_some());
                        }
                        5 => {
                            // Insert storage
                            let (storage_path, storage_value) =
                                new_storage_slots_in_existing_accounts_with_storage[i].clone();

                            tx.set_storage_slot(storage_path.clone(), Some(storage_value)).unwrap();
                        }
                        6 => {
                            // Update storage
                            let (storage_path, _) = existing_storage_slots[i].clone();
                            tx.set_storage_slot(
                                storage_path,
                                Some(StorageValue::from(U256::from(i))),
                            )
                            .unwrap();
                        }
                        7 => {
                            // Delete storage
                            let (storage_path, _) = existing_storage_slots[i].clone();
                            tx.set_storage_slot(storage_path.clone(), None).unwrap();
                        }
                        _ => unreachable!(),
                    }
                }
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_account_reads,
    bench_account_inserts,
    bench_account_updates,
    bench_account_deletes,
    bench_mixed_operations
);
criterion_main!(benches);
