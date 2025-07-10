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

mod benchmark_common;

use alloy_primitives::{StorageKey, StorageValue, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::*;
use std::{fs, io, path::Path, time::Duration};
use tempdir::TempDir;
use triedb::{
    account::Account,
    path::{AddressPath, StoragePath},
    config::Config,
    Database,
};

use benchmark_common::{
    generate_random_address, generate_storage_paths_values, get_base_database, BaseDatabase,
    BATCH_SIZE, DEFAULT_SETUP_DB_CONTRACT_SIZE, DEFAULT_SETUP_DB_EOA_SIZE,
    DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT, SEED_CONTRACT, SEED_EOA,
};

const SEED_NEW_EOA: u64 = 44; // new EOA seeding value
const SEED_NEW_CONTRACT: u64 = 45; // new contract account seeding value

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
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("eoa_reads", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let db_path = dir.path().join(&file_name);
                Database::open(db_path.clone(), &Config::default()).unwrap()
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
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("eoa_inserts", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_insert").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                addresses.iter().enumerate().for_each(|(i, addr)| {
                    let account =
                        Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                    tx.set_account(addr.clone(), Some(account)).unwrap();
                });
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_account_inserts_loop(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_loop_operations");
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
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("eoa_inserts_loop", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_insert_loop").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                for i in 0..10 {
                    let mut tx = db.begin_rw().unwrap();
                    for j in 0..BATCH_SIZE / 10 {
                        let account = Account::new(
                            j as u64,
                            U256::from(j as u64),
                            EMPTY_ROOT_HASH,
                            KECCAK_EMPTY,
                        );
                        tx.set_account(addresses[j + i * BATCH_SIZE / 10].clone(), Some(account))
                            .unwrap();
                    }
                    tx.commit().unwrap();
                }
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
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("eoa_updates", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let db_path = dir.path().join(&file_name);
                Database::open(db_path.clone(), &Config::default()).unwrap()
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
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("eoa_deletes", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_delete").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path, &Config::default()).unwrap()
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

    let mut existing_storage_slots: Vec<(StoragePath, StorageValue)> = Vec::with_capacity(
        existing_accounts_with_storage.len() * DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );
    for address in &existing_accounts_with_storage {
        for i in 1..=DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT {
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
        for i in 1..=DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT {
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
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("mixed_operations", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_mixed").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                for i in 0..BATCH_SIZE {
                    let op = eoa_rng.random_range(0..=7);
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

fn bench_storage_reads(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_storage_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );

    let dir = TempDir::new("triedb_bench_storage_read").unwrap();
    let file_name = base_dir.main_file_name.clone();
    copy_files(&base_dir, dir.path()).unwrap();

    let mut rng = StdRng::seed_from_u64(SEED_CONTRACT);
    let total_storage_per_address = DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT / 2;
    let total_addresses = BATCH_SIZE / total_storage_per_address;
    let addresses: Vec<AddressPath> =
        (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();
    let storage_paths_values = generate_storage_paths_values(&addresses, total_storage_per_address);

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("storage_reads", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let db_path = dir.path().join(&file_name);
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                let mut tx = db.begin_ro().unwrap();
                storage_paths_values.iter().for_each(|(storage_path, _)| {
                    let a = tx.get_storage_slot(storage_path.clone()).unwrap();
                    assert!(a.is_some());
                });
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_storage_inserts(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_storage_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );
    let file_name = base_dir.main_file_name.clone();

    let mut rng = StdRng::seed_from_u64(SEED_NEW_CONTRACT);
    let total_storage_per_address = DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT;
    let total_addresses = BATCH_SIZE / total_storage_per_address;
    let addresses: Vec<AddressPath> =
        (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();
    let storage_paths_values = generate_storage_paths_values(&addresses, total_storage_per_address);

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("storage_inserts", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_storage_insert").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                addresses.iter().enumerate().for_each(|(i, address)| {
                    let account =
                        Account::new(i as u64, U256::from(i as u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                    tx.set_account(address.clone(), Some(account)).unwrap();
                });
                storage_paths_values.iter().for_each(|(storage_path, storage_value)| {
                    tx.set_storage_slot(storage_path.clone(), Some(*storage_value)).unwrap();
                });
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_storage_updates(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_storage_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );
    let file_name = base_dir.main_file_name.clone();

    let mut rng = StdRng::seed_from_u64(SEED_CONTRACT);
    let total_storage_per_address = DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT;
    let total_addresses = BATCH_SIZE / total_storage_per_address;
    let addresses: Vec<AddressPath> =
        (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();
    let storage_paths_values = generate_storage_paths_values(&addresses, total_storage_per_address);

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("storage_updates", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_storage_update").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                storage_paths_values.iter().for_each(|(storage_path, storage_value)| {
                    tx.set_storage_slot(storage_path.clone(), Some(*storage_value)).unwrap();
                });
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_storage_deletes(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_storage_operations");
    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );
    let file_name = base_dir.main_file_name.clone();

    let mut rng = StdRng::seed_from_u64(SEED_CONTRACT);
    let total_storage_per_address = DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT;
    let total_addresses = BATCH_SIZE / total_storage_per_address;
    let addresses: Vec<AddressPath> =
        (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();
    let storage_paths_values = generate_storage_paths_values(&addresses, total_storage_per_address);

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("storage_deletes", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let dir = TempDir::new("triedb_bench_storage_delete").unwrap();
                copy_files(&base_dir, dir.path()).unwrap();
                let db_path = dir.path().join(&file_name);
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                let mut tx = db.begin_rw().unwrap();
                storage_paths_values.iter().for_each(|(storage_path, _)| {
                    tx.set_storage_slot(storage_path.clone(), None).unwrap();
                });
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
    bench_account_inserts_loop,
    bench_account_updates,
    bench_account_deletes,
    bench_mixed_operations,
    bench_storage_reads,
    bench_storage_inserts,
    bench_storage_updates,
    bench_storage_deletes,
);
criterion_main!(benches);
