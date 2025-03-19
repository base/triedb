use alloy_primitives::{Address, StorageKey, StorageValue, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::*;
use std::{cell::RefCell, collections::HashSet};
use tempdir::TempDir;
use triedb::{
    account::Account,
    path::{AddressPath, StoragePath},
    Database, MmapPageManager,
};

const SIZES: &[usize] = &[1_000_000, 3_000_000];
const BATCH_SIZE: usize = 10_000;

fn generate_random_address(rng: &mut StdRng) -> AddressPath {
    let addr = Address::random_with(rng);
    AddressPath::for_address(addr)
}

fn setup_database(size: usize) -> (TempDir, Database<MmapPageManager>) {
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

fn setup_database_with_storage(size: usize) -> (TempDir, Database<MmapPageManager>) {
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

fn bench_reads(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(42);
        let addresses: Vec<AddressPath> =
            (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("random_reads", size), &size, |b, _| {
            b.iter(|| {
                let tx = db.begin_ro().unwrap();
                for addr in &addresses {
                    let a = tx.get_account(addr.clone()).unwrap();
                    assert!(a.is_some());
                }
                tx.commit().unwrap();
            });
        });
    }
    group.finish();
}

fn bench_storage_reads_single_account(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_single_account_storage_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(42);
        let single_address = generate_random_address(&mut rng);
        let storage_paths: Vec<StoragePath> = (0..BATCH_SIZE)
            .map(|i| {
                let storage_key = StorageKey::from(U256::from(i));

                StoragePath::for_address_path_and_slot(single_address.clone(), storage_key)
            })
            .collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::new("random_single_account_storage_reads", size),
            &size,
            |b, _| {
                b.iter(|| {
                    let tx = db.begin_ro().unwrap();
                    for storage_path in &storage_paths {
                        let a = tx.get_storage_slot(storage_path.clone()).unwrap();
                        assert!(a.is_some());
                    }
                    tx.commit().unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_storage_reads_multiple_accounts(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_multiple_accounts_storage_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(42);
        let total_addresses = size / BATCH_SIZE;
        let addresses: Vec<AddressPath> =
            (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();

        let total_storage_per_address = BATCH_SIZE / total_addresses;
        let mut storage_paths: Vec<StoragePath> = Vec::new();
        for address in addresses {
            for i in 0..=total_storage_per_address {
                let storage_key = StorageKey::from(U256::from(i));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                storage_paths.push(storage_path);
            }
        }

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::new("random_mutiple_account_storage_reads", size),
            &size,
            |b, _| {
                b.iter(|| {
                    let tx = db.begin_ro().unwrap();
                    for storage_path in &storage_paths {
                        let a = tx.get_storage_slot(storage_path.clone()).unwrap();
                        assert!(a.is_some());
                    }
                    tx.commit().unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_inserts(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(43);
        let addresses: Vec<AddressPath> =
            (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("batch_inserts", size), &size, |b, _| {
            b.iter(|| {
                let mut tx = db.begin_rw().unwrap();
                for addr in &addresses {
                    let account =
                        Account::new(1, U256::from(1000u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                    tx.set_account(addr.clone(), Some(account)).unwrap();
                }
                tx.commit().unwrap();
            });
        });
    }
    group.finish();
}

fn bench_storage_inserts_single_account(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_single_account_storage_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(43);
        let single_address = generate_random_address(&mut rng);
        let storage_paths_values: Vec<(StoragePath, StorageValue)> = (0..BATCH_SIZE)
            .map(|i| {
                let storage_key = StorageKey::from(U256::from(i));
                let storage_path =
                    StoragePath::for_address_path_and_slot(single_address.clone(), storage_key);
                let storage_value =
                    StorageValue::from_be_slice(storage_path.get_slot().pack().as_slice());
                (storage_path, storage_value)
            })
            .collect();

        let account = Account::new(1, U256::from(1000u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        let mut tx = db.begin_rw().unwrap();
        tx.set_account(single_address.clone(), Some(account)).unwrap();
        tx.commit().unwrap();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::new("batch_inserts_single_account_storage", size),
            &size,
            |b, _| {
                b.iter(|| {
                    let mut tx = db.begin_rw().unwrap();
                    for (storage_path, storage_value) in &storage_paths_values {
                        tx.set_storage_slot(storage_path.clone(), Some(*storage_value)).unwrap();
                    }
                    tx.commit().unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_storage_inserts_multiple_accounts(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_mutliple_accounts_storage_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(43);
        let total_addresses = size / BATCH_SIZE;
        let addresses: Vec<AddressPath> =
            (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();

        let total_storage_per_address = BATCH_SIZE / total_addresses;
        let mut storage_paths_values: Vec<(StoragePath, StorageValue)> = Vec::new();
        for address in &addresses {
            for i in 0..=total_storage_per_address {
                let storage_key = StorageKey::from(U256::from(i));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                let storage_value =
                    StorageValue::from_be_slice(storage_path.get_slot().pack().as_slice());
                storage_paths_values.push((storage_path, storage_value));
            }
        }

        let mut tx = db.begin_rw().unwrap();
        let account = Account::new(1, U256::from(1000u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
        for addr in &addresses {
            tx.set_account(addr.clone(), Some(account.clone())).unwrap();
        }
        tx.commit().unwrap();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::new("batch_inserts_multiple_account_storage", size),
            &size,
            |b, _| {
                b.iter(|| {
                    let mut tx = db.begin_rw().unwrap();
                    for (storage_path, storage_value) in &storage_paths_values {
                        tx.set_storage_slot(storage_path.clone(), Some(*storage_value)).unwrap();
                    }
                    tx.commit().unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_updates(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(42);
        let addresses: Vec<AddressPath> =
            (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("batch_updates", size), &size, |b, _| {
            b.iter(|| {
                let mut tx = db.begin_rw().unwrap();
                for addr in &addresses {
                    let new_account = Account::new(
                        999_999_999,
                        U256::from(999_999_999u64),
                        EMPTY_ROOT_HASH,
                        KECCAK_EMPTY,
                    );
                    tx.set_account(addr.clone(), Some(new_account)).unwrap();
                }
                tx.commit().unwrap();
            });
        });
    }
    group.finish();
}

fn bench_storage_single_account_updates(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_single_account_storage_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(42);
        let single_address = generate_random_address(&mut rng);
        let storage_paths_values: Vec<(StoragePath, StorageValue)> = (0..BATCH_SIZE)
            .map(|i| {
                let storage_key = StorageKey::from(U256::from(i));
                let storage_path =
                    StoragePath::for_address_path_and_slot(single_address.clone(), storage_key);
                let mut new_value = storage_path.get_slot().pack();
                new_value.reverse();
                let storage_value = StorageValue::from_be_slice(new_value.as_slice());
                (storage_path, storage_value)
            })
            .collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::new("batch_single_account_storage_updates", size),
            &size,
            |b, _| {
                b.iter(|| {
                    let mut tx = db.begin_rw().unwrap();
                    for (storage_path, storage_value) in &storage_paths_values {
                        tx.set_storage_slot(storage_path.clone(), Some(*storage_value)).unwrap();
                    }
                    tx.commit().unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_storage_multiple_account_updates(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_multiple_accounts_storage_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(42);
        let total_addresses = size / BATCH_SIZE;
        let addresses: Vec<AddressPath> =
            (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();

        let total_storage_per_address = BATCH_SIZE / total_addresses;
        let mut storage_paths_values: Vec<(StoragePath, StorageValue)> = Vec::new();
        for address in &addresses {
            for i in 0..=total_storage_per_address {
                let storage_key = StorageKey::from(U256::from(i));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                let mut new_value = storage_path.get_slot().pack();
                new_value.reverse();
                let storage_value = StorageValue::from_be_slice(new_value.as_slice());
                storage_paths_values.push((storage_path, storage_value));
            }
        }

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::new("batch_multiple_accounts_storage_updates", size),
            &size,
            |b, _| {
                b.iter(|| {
                    let mut tx = db.begin_rw().unwrap();
                    for (storage_path, storage_value) in &storage_paths_values {
                        tx.set_storage_slot(storage_path.clone(), Some(*storage_value)).unwrap();
                    }
                    tx.commit().unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_deletes(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(42);
        let addresses: Vec<AddressPath> =
            (0..size).map(|_| generate_random_address(&mut rng)).collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("batch_deletes", size), &size, |b, _| {
            b.iter(|| {
                let mut tx = db.begin_rw().unwrap();
                for addr in &addresses[0..BATCH_SIZE] {
                    tx.set_account(addr.clone(), None).unwrap();
                }
                // because we are deleting data, after each iteration we drop all the changes
                // we make so that we can delete all the values again.
                tx.rollback().unwrap();
            });
        });
    }
    group.finish();
}

fn bench_storage_single_account_deletes(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_single_account_storage_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(42);
        let single_address = generate_random_address(&mut rng);
        let storage_paths: Vec<StoragePath> = (0..BATCH_SIZE)
            .map(|i| {
                let storage_key = StorageKey::from(U256::from(i));

                StoragePath::for_address_path_and_slot(single_address.clone(), storage_key)
            })
            .collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::new("batch_single_account_storage_deletes", size),
            &size,
            |b, _| {
                b.iter(|| {
                    let mut tx = db.begin_rw().unwrap();
                    for storage_path in &storage_paths {
                        tx.set_storage_slot(storage_path.clone(), None).unwrap();
                    }
                    // because we are deleting data, after each iteration we drop all the changes
                    // we make so that we can delete all the values again.
                    tx.rollback().unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_storage_mutliple_accounts_deletes(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_multiple_accounts_storage_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(42);
        let total_addresses = size / BATCH_SIZE;
        let addresses: Vec<AddressPath> =
            (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();

        let total_storage_per_address = BATCH_SIZE / total_addresses;
        let mut storage_paths: Vec<StoragePath> = Vec::new();
        for address in &addresses {
            for i in 0..=total_storage_per_address {
                let storage_key = StorageKey::from(U256::from(i));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                storage_paths.push(storage_path);
            }
        }

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::new("batch_single_account_storage_deletes", size),
            &size,
            |b, _| {
                b.iter(|| {
                    let mut tx = db.begin_rw().unwrap();
                    for storage_path in &storage_paths {
                        tx.set_storage_slot(storage_path.clone(), None).unwrap();
                    }
                    // because we are deleting data, after each iteration we drop all the changes
                    // we make so that we can delete all the values again.
                    tx.rollback().unwrap();
                });
            },
        );
    }
    group.finish();
}

fn bench_mixed_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("mixed_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(42);
        let existing_addresses: Vec<AddressPath> =
            (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();
        let new_addresses: Vec<AddressPath> =
            (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();
        let existing_accounts_with_storage: Vec<AddressPath> =
            (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

        let mut existing_storage_slots: Vec<(StoragePath, StorageValue)> = Vec::new();
        for address in &existing_accounts_with_storage {
            for i in 0..=10 {
                let storage_key = StorageKey::from(U256::from(i));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                let mut new_value = storage_path.get_slot().pack();
                new_value.reverse();
                let storage_value = StorageValue::from_be_slice(new_value.as_slice());
                existing_storage_slots.push((storage_path, storage_value));
            }
        }

        // add these storage slots
        let mut tx = db.begin_rw().unwrap();
        for (storage_path, storage_value) in &existing_storage_slots {
            tx.set_storage_slot(storage_path.clone(), Some(*storage_value)).unwrap();
        }
        tx.commit().unwrap();

        // these storage slots will be used to insert new values into storage
        let mut new_storage_slots_in_existing_accounts_with_storage: Vec<(
            StoragePath,
            StorageValue,
        )> = Vec::new();
        for address in &existing_accounts_with_storage {
            for i in 0..=10 {
                let storage_key = StorageKey::from(U256::from(i + BATCH_SIZE + 1));
                let storage_path =
                    StoragePath::for_address_path_and_slot(address.clone(), storage_key);
                let mut new_value = storage_path.get_slot().pack();
                new_value.reverse();
                let storage_value = StorageValue::from_be_slice(new_value.as_slice());
                new_storage_slots_in_existing_accounts_with_storage
                    .push((storage_path, storage_value));
            }
        }

        let deleted_accounts: RefCell<HashSet<AddressPath>> = RefCell::new(HashSet::new());
        let deleted_storage: RefCell<HashSet<StoragePath>> = RefCell::new(HashSet::new());

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("mixed_workload", size), &size, |b, _| {
            b.iter_with_setup(
                || {
                    // repopulate deleted values
                    let mut tx = db.begin_rw().unwrap();
                    for deleted_account_address in deleted_accounts.borrow().clone().into_iter() {
                        let account =
                            Account::new(1, U256::from(1000u64), EMPTY_ROOT_HASH, KECCAK_EMPTY);
                        tx.set_account(deleted_account_address.clone(), Some(account)).unwrap();
                    }

                    for deleted_storage_path in deleted_storage.borrow().clone().into_iter() {
                        let mut new_value = deleted_storage_path.get_slot().pack();
                        new_value.reverse();
                        let storage_value = StorageValue::from_be_slice(new_value.as_slice());
                        tx.set_storage_slot(deleted_storage_path.clone(), Some(storage_value))
                            .unwrap();
                    }

                    tx.commit().unwrap();

                    deleted_accounts.borrow_mut().clear();
                    deleted_storage.borrow_mut().clear();
                },
                |_| {
                    let mut tx = db.begin_rw().unwrap();
                    for i in 0..BATCH_SIZE {
                        let op = rng.gen_range(0..=7);
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
                                let account = Account::new(
                                    1,
                                    U256::from(1000u64),
                                    EMPTY_ROOT_HASH,
                                    KECCAK_EMPTY,
                                );
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
                                deleted_accounts.borrow_mut().insert(address);
                            }
                            4 => {
                                // Read storage
                                let (storage_path, _) = existing_storage_slots[i].clone();
                                let storage_value =
                                    tx.get_storage_slot(storage_path.clone()).unwrap();
                                assert!(storage_value.is_some());
                            }
                            5 => {
                                // Insert storage
                                let (storage_path, storage_value) =
                                    new_storage_slots_in_existing_accounts_with_storage[i].clone();

                                tx.set_storage_slot(storage_path, Some(storage_value)).unwrap();
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
                                deleted_storage.borrow_mut().insert(storage_path);
                            }
                            _ => unreachable!(),
                        }
                    }
                    tx.commit().unwrap();
                },
            );
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    bench_reads,
    bench_inserts,
    bench_updates,
    bench_deletes,
    bench_mixed_operations,
    bench_storage_reads_single_account,
    bench_storage_reads_multiple_accounts,
    bench_storage_inserts_single_account,
    bench_storage_inserts_multiple_accounts,
    bench_storage_single_account_updates,
    bench_storage_multiple_account_updates,
    bench_storage_single_account_deletes,
    bench_storage_mutliple_accounts_deletes
);
criterion_main!(benches);
