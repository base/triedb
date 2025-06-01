mod benchmark_common;
use alloy_primitives::{StorageKey, StorageValue, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use benchmark_common::{
    generate_random_address, generate_storage_paths, setup_database_with_storage, BATCH_SIZE,
};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::*;
use std::{cell::RefCell, collections::HashSet, fs, io, path::Path};
use tempdir::TempDir;
use triedb::{
    account::Account,
    path::{AddressPath, StoragePath},
    transaction::Transaction,
    Database,
};

const SIZES: &[usize] = &[1_000_000];

pub fn setup_database(sizes: &[usize]) -> TempDir {
    let dir = TempDir::new("triedb_bench_based").unwrap();

    for &size in sizes {
        let db_path = dir.path().join(format!("db_{}", size));
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
    }

    dir
}

fn copy_files(from: &Path, to: &Path) -> Result<(), io::Error> {
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let from_path = entry.path();
        let to_path = to.join(entry.file_name());

        if from_path.is_file() {
            fs::copy(&from_path, &to_path)?;
        }
    }

    Ok(())
}

fn bench_reads(c: &mut Criterion) {
    let mut group = c.benchmark_group("read_operations");

    let based_dir = setup_database(SIZES);
    let dir = TempDir::new("triedb_bench").unwrap();
    copy_files(based_dir.path(), dir.path()).unwrap();

    let mut rng = StdRng::seed_from_u64(42);
    let addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

    for &size in SIZES {
        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("random_reads", size), &size, |b, _| {
            b.iter_with_setup(
                || {
                    let db_path = dir.path().join(format!("db_{}", size));
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
    }

    group.finish();
}

fn bench_inserts(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_operations");
    let based_dir = setup_database(SIZES);

    let mut rng = StdRng::seed_from_u64(43);
    let addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

    for &size in SIZES {
        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("batch_inserts", size), &size, |b, _| {
            b.iter_with_setup(
                || {
                    let dir = TempDir::new("triedb_bench").unwrap();
                    copy_files(based_dir.path(), dir.path()).unwrap();
                    let db_path = dir.path().join(format!("db_{}", size));
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
    }

    group.finish();
}

criterion_group!(benches, bench_reads, bench_inserts);
criterion_main!(benches);
