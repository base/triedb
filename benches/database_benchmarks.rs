use alloy_primitives::{Address, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::*;
use tempdir::TempDir;
use triedb::{account::RlpAccount, path::AddressPath, Database, MmapPageManager};

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
            let account = RlpAccount::new(
                i as u64,
                U256::from(i as u64),
                EMPTY_ROOT_HASH,
                KECCAK_EMPTY,
            );

            tx.set_account(address, Some(account)).unwrap();
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
        let addresses: Vec<AddressPath> = (0..BATCH_SIZE)
            .map(|_| generate_random_address(&mut rng))
            .collect();

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

fn bench_inserts(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(43);
        let addresses: Vec<AddressPath> = (0..BATCH_SIZE)
            .map(|_| generate_random_address(&mut rng))
            .collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("batch_inserts", size), &size, |b, _| {
            b.iter(|| {
                let mut tx = db.begin_rw().unwrap();
                for addr in &addresses {
                    let account =
                        RlpAccount::new(1, U256::from(1000u64), KECCAK_EMPTY, EMPTY_ROOT_HASH);
                    tx.set_account(addr.clone(), Some(account)).unwrap();
                }
                tx.commit().unwrap();
            });
        });
    }
    group.finish();
}

fn bench_updates(c: &mut Criterion) {
    let mut group = c.benchmark_group("update_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(42);
        let addresses: Vec<AddressPath> = (0..BATCH_SIZE)
            .map(|_| generate_random_address(&mut rng))
            .collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("batch_updates", size), &size, |b, _| {
            b.iter(|| {
                let mut tx = db.begin_rw().unwrap();
                for addr in &addresses {
                    let new_account = RlpAccount::new(
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

fn bench_deletes(c: &mut Criterion) {
    let mut group = c.benchmark_group("delete_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(42);
        let addresses: Vec<AddressPath> = (0..BATCH_SIZE)
            .map(|_| generate_random_address(&mut rng))
            .collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("batch_deletes", size), &size, |b, _| {
            b.iter(|| {
                let mut tx = db.begin_rw().unwrap();
                for addr in &addresses {
                    tx.set_account(addr.clone(), None::<RlpAccount>).unwrap();
                }
                tx.commit().unwrap();
            });
        });
    }
    group.finish();
}

fn bench_mixed_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("mixed_operations");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(42);
        let existing_addresses: Vec<AddressPath> = (0..BATCH_SIZE)
            .map(|_| generate_random_address(&mut rng))
            .collect();
        let new_addresses: Vec<AddressPath> = (0..BATCH_SIZE)
            .map(|_| generate_random_address(&mut rng))
            .collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("mixed_workload", size), &size, |b, _| {
            b.iter(|| {
                let mut tx = db.begin_rw().unwrap();
                for i in 0..BATCH_SIZE {
                    let op = rng.gen_range(0..3);

                    match op {
                        0 => {
                            // Read
                            let address = existing_addresses[i].clone();
                            let account = tx.get_account(address).unwrap();
                            assert!(account.is_some());
                        }
                        1 => {
                            // Insert
                            let address = new_addresses[i].clone();
                            let account = RlpAccount::new(
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
                            let new_account = RlpAccount::new(
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
                            tx.set_account(address.clone(), None::<RlpAccount>).unwrap();
                        }
                        _ => unreachable!(),
                    }
                }
                tx.commit().unwrap();
            });
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
    bench_mixed_operations
);
criterion_main!(benches);
