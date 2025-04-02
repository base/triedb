mod benchmark_common;

use alloy_primitives::{StorageKey, U256};
use benchmark_common::{
    generate_random_address, setup_database, setup_database_with_storage, BATCH_SIZE,
};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::*;
use triedb::path::{AddressPath, StoragePath};

const SIZES: &[usize] = &[1_000_000, 3_000_000];

fn bench_account_get_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("account_get_proof");

    for &size in SIZES {
        let (_dir, db) = setup_database(size);
        let mut rng = StdRng::seed_from_u64(42);
        let addresses: Vec<AddressPath> =
            (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("account_get_proof", size), &size, |b, _| {
            b.iter(|| {
                let tx = db.begin_ro().unwrap();
                for addr in &addresses {
                    let result = tx.get_account_with_proof(addr.clone()).unwrap();
                    assert!(result.is_some());
                }
                tx.commit().unwrap();
            });
        });
    }
    group.finish();
}

fn bench_storage_get_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("storage_get_proof");

    for &size in SIZES {
        let (_dir, db) = setup_database_with_storage(size);
        let mut rng = StdRng::seed_from_u64(42);
        let total_addresses = size / BATCH_SIZE;
        let addresses: Vec<AddressPath> =
            (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();

        let total_storage_per_address = BATCH_SIZE / total_addresses;
        let storage_paths: Vec<StoragePath> = addresses
            .iter()
            .flat_map(|address| {
                (0..=total_storage_per_address).map(|i| {
                    StoragePath::for_address_path_and_slot(
                        address.clone(),
                        StorageKey::from(U256::from(i)),
                    )
                })
            })
            .collect();

        group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(BenchmarkId::new("storage_get_proof", size), &size, |b, _| {
            b.iter(|| {
                let tx = db.begin_ro().unwrap();
                for storage_path in &storage_paths {
                    let result = tx.get_storage_with_proof(storage_path.clone()).unwrap();
                    assert!(result.is_some());
                }
                tx.commit().unwrap();
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_account_get_proof, bench_storage_get_proof);

criterion_main!(benches);
