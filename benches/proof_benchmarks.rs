mod benchmark_common;

use benchmark_common::{
    generate_random_address, generate_storage_paths_values, get_base_database, BATCH_SIZE,
    DEFAULT_SETUP_DB_CONTRACT_SIZE, DEFAULT_SETUP_DB_EOA_SIZE,
    DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT, SEED_CONTRACT, SEED_EOA,
};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::*;
use std::time::Duration;
use triedb::{path::AddressPath, Database};

fn bench_account_get_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("account_get_proof");

    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );

    let mut rng = StdRng::seed_from_u64(SEED_EOA);
    let addresses: Vec<AddressPath> =
        (0..BATCH_SIZE).map(|_| generate_random_address(&mut rng)).collect();

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("account_get_proof", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let db_path = base_dir.file_name_path.clone();
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                let tx = db.begin_ro().unwrap();
                for addr in &addresses {
                    let result = tx.get_account_with_proof(addr.clone()).unwrap();
                    assert!(result.is_some());
                }
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

fn bench_storage_get_proof(c: &mut Criterion) {
    let mut group = c.benchmark_group("storage_get_proof");

    let base_dir = get_base_database(
        DEFAULT_SETUP_DB_EOA_SIZE,
        DEFAULT_SETUP_DB_CONTRACT_SIZE,
        DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT,
    );

    let mut rng = StdRng::seed_from_u64(SEED_CONTRACT);
    let total_storage_per_address = DEFAULT_SETUP_DB_STORAGE_PER_CONTRACT / 2;
    let total_addresses = BATCH_SIZE / total_storage_per_address;
    let addresses: Vec<AddressPath> =
        (0..total_addresses).map(|_| generate_random_address(&mut rng)).collect();
    let storage_paths_values = generate_storage_paths_values(&addresses, total_storage_per_address);

    group.throughput(criterion::Throughput::Elements(BATCH_SIZE as u64));
    group.measurement_time(Duration::from_secs(30));
    group.bench_function(BenchmarkId::new("storage_get_proof", BATCH_SIZE), |b| {
        b.iter_with_setup(
            || {
                let db_path = base_dir.file_name_path.clone();
                Database::open(db_path, &Config::default()).unwrap()
            },
            |db| {
                let tx = db.begin_ro().unwrap();
                for (storage_path, _) in &storage_paths_values {
                    let result = tx.get_storage_with_proof(storage_path.clone()).unwrap();
                    assert!(result.is_some());
                }
                tx.commit().unwrap();
            },
        );
    });

    group.finish();
}

criterion_group!(benches, bench_account_get_proof, bench_storage_get_proof);

criterion_main!(benches);
