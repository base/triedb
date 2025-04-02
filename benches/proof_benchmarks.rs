use alloy_primitives::{Address, StorageKey, StorageValue, U256};
use alloy_trie::{EMPTY_ROOT_HASH, KECCAK_EMPTY};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use rand::prelude::*;
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

fn setup_database_with_storage(size: usize) -> (TempDir, Database<MmapPageManager>) {
    let dir = TempDir::new("triedb_bench_proof").unwrap();
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
                    let a = tx.get_storage_with_proof(storage_path.clone()).unwrap();
                    assert!(a.is_some());
                }
                tx.commit().unwrap();
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_storage_get_proof,);

criterion_main!(benches);
