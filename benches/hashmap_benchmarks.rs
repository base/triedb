use std::collections::HashMap;

use alloy_primitives::Address;
use alloy_trie::Nibbles;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::prelude::*;
use triedb::{context::B512Map, path::AddressPath};

fn generate_random_address(rng: &mut StdRng) -> AddressPath {
    let addr = Address::random_with(rng);
    AddressPath::for_address(addr)
}

fn generate_test_nibbles(count: usize) -> Vec<Nibbles> {
    let mut nibbles = Vec::with_capacity(count);
    let mut rng = StdRng::seed_from_u64(42);

    nibbles.extend((0..count).map(|_| {
        let address = generate_random_address(&mut rng);
        let nibbles = address.to_nibbles();
        nibbles.clone()
    }));

    nibbles
}

fn bench_hashmaps(c: &mut Criterion) {
    let mut group = c.benchmark_group("HashMap Comparison");

    // Test with different sizes
    for size in [10, 100, 1000].iter() {
        let test_data = generate_test_nibbles(*size);

        // Benchmark insertion
        group.bench_function(format!("default_hash_insert_{}", size), |b| {
            b.iter(|| {
                let mut map = HashMap::with_capacity(1000);
                for (i, nibbles) in test_data.iter().enumerate() {
                    map.insert(nibbles.clone(), (i as u32, 0u8));
                }
                black_box(map)
            });
        });

        group.bench_function(format!("b512map_fbhash_insert_{}", size), |b| {
            b.iter(|| {
                let map = B512Map::with_capacity(1000);
                for (i, nibbles) in test_data.iter().enumerate() {
                    map.insert(nibbles, (i as u32, 0u8));
                }
                black_box(map)
            });
        });

        // Create pre-populated maps for lookup benchmarks
        let mut default_map = HashMap::with_capacity(1000);
        let b512_map = B512Map::with_capacity(1000);
        for (i, nibbles) in test_data.iter().enumerate() {
            default_map.insert(nibbles.clone(), (i as u32, 0u8));
            b512_map.insert(nibbles, (i as u32, 0u8));
        }

        group.bench_function(format!("default_hashmap_lookup_{}", size), |b| {
            b.iter(|| {
                for nibbles in test_data.iter() {
                    black_box(default_map.get(nibbles));
                }
            });
        });

        group.bench_function(format!("b512map_lookup_{}", size), |b| {
            b.iter(|| {
                for nibbles in test_data.iter() {
                    black_box(b512_map.get(nibbles));
                }
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_hashmaps);
criterion_main!(benches);
