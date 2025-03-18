use std::collections::HashMap;

use alloy_trie::Nibbles;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use triedb::context::{NibblesHasherBuilder, NibblesMap};

// Helper function to generate test data
fn generate_test_nibbles(count: usize) -> Vec<Nibbles> {
    let mut nibbles = Vec::with_capacity(count);
    for i in 0..count {
        // Create varied nibbles of different lengths
        let bytes = i.to_be_bytes();
        let nibbles_data: Vec<u8> =
            bytes.iter().flat_map(|&b| vec![(b >> 4) & 0xF, b & 0xF]).collect();
        nibbles.push(Nibbles::from_nibbles(&nibbles_data));
    }
    nibbles
}

fn bench_hashmaps(c: &mut Criterion) {
    let mut group = c.benchmark_group("HashMap Comparison");

    // Test with different sizes
    for size in [10, 100, 1000].iter() {
        let test_data = generate_test_nibbles(*size);

        // Benchmark insertion
        group.bench_function(format!("hashmap_default_hash_insert_{}", size), |b| {
            b.iter(|| {
                let mut map = HashMap::with_capacity(1000);
                for (i, nibbles) in test_data.iter().enumerate() {
                    map.insert(nibbles.clone(), (i as u32, 0u8));
                }
                black_box(map)
            });
        });

        group.bench_function(format!("hashmap_nibbles_hash_insert_{}", size), |b| {
            b.iter(|| {
                let mut map =
                    NibblesMap::with_capacity_and_hasher(1000, NibblesHasherBuilder::default());
                for (i, nibbles) in test_data.iter().enumerate() {
                    map.insert(nibbles.clone(), (i as u32, 0u8));
                }
                black_box(map)
            });
        });

        // Create pre-populated maps for lookup benchmarks
        let mut default_map = HashMap::with_capacity(1000);
        let mut custom_map =
            NibblesMap::with_capacity_and_hasher(1000, NibblesHasherBuilder::default());
        for (i, nibbles) in test_data.iter().enumerate() {
            default_map.insert(nibbles.clone(), (i as u32, 0u8));
            custom_map.insert(nibbles.clone(), (i as u32, 0u8));
        }

        // Benchmark lookups
        group.bench_function(format!("default_hashmap_lookup_{}", size), |b| {
            b.iter(|| {
                for nibbles in test_data.iter() {
                    black_box(default_map.get(nibbles));
                }
            });
        });

        group.bench_function(format!("custom_hashmap_lookup_{}", size), |b| {
            b.iter(|| {
                for nibbles in test_data.iter() {
                    black_box(custom_map.get(nibbles));
                }
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_hashmaps);
criterion_main!(benches);
