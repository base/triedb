cargo build --release --example insert --no-default-features --features buffer_pool_backend
mv ./target/release/examples/insert ./target/release/examples/insert-buffer-pool
cargo build --release --example insert --no-default-features --features mmap_backend
mv ./target/release/examples/insert ./target/release/examples/insert-mmap

mkdir -p target/db/mmap
mkdir -p target/db/buffer-pool

for i in 1 2 1000 10000 100000; do
    echo "=============================================================================="
    echo "== Running for mmap/db_${i}"
    time ./target/release/examples/insert-mmap ./target/db/mmap/db_${i} ${i} 1000 100 10
    sleep 10
    echo "== Running for buffer-pool/db_${i}"
    time ./target/release/examples/insert-buffer-pool ./target/db/buffer-pool/db_${i} ${i} 1000 100 10
    sleep 10

    # Get and compare hashes
    mmap_hash=$(shasum -a 256 ./target/db/mmap/db_${i} | cut -d' ' -f1)
    buffer_hash=$(shasum -a 256 ./target/db/buffer-pool/db_${i} | cut -d' ' -f1)
    echo "Comparing hashes for db_${i}:"
    echo "MMAP:        ${mmap_hash}"
    echo "Buffer Pool: ${buffer_hash}"
    if [ "$mmap_hash" = "$buffer_hash" ]; then
        echo "✅ Hashes match"
    else
        echo "❌ Hashes differ"
    fi
done
