# this will modify files in place
format:
	@cargo fmt

bench:
	cargo bench --features "benchmarking"
