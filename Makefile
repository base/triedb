BASELINE := main

# this will modify files in place
format:
	@cargo clippy --fix
	@cargo fmt

bench-baseline:
	@cargo bench -- --save-baseline $(shell git rev-parse --abbrev-ref HEAD)

bench-compare:
	@cargo bench -- --baseline $(BASELINE)

test:
	@cargo test
