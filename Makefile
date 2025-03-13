BASELINE := main

.PHONY: format
format:
	@cargo +nightly fmt

.PHONY: lint
lint:
	@cargo clippy --fix --allow-dirty

bench-baseline:
	@cargo bench -- --save-baseline $(shell git rev-parse --abbrev-ref HEAD)

bench-compare:
	@cargo bench -- --baseline $(BASELINE)

test:
	@cargo test
