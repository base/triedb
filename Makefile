SHELL := /bin/bash

BASELINE := main

### BEGIN Integration Test Variables ###
ETHEREUM_EXECUTION_SPEC_VERSION := v4.1.0
ETHEREUM_EXECUTION_SPEC_VERSION_FILE_HASH := d463caf870a9330b56944572474f828b5a518315b521524822d907fd9e512a93ada37cb9b412119c8eaaa8d6588dd5e9
TESTS_FIXTURES_PATH := tests/fixtures
### END Integration Test Variables ###

.PHONY: format
format:
	@cargo +nightly fmt

.PHONY: lint
lint:
	@cargo clippy --fix --allow-dirty

.PHONY: bench-baseline
bench-baseline:
	@cargo bench --bench database_benchmarks -- --save-baseline $(shell git rev-parse --abbrev-ref HEAD)

.PHONY: bench-compare
bench-compare:
	@cargo bench --bench database_benchmarks -- --baseline $(BASELINE)

.PHONY: test
test:
	@cargo test $(cargo_flags)

.PHONY: unit-tests
unit-tests:
	cargo test --lib $(cargo_flags) -- $(test_flags)

.PHONY: integration-tests
integration-tests: tests/fixtures
	@cargo test --test '*' $(cargo_flags) -- $(test_flags)

tests/fixtures: tests/fixtures_stable.tar.gz
	@tar -xzf $< -C $(@D)
	@rm -rf tests/fixtures_stable.tar.gz

tests/fixtures_stable.tar.gz:
	@curl -L https://github.com/ethereum/execution-spec-tests/releases/download/$(ETHEREUM_EXECUTION_SPEC_VERSION)/fixtures_stable.tar.gz > $@.tmp.tar
	@shasum -a 384 -c <<< "$(ETHEREUM_EXECUTION_SPEC_VERSION_FILE_HASH)  $@.tmp.tar"
	@mv $@.tmp.tar $@

.PHONY: clean
clean:
	@rm -rf tests/fixtures
	@rm -rf tests/fixtures_stable.tar.gz
