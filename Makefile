BASELINE := main

### BEGIN Integration Test Variables ###
ETHEREUM_EXECUTION_SPEC_VERSION=v4.1.0
TESTS_FIXTURES_PATH=tests/fixtures
### END Integration Test Variables ###

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

unit-tests:
	@cargo test --lib

integration-tests: download-ethereum-execution-spec-fixture
	@cargo test --test '*' -- --nocapture

download-ethereum-execution-spec-fixture:
	@if [ ! -d $(TESTS_FIXTURES_PATH) ]; then \
		curl -L \
		https://github.com/ethereum/execution-spec-tests/releases/download/$(ETHEREUM_EXECUTION_SPEC_VERSION)/fixtures_stable.tar.gz | tar -xzf - -C tests; \
	fi

clean:
	@rm -rf $(TESTS_FIXTURES_PATH)
