set shell := ["bash", "-c"]
set dotenv-load := true

# Default action is to list all available tasks
@default:
    @just --list

setup:
    #!/usr/bin/env bash

    if [[ "$OSTYPE" == "darwin"* ]]; then
        just mac-setup
    fi

    devbox install
    devbox run mise trust
    devbox run mise install
    rustup toolchain install nightly
    cargo +stable install cargo-llvm-cov --locked
    rustup component add llvm-tools-preview --toolchain nightly-aarch64-apple-darwin
    rustup component add rustfmt
    rustup component add clippy
    cargo binstall cargo-nextest --secure --no-confirm
    pre-commit install
    pre-commit install-hooks

mac-setup:
    brew install libiconv llvm
    cargo install cargo-llvm-cov
    rustup component add llvm-tools-preview
    rustup component add llvm-tools-preview --toolchain nightly-aarch64-apple-darwin
    xcode-select --install
    sudo xcode-select --switch /Library/Developer/CommandLineTools

update-deps:
    cargo update

# Development tasks
watch:
    cargo watch -x check -x test

# Rust tasks
rust-check:
    cargo check --all-targets

rust-test:
    cargo nextest run --all-targets --no-fail-fast
    cargo test --doc --no-fail-fast

rust-doc:
    cargo doc --no-deps --document-private-items

rust-audit:
    cargo audit || exit 1
    cargo deny check || exit 1

rust-build:
    cargo build

rust-fmt:
    cargo fmt --all

rust-clippy:
    cargo clippy --all-targets -- -D warnings

rust-clean:
    cargo clean

copyright:
    fd -e rs -e ts -e js -e jsx -e tsx | xargs addlicense -f copyright.tmpl -c "Asim Ihsan" -v -s

copyright-check:
    fd -e rs -e ts -e js -e jsx -e tsx | xargs addlicense -f copyright.tmpl -c "Asim Ihsan" -v -s -check

# Combined tasks
check: rust-check rust-fmt rust-clippy rust-audit copyright-check

test: rust-test

cov:
    cargo llvm-cov nextest

cov-local-web:
    cargo +nightly llvm-cov nextest --no-fail-fast --open --show-missing-lines --mcdc
    
cov-local:
    cargo +nightly llvm-cov nextest --no-fail-fast --text --show-missing-lines --mcdc

build: rust-build

clean: rust-clean

# CI tasks
ci: build check test cov
