set shell := ["bash", "-c"]
set dotenv-load := true

# Default action is to list all available tasks
@default:
    @just --list

# =============================================================================
# Setup and Dependencies
# =============================================================================

setup:
    #!/usr/bin/env bash
    set -e

    mise trust
    mise install

    if [[ "$OSTYPE" == "darwin"* ]]; then
        just mac-setup
    fi

    uv venv
    uv sync

    rustup toolchain install nightly
    rustup target add wasm32-wasip1
    rustup component add llvm-tools-preview
    rustup component add rustfmt
    rustup component add clippy

mac-setup:
    #!/usr/bin/env bash
    set -e

    if [[ "$OSTYPE" != "darwin"* ]]; then
        echo "This script is only for macOS."
        exit 1
    fi

    if ! command -v brew &> /dev/null; then
        echo "brew command not found, please install Homebrew first."
        exit 1
    fi

    brew install libiconv llvm
    rustup component add llvm-tools-preview
    rustup component add llvm-tools-preview --toolchain nightly-aarch64-apple-darwin
    if ! xcode-select -p >/dev/null 2>&1; then
        xcode-select --install
        sudo xcode-select --switch /Library/Developer/CommandLineTools
    fi

update-deps:
    cargo +nightly -Z unstable-options update --breaking

# =============================================================================
# Rust Development Tasks
# =============================================================================

# Development workflow
rust-dev: rust-format rust-clippy-fix rust-test-all

# Watching for changes
rust-watch:
    cargo watch -x check -x test

# Formatting
rust-check-format:
    cargo fmt -- --check

rust-format:
    cargo fmt

# Linting 
rust-check-clippy:
    cargo clippy --all-targets --all-features -- -D warnings

rust-clippy-fix:
    cargo clippy --all-targets --all-features --fix --allow-dirty -- -D warnings

rust-test-all: rust-test rust-test-doc

# Testing
rust-test:
    cargo nextest run --all-features --no-fail-fast

rust-test-doc:
    cargo test --doc

rust-test-miri:
    MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-symbolic-alignment-check" PROPTEST_DISABLE_FAILURE_PERSISTENCE=1 cargo +nightly miri test

# Coverage
rust-coverage:
    cargo llvm-cov --all-features --workspace --lcov --output-path lcov.info
    cargo llvm-cov report --html

rust-coverage-ci:
    cargo llvm-cov --all-features --workspace
    # cargo llvm-cov --all-features --workspace --fail-under-lines 80

# Security & Dependencies
rust-audit:
    cargo audit
    cargo deny check

# MSRV verification
rust-msrv-check:
    cargo msrv verify

# Feature matrix testing
rust-hack-check:
    cargo hack test --each-feature --no-dev-deps

# Building
rust-build:
    cargo build

rust-build-release:
    cargo build --release

# Cleaning
rust-clean:
    cargo clean

# Run all Rust checks
rust-check-all: rust-check-format rust-check-clippy rust-test-all rust-coverage-ci rust-audit

# =============================================================================
# Cross-Language Tasks (All Languages)
# =============================================================================

# Combined linting across all languages
lint-all: rust-check-clippy copyright-check

# Combined testing across all languages
test-all: rust-test

# Combined building across all languages
build-all: rust-build rust-build-release

# Combined cleaning across all languages
clean-all: rust-clean

# =============================================================================
# Copyright and Legal
# =============================================================================

copyright:
    mise x -- bash -c 'fd -e rs -e ts -e js -e jsx -e tsx -e go -e py | xargs addlicense -f copyright.tmpl -c "Asim Ihsan" -v -s'

copyright-check:
    mise x -- bash -c 'fd -e rs -e ts -e js -e jsx -e tsx -e go -e py | xargs addlicense -f copyright.tmpl -c "Asim Ihsan" -v -s -check'

# =============================================================================
# Development Workflows
# =============================================================================



# Development workflow for all languages
dev-all: rust-dev
    wait

# =============================================================================
# CI and Release Tasks
# =============================================================================

# Full CI pipeline
ci: build-all lint-all test-all

# Release preparation
release-prep: rust-check-all
    git status
    @echo "Ready for release if git status is clean"

# =============================================================================
# Legacy Aliases (for backwards compatibility)
# =============================================================================

# Legacy short aliases - prefer the explicit rust-* versions above
alias format := rust-format
alias clippy := rust-check-clippy
alias test := rust-test
alias build := rust-build
alias clean := rust-clean
alias dev := rust-dev
alias watch := rust-watch
alias audit := rust-audit

# Legacy combined aliases - prefer the *-all versions above
alias check := lint-all
alias coverage := rust-coverage
alias cov := rust-coverage-ci

# Legacy coverage with platform-specific handling
cov-local:
    #!/usr/bin/env bash
    set -e
    
    if [[ "$OSTYPE" == "darwin"* ]]; then
        cargo +nightly llvm-cov nextest --no-fail-fast --text --show-missing-lines --mcdc
    else
        cargo llvm-cov nextest --no-fail-fast --text --show-missing-lines --mcdc
    fi

# =============================================================================
# Iterative Coverage Helpers (local development)
# =============================================================================

# Build & run full test-suite once, producing raw coverage data but **no** report.
cov-warm:
    bash scripts/cov.sh warm

# Re-print line coverage for a single file. Example:
#   just cov-file src/lib.rs
cov-file file:
    bash scripts/cov.sh file {{file}}

# Generate HTML coverage for a single file and open it in the browser.
cov-file-html file:
    bash scripts/cov.sh file-html {{file}}

# Re-print coverage for all .rs files under a directory path.
cov-dir dir:
    bash scripts/cov.sh dir {{dir}}

# Full HTML coverage report (opens browser).
cov-html:
    bash scripts/cov.sh html

cov-json-file file:
    bash scripts/cov.sh json-file {{file}}
