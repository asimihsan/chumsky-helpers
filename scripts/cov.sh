#!/usr/bin/env bash
# cov.sh - Helper script for interactive code-coverage workflows.
#
# This script wraps `cargo llvm-cov` so you can iterate quickly on coverage for
# specific files or directories without re-building every time.
#
# Usage:
#   scripts/cov.sh warm                 # build + test once, but do **not** print a report
#   scripts/cov.sh file <path> [flags]  # reprint line coverage for a single file
#   scripts/cov.sh file-html <path>     # HTML coverage for a single file and open in browser
#   scripts/cov.sh dir <path>           # reprint line coverage for all .rs files under <path>
#   scripts/cov.sh html                 # full HTML report of the whole workspace and open in browser
#
# Notes:
#   • All sub-commands assume you are at the workspace root (the same place as the Justfile).
#   • `warm` **must** be run at least once after each code change so that the raw
#     coverage data is up-to-date.  After that, `file`, `dir`, and HTML sub-commands
#     are instantaneous because they only re-render existing data.
#   • Extra flags after <path> are passed straight through to `cargo llvm-cov report`.

set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd)
PROJECT_ROOT=$(dirname "$SCRIPT_DIR")
pushd "$PROJECT_ROOT" > /dev/null
trap 'popd > /dev/null' EXIT

cmd=${1:-help}

# Ensure cargo-llvm-cov is installed.
if ! command -v cargo-llvm-cov >/dev/null 2>&1; then
  echo "error: cargo-llvm-cov not found. Install with 'cargo install cargo-llvm-cov'." >&2
  exit 1
fi

usage() {
  grep '^#' "$0" | cut -c 4-
}

warm() {
  echo "[cov] Running full test suite with instrumentation …" >&2
  cargo +nightly llvm-cov --no-report --all-features --workspace --mcdc "$@"
}

file_cov() {
  if [[ $# -lt 1 ]]; then
    echo "error: missing <path> argument for 'file' subcommand" >&2
    usage; exit 1
  fi
  local path=$1; shift
  echo "[cov] Showing coverage for $path …" >&2
  # Workaround: cargo-llvm-cov report does not accept positional file paths. Use a negative regex
  # that ignores everything except the requested file.
  local regex="^(?!.*$(printf '%s' "$path" | sed 's/[.[\\^$*+?{}|()]/\\&/g')).*$"
  cargo +nightly llvm-cov report --text --show-missing-lines --mcdc --ignore-filename-regex "$regex" "$@"
}

file_html() {
  if [[ $# -lt 1 ]]; then
    echo "error: missing <path> argument for 'file-html' subcommand" >&2
    usage; exit 1
  fi
  local path=$1; shift
  echo "[cov] Generating HTML coverage for $path …" >&2
  cargo +nightly llvm-cov report --html --open --mcdc "$path" "$@"
}

dir_cov() {
  if [[ $# -lt 1 ]]; then
    echo "error: missing <dir> argument for 'dir' subcommand" >&2
    usage; exit 1
  fi
  local dir=$1; shift
  echo "[cov] Showing coverage for directory $dir …" >&2
  # Build a negative lookahead regex that keeps only files under the directory.
  mapfile -t files < <(find "$dir" -type f -name '*.rs')
  if [[ ${#files[@]} -eq 0 ]]; then
    echo "error: no .rs files found under $dir" >&2
    exit 1
  fi
  # Join paths with OR and escape regex special characters.
  local joined="$(printf '%s|' "${files[@]}" | sed 's/|$//')"
  local escaped="$(printf '%s' "$joined" | sed 's/[.[\\^$*+?{}|()]/\\&/g')"
  local regex="^(?!.*($escaped)).*$"
  cargo +nightly llvm-cov report --text --show-missing-lines --mcdc --ignore-filename-regex "$regex" "$@"
}

html_full() {
  echo "[cov] Rendering full HTML coverage report …" >&2
  cargo +nightly llvm-cov --html --open --mcdc "$@"
}

json_file() {
  if [[ $# -lt 1 ]]; then
    echo "error: missing <path> argument for 'json-file' subcommand" >&2
    usage; exit 1
  fi
  local path=$1; shift
  echo "[cov] Generating JSON coverage for $path …" >&2
  # Generate JSON and filter with jq for the requested file.
  cargo +nightly llvm-cov --mcdc --json "$@"
}

case "$cmd" in
  warm)
    shift; warm "$@" ;;
  file)
    shift; file_cov "$@" ;;
  file-html)
    shift; file_html "$@" ;;
  dir)
    shift; dir_cov "$@" ;;
  html)
    shift; html_full "$@" ;;
  json-file)
    shift; json_file "$@" ;;
  help|*-h|--help)
    usage ;;
  *)
    echo "error: unknown subcommand: $cmd" >&2
    usage; exit 1 ;;
esac 