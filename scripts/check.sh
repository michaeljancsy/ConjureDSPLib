#!/usr/bin/env bash
# The full local check every pull request reports: Rust format, lints and tests,
# then the proofs (scripts/prove.sh). GitHub Actions do not run on this private repository.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
printf '== cargo fmt --check\n';   cargo fmt --check
printf '== cargo clippy\n';        cargo clippy --all-targets -- -D warnings
printf '== cargo test\n';          cargo test
"$ROOT/scripts/prove.sh"
