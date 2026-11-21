#!/usr/bin/env bash
# The full local check every pull request reports: Rust format, lints and tests,
# then the proofs (scripts/prove.sh). GitHub Actions do not run on this private repository.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUST="$(sed -n 's/^RUST=//p' proofs/PINS)"
case "$(rustc --version)" in "rustc $RUST "*) ;; *) echo "FAIL: rustc is not $RUST (see rust-toolchain.toml)" >&2; exit 1 ;; esac
printf '== cargo fmt --check\n';   cargo fmt --check
printf '== cargo clippy\n';        cargo clippy --all-targets -- -D warnings
printf '== cargo test\n';          cargo test
printf '== cargo doc\n';           RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --quiet
"$ROOT/scripts/prove.sh"
