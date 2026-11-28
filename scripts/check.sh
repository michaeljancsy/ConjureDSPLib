#!/usr/bin/env bash
# The full local check every pull request reports: Rust format, lints and tests,
# then the proofs (scripts/prove.sh).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUST="$(sed -n 's/^RUST=//p' proofs/PINS)"
case "$(rustc --version)" in "rustc $RUST "*) ;; *) echo "FAIL: rustc is not $RUST (see rust-toolchain.toml)" >&2; exit 1 ;; esac
printf '== cargo fmt --check\n';   cargo fmt --check
printf '== cargo clippy\n';        cargo clippy --all-targets -- -D warnings
printf '== cargo clippy (std)\n';  cargo clippy --all-targets --features std -- -D warnings
printf '== cargo test\n';          cargo test
printf '== cargo test (std)\n';    cargo test --features std
printf '== cargo doc\n';           RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --quiet
printf '== cargo doc (std)\n';     RUSTDOCFLAGS='-D warnings' cargo doc --no-deps --quiet --features std
"$ROOT/scripts/prove.sh"
