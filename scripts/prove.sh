#!/usr/bin/env bash
# Build and check the Lean proofs about this crate, in order:
#   1. Charon: Rust -> LLBC
#   2. Aeneas: LLBC -> Lean (proofs/ConjureDSPLib/Code/), which must match what is committed
#   3. lake build
#   4. axiom check: only propext, Classical.choice and Quot.sound; no sorry
#
# Tool locations (defaults in brackets):
#   AENEAS_DIR     checkout of michaeljancsy/aeneas at the commit in proofs/PINS, with the Aeneas
#                  binary built [~/Projects/ConjureDSP/toolchains/aeneas-<first 8 of commit>]
#   CHARON_BIN     Charon binary at the commit in proofs/PINS [$AENEAS_DIR/charon/bin/charon]
#   LAKE_PACKAGES  optional folder of already-built Lake packages (Mathlib, FloatLib, ...) to link
#                  as proofs/.lake/packages, so they are not downloaded and rebuilt again
#
# Needs the `aeneas` opam switch only to build Aeneas itself, not to run it.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
# shellcheck disable=SC1091
source proofs/PINS

AENEAS_DIR="${AENEAS_DIR:-$HOME/Projects/ConjureDSP/toolchains/aeneas-${AENEAS_COMMIT:0:8}}"
CHARON_BIN="${CHARON_BIN:-$AENEAS_DIR/charon/bin/charon}"
AENEAS_BIN="$AENEAS_DIR/bin/aeneas"

step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

step "Checking tool versions against proofs/PINS"
[ -x "$AENEAS_BIN" ] || fail "no Aeneas binary at $AENEAS_BIN (set AENEAS_DIR)"
[ -x "$CHARON_BIN" ] || fail "no Charon binary at $CHARON_BIN (set CHARON_BIN)"
got_aeneas="$(git -C "$AENEAS_DIR" rev-parse HEAD)"
[ "$got_aeneas" = "$AENEAS_COMMIT" ] || fail "Aeneas is at $got_aeneas, PINS says $AENEAS_COMMIT"
got_charon="$("$CHARON_BIN" version)"
case "$got_charon" in *"$CHARON_COMMIT"*) ;; *) fail "Charon reports '$got_charon', PINS says $CHARON_COMMIT" ;; esac
pin_charon="$(tail -n 1 "$AENEAS_DIR/charon-pin")"
[ "$pin_charon" = "$CHARON_COMMIT" ] || fail "Aeneas's charon-pin is $pin_charon, PINS says $CHARON_COMMIT"
grep -qx "leanprover/lean4:$LEAN" proofs/lean-toolchain || fail "proofs/lean-toolchain is not $LEAN"
grep -qx "leanprover/lean4:$LEAN" "$AENEAS_DIR/backends/lean/lean-toolchain" \
  || fail "Aeneas's Lean library does not use $LEAN"
echo "Aeneas $AENEAS_COMMIT, Charon $CHARON_COMMIT, Lean $LEAN: OK"

mkdir -p proofs/.toolchain proofs/.lake
ln -sfn "$AENEAS_DIR" proofs/.toolchain/aeneas
if [ -n "${LAKE_PACKAGES:-}" ]; then
  [ -e proofs/.lake/packages ] || ln -s "$LAKE_PACKAGES" proofs/.lake/packages
  [ -e "$AENEAS_DIR/backends/lean/.lake/packages" ] || {
    mkdir -p "$AENEAS_DIR/backends/lean/.lake"
    ln -s "$LAKE_PACKAGES" "$AENEAS_DIR/backends/lean/.lake/packages"
  }
fi

step "1. Charon"
mkdir -p target
"$CHARON_BIN" cargo --preset=aeneas --dest-file target/conjure_dsp_lib.llbc

step "2. Aeneas"
"$AENEAS_BIN" -backend lean target/conjure_dsp_lib.llbc -dest proofs/ConjureDSPLib/Code
if ! git diff --quiet -- proofs/ConjureDSPLib/Code \
   || [ -n "$(git ls-files --others --exclude-standard -- proofs/ConjureDSPLib/Code)" ]; then
  git status --short -- proofs/ConjureDSPLib/Code
  if [ "${ALLOW_REGENERATED:-0}" = 1 ]; then
    echo "Note: the generated Lean changed (allowed by ALLOW_REGENERATED=1). Commit it."
  else
    fail "the generated Lean differs from what is committed. Re-run with ALLOW_REGENERATED=1 and commit it."
  fi
fi

step "3. lake build"
( cd proofs && lake build )

step "4. Axiom check"
( cd proofs && lake env lean --run AxiomCheck.lean )

printf '\nAll proofs built and checked.\n'
