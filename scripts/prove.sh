#!/usr/bin/env bash
# Build and check the Lean proofs about this crate, in order:
#   1. Charon: Rust -> LLBC
#   2. Aeneas: LLBC -> Lean (proofs/ConjureDSPLib/Code/Types.lean and Funs.lean), which must match
#      the last commit
#   3. lake build
#   4. axiom check (proofs/AxiomCheck.lean): every module file built; only propext,
#      Classical.choice and Quot.sound; no sorry; no axioms of our own; no public theorem
#      statement names Lean's NaN constants or Aeneas's bitsOf, signBit or copysignBits helpers
#      (Float.toBits is allowed, for -0)
#   5. kernel replay: leanchecker re-checks every declaration of every module
#
# Tool locations (defaults in brackets):
#   AENEAS_DIR     clean checkout of michaeljancsy/aeneas at the commit in proofs/PINS, with the
#                  Aeneas binary built from it and Charon in its charon/ folder
#                  [the author's local layout: ~/Projects/ConjureDSP/toolchains/aeneas-<first 8
#                  characters of the commit>; anyone else should set AENEAS_DIR]
#   CHARON_BIN     Charon binary at the commit in proofs/PINS [$AENEAS_DIR/charon/bin/charon]
#   LAKE_PACKAGES  optional folder of already-built Lake packages (Mathlib, FloatLib, ...). It is
#                  linked as proofs/.lake/packages and as $AENEAS_DIR/backends/lean/.lake/packages,
#                  so nothing is downloaded or rebuilt. Each package there must already be at the
#                  revision in proofs/lake-manifest.json; the script refuses to use it otherwise.
#   ALLOW_REGENERATED=1  report changed generated Lean instead of failing (then commit it)
#
# Building Aeneas itself needs the `aeneas` opam switch; running it does not.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
# PINS holds only KEY=value lines, so it can be read as shell.
# shellcheck disable=SC1091
source proofs/PINS

step() { printf '\n== %s\n' "$*"; }
fail() { printf 'FAIL: %s\n' "$*" >&2; exit 1; }

command -v python3 >/dev/null 2>&1 || fail "python3 is needed (install it with your system's package manager)"
git rev-parse --is-inside-work-tree >/dev/null 2>&1 \
  || fail "run this from a git checkout of ConjureDSPLib (it compares generated Lean with the last commit)"

AENEAS_DIR="${AENEAS_DIR:-$HOME/Projects/ConjureDSP/toolchains/aeneas-${AENEAS_COMMIT:0:8}}"
[ -d "$AENEAS_DIR" ] || fail "no Aeneas checkout at $AENEAS_DIR (set AENEAS_DIR)"
AENEAS_DIR="$(cd "$AENEAS_DIR" && pwd)"
CHARON_BIN="${CHARON_BIN:-$AENEAS_DIR/charon/bin/charon}"
AENEAS_BIN="$AENEAS_DIR/bin/aeneas"

step "Checking tool versions against proofs/PINS"
[ -x "$AENEAS_BIN" ] || fail "no Aeneas binary at $AENEAS_BIN"
[ -x "$CHARON_BIN" ] || fail "no Charon binary at $CHARON_BIN (set CHARON_BIN)"
got="$(git -C "$AENEAS_DIR" rev-parse HEAD)"
[ "$got" = "$AENEAS_COMMIT" ] || fail "Aeneas checkout is at $got, PINS says $AENEAS_COMMIT"
[ -z "$(git -C "$AENEAS_DIR" status --porcelain --untracked-files=no)" ] \
  || fail "the Aeneas checkout at $AENEAS_DIR has local changes"
# Aeneas reports `git describe --always --dirty` of the tree it was built from. Accept the same
# description of this (clean) checkout, which is the tag name on a clone that has the tag on the
# pinned commit, or any description naming the commit (`<older tag>-<n>-g<commit>`).
got="$("$AENEAS_BIN" -version)"
described="$(git -C "$AENEAS_DIR" describe --always --dirty)"
case "$got" in
  *-dirty*) fail "the Aeneas binary was built from a modified tree: $got" ;;
  "aeneas $described" | *"-g${AENEAS_COMMIT:0:8}"*) ;;
  *) fail "the Aeneas binary reports '$got'; this checkout is '$described' (commit \
${AENEAS_COMMIT:0:8}); rebuild it" ;;
esac
got="$("$CHARON_BIN" version)"
case "$got" in *"$CHARON_COMMIT"*) ;; *) fail "Charon reports '$got', PINS says $CHARON_COMMIT" ;; esac
got="$(tail -n 1 "$AENEAS_DIR/charon-pin")"
[ "$got" = "$CHARON_COMMIT" ] || fail "Aeneas's charon-pin is $got, PINS says $CHARON_COMMIT"
grep -qx "leanprover/lean4:$LEAN" proofs/lean-toolchain || fail "proofs/lean-toolchain is not $LEAN"
grep -qx "leanprover/lean4:$LEAN" "$AENEAS_DIR/backends/lean/lean-toolchain" \
  || fail "Aeneas's Lean library does not use Lean $LEAN"
manifest_rev() { # package name, field -> value from proofs/lake-manifest.json
  python3 -c 'import json,sys
for p in json.load(open("proofs/lake-manifest.json"))["packages"]:
    if p["name"] == sys.argv[1]: print(p.get(sys.argv[2]) or ""); break' "$1" "$2"
}
[ "$(manifest_rev mathlib inputRev)" = "$MATHLIB" ] || fail "lake-manifest.json's Mathlib is not $MATHLIB"
[ "$(manifest_rev FloatLib rev)" = "$FLOATLIB_COMMIT" ] \
  || fail "lake-manifest.json's FloatLib is not $FLOATLIB_COMMIT"
grep -q "\"$FLOATLIB_COMMIT\"" proofs/lakefile.lean || fail "lakefile.lean's FloatLib is not $FLOATLIB_COMMIT"
echo "Aeneas ${AENEAS_COMMIT:0:8}, Charon ${CHARON_COMMIT:0:8}, Lean $LEAN, Mathlib $MATHLIB, FloatLib ${FLOATLIB_COMMIT:0:8}: OK"

link() { # target, link path: make the link, or fail if something else is already there
  if [ -L "$2" ]; then
    [ "$(readlink "$2")" = "$1" ] || fail "$2 already links to $(readlink "$2"), not $1"
  elif [ -e "$2" ]; then
    fail "$2 already exists and is not a link to $1; remove it or unset LAKE_PACKAGES"
  else
    mkdir -p "$(dirname "$2")"
    ln -s "$1" "$2"
  fi
}
mkdir -p proofs/.toolchain
ln -sfn "$AENEAS_DIR" proofs/.toolchain/aeneas
if [ -n "${LAKE_PACKAGES:-}" ]; then
  LAKE_PACKAGES="$(cd "$LAKE_PACKAGES" && pwd)"
  # Refuse a shared package folder at other revisions: Lake would check them out in place.
  python3 - "$LAKE_PACKAGES" <<'PY' || fail "LAKE_PACKAGES does not match proofs/lake-manifest.json"
import json, subprocess, sys
bad = False
for p in json.load(open("proofs/lake-manifest.json"))["packages"]:
    if p["type"] != "git":
        continue
    d = f"{sys.argv[1]}/{p['name']}"
    try:
        head = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"], capture_output=True,
                              text=True, check=True).stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        head = "(missing)"
    if head != p["rev"]:
        print(f"  {p['name']}: {head}, manifest says {p['rev']}", file=sys.stderr)
        bad = True
    elif subprocess.run(["git", "-C", d, "status", "--porcelain", "--untracked-files=no"],
                        capture_output=True, text=True).stdout.strip():
        print(f"  {p['name']}: has local changes", file=sys.stderr)
        bad = True
sys.exit(1 if bad else 0)
PY
  link "$LAKE_PACKAGES" proofs/.lake/packages
  link "$LAKE_PACKAGES" "$AENEAS_DIR/backends/lean/.lake/packages"
fi

step "1. Charon"
mkdir -p target
# All `Debug` and `Default` implementations are left out: they are not DSP code. Translating
# `Debug` would bring in Aeneas axioms for formatting floats; `Default` is left out to keep the
# generated Lean to the DSP code. So proved code cannot call them (for example
# `StateF64::default()`).
"$CHARON_BIN" cargo --preset=aeneas \
  --exclude '{impl core::fmt::Debug for _}' --exclude '{impl core::default::Default for _}' \
  --dest-file target/conjure_dsp_lib.llbc

step "2. Aeneas"
# Split files: Code/Types.lean and Code/Funs.lean. Funs.lean imports Code/FunsExternal.lean, the
# hand-written models of the external functions the crate calls (libm's tan, pow, sqrt). Aeneas
# also writes Code/FunsExternal_Template.lean, which declares those functions as axioms; it is
# moved out of the Lean library to target/ so it is neither built nor committed (compare it with
# FunsExternal.lean when the crate calls a new external function; lake build fails until
# FunsExternal.lean defines it).
"$AENEAS_BIN" -backend lean target/conjure_dsp_lib.llbc -dest proofs -subdir ConjureDSPLib/Code \
  -split-files
if [ -f proofs/ConjureDSPLib/Code/FunsExternal_Template.lean ]; then
  mv proofs/ConjureDSPLib/Code/FunsExternal_Template.lean target/FunsExternal_Template.lean
fi
if ! git diff --quiet HEAD -- proofs/ConjureDSPLib/Code \
   || [ -n "$(git ls-files --others --exclude-standard -- proofs/ConjureDSPLib/Code)" ]; then
  git status --short -- proofs/ConjureDSPLib/Code
  if [ "${ALLOW_REGENERATED:-0}" = 1 ]; then
    echo "Note: the generated Lean differs from the last commit (allowed by ALLOW_REGENERATED=1). Commit it."
  else
    fail "the generated Lean differs from the last commit. Re-run with ALLOW_REGENERATED=1 and commit it."
  fi
fi

step "3. lake build"
( cd proofs && lake build )

step "4. Axiom check"
( cd proofs && lake env lean --run AxiomCheck.lean )

step "5. Kernel replay (leanchecker)"
# leanchecker re-checks every compiled module whose name starts with ConjureDSPLib, so first make
# sure no compiled file is left over from a deleted source file.
stale="$(cd proofs/.lake/build/lib/lean && find ConjureDSPLib -name '*.olean' | while read -r f; do
  src="../../../../${f%.olean}.lean"; [ -f "$src" ] || [ "$f" = ConjureDSPLib.olean ] || echo "$f"; done)"
[ -z "$stale" ] || fail "compiled files with no source (delete them from proofs/.lake/build): $stale"
( cd proofs && lake env leanchecker ConjureDSPLib ) || fail "leanchecker rejected the proofs"
echo "Every ConjureDSPLib module: OK"

printf '\nAll proofs built and checked.\n'
