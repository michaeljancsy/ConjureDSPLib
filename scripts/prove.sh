#!/usr/bin/env bash
# Build and check the Lean proofs about this crate, in order:
#   1. Charon: Rust -> LLBC
#   2. Aeneas: LLBC -> Lean (proofs/ConjureDSPLib/Code/), which must match the last commit
#   3. lake build
#   4. axiom check (proofs/AxiomCheck.lean): every module file built; only propext,
#      Classical.choice and Quot.sound; no sorry; no axioms of our own
#   5. kernel replay: leanchecker re-checks every declaration of every module
#
# Tool locations (defaults in brackets):
#   AENEAS_DIR     clean checkout of michaeljancsy/aeneas at the commit in proofs/PINS, with the
#                  Aeneas binary built from it and Charon in its charon/ folder
#                  [~/Projects/ConjureDSP/toolchains/aeneas-<first 8 characters of the commit>]
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
got="$("$AENEAS_BIN" -version)"
case "$got" in
  *-dirty*) fail "the Aeneas binary was built from a modified tree: $got" ;;
  *"-g${AENEAS_COMMIT:0:8}"*) ;;
  *) fail "the Aeneas binary reports '$got', not commit ${AENEAS_COMMIT:0:8}; rebuild it" ;;
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
sys.exit(1 if bad else 0)
PY
  link "$LAKE_PACKAGES" proofs/.lake/packages
  link "$LAKE_PACKAGES" "$AENEAS_DIR/backends/lean/.lake/packages"
fi

step "1. Charon"
mkdir -p target
"$CHARON_BIN" cargo --preset=aeneas --dest-file target/conjure_dsp_lib.llbc

step "2. Aeneas"
"$AENEAS_BIN" -backend lean target/conjure_dsp_lib.llbc -dest proofs/ConjureDSPLib/Code
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
modules="$(cd proofs && find ConjureDSPLib -name '*.lean' | sed 's/\.lean$//; s#/#.#g' | sort)"
for m in ConjureDSPLib $modules; do
  ( cd proofs && lake env leanchecker "$m" ) || fail "leanchecker rejected $m"
  echo "$m: OK"
done

printf '\nAll proofs built and checked.\n'
