/-
Axiom check for the proofs, run by `scripts/prove.sh` with `lake env lean --run AxiomCheck.lean`
after `lake build`.

It imports every module file under `ConjureDSPLib/` (not only those the root file imports) and
looks at every declaration they contain, private and compiler-generated ones included. It fails
(exit code 1) if:
- a module file under `ConjureDSPLib/` is not imported by the root file `ConjureDSPLib.lean`;
- any declaration is itself an `axiom`;
- any declaration depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
  That includes `sorryAx` (what `sorry` leaves behind) and the axioms `native_decide` creates.

It trusts the compiled `.olean` files. `scripts/prove.sh` also replays every module through
Lean's kernel with `leanchecker`, which catches proofs that skipped the kernel.
-/
import Lean
open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Module names of every `.lean` file under `dir`, e.g. `ConjureDSPLib.OnePole.Spec`. -/
partial def modulesUnder (dir : System.FilePath) (pre : Name) : IO (Array Name) := do
  let mut out := #[]
  for e in (← dir.readDir).qsort (·.fileName < ·.fileName) do
    if (← e.path.isDir) then
      out := out ++ (← modulesUnder e.path (pre.str e.fileName))
    else if e.path.extension == some "lean" then
      out := out.push (pre.str (e.path.fileStem.getD e.fileName))
  return out

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods ← modulesUnder "ConjureDSPLib" `ConjureDSPLib
  let all := #[`ConjureDSPLib] ++ mods
  let mut failed := false

  -- Every module file must be reachable from the root file, or `lake build` skips it.
  let rootEnv ← importModules #[{ module := `ConjureDSPLib }] {} (trustLevel := 1024)
  for m in mods do
    unless rootEnv.header.moduleNames.contains m do
      IO.eprintln s!"FAIL: {m} is not imported by ConjureDSPLib.lean, so lake build skips it"
      failed := true

  let env ← importModules (all.map ({ module := · })) {} (trustLevel := 1024)
  let modOf := fun (n : Name) =>
    (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  let mut count := 0
  for (n, ci) in env.constants.toList do
    let some m := modOf n | continue
    unless all.contains m do continue
    count := count + 1
    if ci matches .axiomInfo _ then
      IO.eprintln s!"FAIL: {n} (in {m}) is an axiom"
      failed := true
    let (axs, _) ← (collectAxioms n : CoreM _).toIO
      { fileName := "AxiomCheck", fileMap := default } { env }
    for a in axs do
      unless allowed.contains a do
        IO.eprintln s!"FAIL: {n} (in {m}) depends on {a}"
        failed := true
  IO.println s!"Axiom check: {count} declarations in {all.size} modules."
  if failed then return 1
  IO.println "OK: only propext, Classical.choice and Quot.sound are used."
  return 0
