/-
Axiom check for every declaration in the `ConjureDSPLib` modules, run by `scripts/prove.sh` with
`lake env lean --run AxiomCheck.lean` after `lake build`.

It fails (exit code 1) if any declaration depends on an axiom other than the three standard ones
(`propext`, `Classical.choice`, `Quot.sound`). That includes `sorryAx`, which is what `sorry`
leaves behind, and any `axiom` declared in this project.
-/
import Lean
open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ConjureDSPLib }] {} (trustLevel := 1024)
  let ours := fun (n : Name) =>
    match env.getModuleIdxFor? n with
    | some idx => (`ConjureDSPLib).isPrefixOf (env.header.moduleNames[idx.toNat]!)
    | none => false
  let names := env.constants.toList.filterMap fun (n, _) =>
    if ours n && !n.isInternal then some n else none
  let mut bad : Array (Name × Name) := #[]
  for n in names do
    let (axs, _) ← (collectAxioms n : CoreM _).toIO
      { fileName := "AxiomCheck", fileMap := default } { env }
    for a in axs do
      unless allowed.contains a do bad := bad.push (n, a)
  IO.println s!"Axiom check: {names.length} declarations in ConjureDSPLib modules."
  if bad.isEmpty then
    IO.println "OK: only propext, Classical.choice and Quot.sound are used."
    return 0
  for (n, a) in bad do
    IO.eprintln s!"FAIL: {n} depends on {a}"
  return 1
