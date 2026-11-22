/-
Axiom check for the proofs, run by `scripts/prove.sh` with `lake env lean --run AxiomCheck.lean`
after `lake build`.

It imports every module file under `ConjureDSPLib/` (not only those the root file imports) and
looks at every declaration they contain, private and compiler-generated ones included. It fails
(exit code 1) if:
- a module file under `ConjureDSPLib/` is not imported by the root file `ConjureDSPLib.lean`;
- any declaration is itself an `axiom`;
- any declaration depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`.
  That includes `sorryAx` (what `sorry` leaves behind) and the axioms `native_decide` creates;
- the statement (type) of a public theorem outside the generated `ConjureDSPLib.Code` mentions
  a NaN constant (`Float.nan`, `Float32.nan` and their models) or a helper of Aeneas's float
  model that gives a NaN's bits or sign (`core.f64.bitsOf`, `signBit`, `copysignBits` and the
  `f32` ones). The model has a single NaN, so a statement about NaN bits or signs could
  disagree with Rust. `Float.toBits` and `Float32.toBits` are allowed: theorems use them for
  `-0`, whose bits the model and Rust agree on. Proofs and definitions are not checked.

It trusts the compiled `.olean` files. `scripts/prove.sh` also replays every module through
Lean's kernel with `leanchecker`, which catches proofs that skipped the kernel.
-/
import Lean
open Lean

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Constants that public theorem statements must not mention (see the header). -/
def nanConsts : List Name :=
  [`Float.nan, `Float32.nan, `Float.Model.nan, `Float32.Model.nan,
   `Aeneas.Std.core.f64.bitsOf, `Aeneas.Std.core.f64.signBit, `Aeneas.Std.core.f64.copysignBits,
   `Aeneas.Std.core.f32.bitsOf, `Aeneas.Std.core.f32.signBit, `Aeneas.Std.core.f32.copysignBits]

/-- Module names of every `.lean` file under `dir`, e.g. `ConjureDSPLib.OnePole.SpecF64`. -/
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
  -- A misspelt name would make the statement check pass silently.
  for c in nanConsts do
    unless env.contains c do
      IO.eprintln s!"FAIL: {c} (listed in nanConsts) does not exist"
      failed := true
  let mut count := 0
  let mut stmts := 0
  for (n, ci) in env.constants.toList do
    let some m := modOf n | continue
    unless all.contains m do continue
    count := count + 1
    if ci matches .axiomInfo _ then
      IO.eprintln s!"FAIL: {n} (in {m}) is an axiom"
      failed := true
    if ci matches .thmInfo _ && !isPrivateName n && !n.isInternal
        && !(`ConjureDSPLib.Code).isPrefixOf m then
      stmts := stmts + 1
      for c in ci.type.getUsedConstants do
        if nanConsts.contains c then
          IO.eprintln s!"FAIL: the statement of {n} (in {m}) mentions {c}"
          failed := true
    let (axs, _) ← (collectAxioms n : CoreM _).toIO
      { fileName := "AxiomCheck", fileMap := default } { env }
    for a in axs do
      unless allowed.contains a do
        IO.eprintln s!"FAIL: {n} (in {m}) depends on {a}"
        failed := true
  IO.println s!"Axiom check: {count} declarations in {all.size} modules."
  IO.println s!"NaN check: {stmts} public theorem statements."
  if failed then return 1
  IO.println "OK: only propext, Classical.choice and Quot.sound are used."
  IO.println "OK: no public theorem statement mentions a NaN constant or a NaN-bits helper."
  return 0
