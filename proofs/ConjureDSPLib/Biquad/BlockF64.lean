module

public import ConjureDSPLib.Biquad.SpecF64
public import ConjureDSPLib.Biquad.Block
public import ConjureDSPLib.Biquad.Contraction
public import ConjureDSPLib.FloatFacts

/-!
# The biquad filter in f64 over a whole block

`process_f64_block_error`: when the Rust `process_f64` filters a block, given a `Contraction`
for the real values of the stored coefficients (see `Block.lean`), finite coefficients and
starting state, inputs at most `M`, no overflow and `cInf·K·κ·β < 1 − ρ`, every output and the
final state are within distances of the exact real-number filter `filt_real` that depend on the
coefficients, the `Contraction`, `M` and the starting state but not on the block length. A
`Contraction` for biquads with complex poles inside the unit circle, and one for distinct real
poles inside it, are in `Biquad/Contraction.lean`.

Each step rounds nine times (`tdf2_f64`); `tdf2_f64_localErr` bounds the effect of those
roundings on the step's output and new state by `α + β·Sb` when the state is at most `Sb` in
size and the input at most `M`, and no intermediate result overflows, with
`α = localErrBase_f64` and `β = localErrSlope_f64`. `block_error_real` in `Block.lean` turns that
into the whole-block bound.

`process_f64_block_error_of_inputs` replaces the no-overflow condition by finite inputs and
`stepValueBound_f64 c C M s ≤ maxFinite_f64`: `stepFinite_f64` shows that a step whose state is
within `Sb` and input within `M` does not overflow when `stepValueBound` at that `Sb` is at most
the largest finite value, and `noOverflow_f64_of_inputs` carries the state bound through the
block with `block_step`.

`block_bound_of_rat_f64` and `block_bounds_of_rat_f64` turn rational bounds on `ω` and `√a2` into
bounds on the constants of these theorems for `complexPolesContraction`, and
`realPolesContraction_block_bounds_of_rat_f64` does the same from rational bounds on
`d = √(a1² − 4·a2)` for `realPolesContraction`; the last sections apply them to RBJ-cookbook
low-pass coefficients at chosen cutoffs (the biquad table and cutoff facts in `proofs/README.md`).
No lower bounds, and no failures of the condition `cInf·K·κ·β < 1 − ρ`, are claimed in f64, so
only the upper-bound lemmas are here (`BlockF32.lean` has the others).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.biquad

/-- The exact real values of the five binary64 coefficients. -/
noncomputable def realCoeffs_f64 (c : CoeffsF64) : CoeffsReal where
  b0 := real_f64 c.b0
  b1 := real_f64 c.b1
  b2 := real_f64 c.b2
  a1 := real_f64 c.a1
  a2 := real_f64 c.a2

/-- The exact real values of the two binary64 state values. -/
noncomputable def realState_f64 (s : StateF64) : ℝ × ℝ := (real_f64 s.s1, real_f64 s.s2)

/-- All five coefficients are finite. -/
def CoeffsFinite_f64 (c : CoeffsF64) : Prop :=
  c.b0.isFinite = true ∧ c.b1.isFinite = true ∧ c.b2.isFinite = true ∧
    c.a1.isFinite = true ∧ c.a2.isFinite = true

/-- One step of `tdf2_f64` from state `s` on input `x` does not overflow: `x` and every
intermediate result are finite. With `y = b0 * x + s1` the output, these are `b0 * x`, `y`,
`b1 * x`, `a1 * y`, `b1 * x - a1 * y`, the new `s1 = b1 * x - a1 * y + s2`, `b2 * x`, `a2 * y`
and the new `s2 = b2 * x - a2 * y`. -/
def StepFinite_f64 (c : CoeffsF64) (s : StateF64) (x : Float) : Prop :=
  let y := c.b0 * x + s.s1
  x.isFinite = true ∧ (c.b0 * x).isFinite = true ∧ y.isFinite = true ∧
    (c.b1 * x).isFinite = true ∧ (c.a1 * y).isFinite = true ∧
    (c.b1 * x - c.a1 * y).isFinite = true ∧ (c.b1 * x - c.a1 * y + s.s2).isFinite = true ∧
    (c.b2 * x).isFinite = true ∧ (c.a2 * y).isFinite = true ∧
    (c.b2 * x - c.a2 * y).isFinite = true

/-- No step overflows: running the filter from state `s` over the inputs, every step is
`StepFinite_f64`. -/
def NoOverflow_f64 (c : CoeffsF64) : StateF64 → List Float → Prop
  | _, [] => True
  | s, x :: xs => StepFinite_f64 c s x ∧ NoOverflow_f64 c (tdf2_f64 c s x).2 xs

/-- `α` for binary64: `localErrBase` with binary64's `u` and `η`, for inputs at most `M`. -/
noncomputable abbrev localErrBase_f64 (c : CoeffsF64) (M : ℝ) : ℝ :=
  localErrBase (realCoeffs_f64 c) unitRoundoff_f64 underflowErr_f64 M

/-- `β` for binary64: `localErrSlope` with binary64's `u`. -/
noncomputable abbrev localErrSlope_f64 (c : CoeffsF64) : ℝ :=
  localErrSlope (realCoeffs_f64 c) unitRoundoff_f64

/-- `L` for binary64: `localErrBound` with `α = localErrBase_f64 c M`, `β = localErrSlope_f64 c`,
the real values of the stored coefficients and the real value of the stored starting state `s`. -/
noncomputable abbrev localErrBound_f64 (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (M : ℝ) (s : StateF64) : ℝ :=
  localErrBound (realCoeffs_f64 c) C M (localErrBase_f64 c M) (localErrSlope_f64 c)
    (realState_f64 s)

/-- `Ê` for binary64: `stateErrBound` with `α = localErrBase_f64 c M`, `β = localErrSlope_f64 c`,
the real values of the stored coefficients and the real value of the stored starting state `s`. -/
noncomputable abbrev stateErrBound_f64 (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (M : ℝ) (s : StateF64) : ℝ :=
  stateErrBound (realCoeffs_f64 c) C M (localErrBase_f64 c M) (localErrSlope_f64 c)
    (realState_f64 s)

/-- `Sb` for binary64: `computedStateBound` with `α = localErrBase_f64 c M`,
`β = localErrSlope_f64 c`, the real values of the stored coefficients and the real value of the
stored starting state `s`. -/
noncomputable abbrev computedStateBound_f64 (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (M : ℝ) (s : StateF64) : ℝ :=
  computedStateBound (realCoeffs_f64 c) C M (localErrBase_f64 c M) (localErrSlope_f64 c)
    (realState_f64 s)

/-- `V` for binary64: `stepValueBound` with binary64's `η`, the real values of the stored
coefficients, inputs at most `M`, and `Sb = computedStateBound_f64 c C M s`. -/
noncomputable abbrev stepValueBound_f64 (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (M : ℝ) (s : StateF64) : ℝ :=
  stepValueBound (realCoeffs_f64 c) underflowErr_f64 M (computedStateBound_f64 c C M s)

/-- **One step's roundings in binary64.** If the coefficients and state are finite, the step
does not overflow, both state values are at most `Sb` in size and the input at most `M`, then
the output and the two new state values of `tdf2_f64` are each within
`α + β·Sb` (`localErrBase_f64`, `localErrSlope_f64`) of the exact step from the same state and
the computed output: `B0·X + S1`, `B1·X - A1·Y + S2` and `B2·X - A2·Y`, where capitals are exact
real values and `Y` is the computed output's. -/
theorem tdf2_f64_localErr (c : CoeffsF64) (s : StateF64) (x : Float) (Sb M : ℝ)
    (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hstep : StepFinite_f64 c s x) (hS1 : |real_f64 s.s1| ≤ Sb) (hS2 : |real_f64 s.s2| ≤ Sb)
    (hX : |real_f64 x| ≤ M) :
    let cr := realCoeffs_f64 c
    let L := localErrBase_f64 c M + localErrSlope_f64 c * Sb
    let Y := real_f64 (tdf2_f64 c s x).1
    |Y - (cr.b0 * real_f64 x + real_f64 s.s1)| ≤ L ∧
      |real_f64 (tdf2_f64 c s x).2.s1 - (cr.b1 * real_f64 x - cr.a1 * Y + real_f64 s.s2)| ≤ L ∧
      |real_f64 (tdf2_f64 c s x).2.s2 - (cr.b2 * real_f64 x - cr.a2 * Y)| ≤ L := by
  obtain ⟨hb0, hb1, hb2, ha1, ha2⟩ := hc
  obtain ⟨hx, hp0, hy, hp1, hq1, hd1, ht1, hp2, hq2, ht2⟩ := hstep
  exact step_localErr (realCoeffs_f64 c) (Model.unitRoundoffAt_pos _).le
    (Model.unitRoundoffAt_lt_one _).le (Model.underflowErrorAt_pos _).le hX hS1 hS2
    (abs_real_mul_sub_le_f64 _ _ hb0 hx hp0)
    (abs_real_add_sub_le_f64 _ _ hp0 hs1 hy)
    (abs_real_mul_sub_le_f64 _ _ hb1 hx hp1)
    (abs_real_mul_sub_le_f64 _ _ ha1 hy hq1)
    (abs_real_sub_sub_le_f64 _ _ hp1 hq1 hd1)
    (abs_real_add_sub_le_f64 _ _ hd1 hs2 ht1)
    (abs_real_mul_sub_le_f64 _ _ hb2 hx hp2)
    (abs_real_mul_sub_le_f64 _ _ ha2 hy hq2)
    (abs_real_sub_sub_le_f64 _ _ hp2 hq2 ht2)

/-- If the coefficients and starting state are finite and no step overflows (`NoOverflow_f64`),
then for every `Sb` and `M`, the run of `filt_f64` (as real values) satisfies `WithinLocalErr`
with `L = α + β·Sb` (`localErrBase_f64 c M`, `localErrSlope_f64 c`): every step whose state is
within `Sb` and its input within `M` rounds within `L`. -/
theorem filt_f64_withinLocalErr (c : CoeffsF64) (hc : CoeffsFinite_f64 c) (Sb M : ℝ) :
    ∀ (xs : List Float) (s : StateF64), s.s1.isFinite = true → s.s2.isFinite = true →
      NoOverflow_f64 c s xs →
      WithinLocalErr (realCoeffs_f64 c) Sb M (localErrBase_f64 c M + localErrSlope_f64 c * Sb)
        (realState_f64 s) (xs.map real_f64) (realState_f64 (filt_f64 c s xs).1)
        ((filt_f64 c s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _; simp [filt_f64, WithinLocalErr, realState_f64]
  | cons x xs ih =>
    intro s hs1 hs2 hno
    obtain ⟨hstep, hrest⟩ := hno
    have ht1 : (tdf2_f64 c s x).2.s1.isFinite = true := hstep.2.2.2.2.2.2.1
    have ht2 : (tdf2_f64 c s x).2.s2.isFinite = true := hstep.2.2.2.2.2.2.2.2.2
    simp only [filt_f64, List.map_cons, realState_f64, WithinLocalErr]
    exact ⟨_, _, fun h1 h2 hX => tdf2_f64_localErr c s x Sb M hc hs1 hs2 hstep h1 h2 hX,
      ih _ ht1 ht2 hrest⟩

/-- **Whole-block error of the f64 biquad.** Let `C` be a `Contraction` for the real values of the
stored coefficients (`realCoeffs_f64 c`), `0 ≤ M`, every input's real value at most `M` in size,
with `β = localErrSlope_f64 c` and `κ = roundGain (realCoeffs_f64 c)`. If the coefficients and
the starting state are finite, no step overflows (`NoOverflow_f64`), and `cInf·K·κ·β < 1 − ρ`, then
the outputs of `filt_f64` and of `filt_real` (run on the real values of the inputs from
`realState_f64 s`) have the same length, every output's real value is within `cInf·Ê + L` of the
corresponding exact output, and each final state value's real value within `cInf·Ê` of the
exact one, where `Ê = stateErrBound_f64 c C M s` and `L = localErrBound_f64 c C M s`. -/
theorem filt_f64_block_error (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c)) (s : StateF64)
    (xs : List Float) (M : ℝ) (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true)
    (hs2 : s.s2.isFinite = true) (hno : NoOverflow_f64 c s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f64 x| ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ) :
    let Ê := stateErrBound_f64 c C M s
    let L := localErrBound_f64 c C M s
    let F := filt_real (realCoeffs_f64 c) (realState_f64 s) (xs.map real_f64)
    List.Forall₂ (fun y e => |real_f64 y - e| ≤ C.cInf * Ê + L) (filt_f64 c s xs).2 F.2 ∧
      |real_f64 (filt_f64 c s xs).1.s1 - F.1.1| ≤ C.cInf * Ê ∧
      |real_f64 (filt_f64 c s xs).1.s2 - F.1.2| ≤ C.cInf * Ê := by
  intro Ê L F
  have h := block_error_real (realCoeffs_f64 c) C M _ _ hM0
    (localErrBase_nonneg _ (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0)
    (localErrSlope_nonneg _ (Model.unitRoundoffAt_pos _).le) hsmall (xs.map real_f64)
    (realState_f64 s) _ _ (by simpa using hM)
    (filt_f64_withinLocalErr c hc _ M xs s hs1 hs2 hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust biquad `process_f64`.** Under the conditions of
`filt_f64_block_error` (with `state` as the starting state and the buffer as the inputs),
`process_f64` never fails, the buffer it returns has one sample per exact output, each sample's
real value is within `cInf·Ê + L` of the corresponding output of `filt_real` (run on the real
values of the inputs from `realState_f64 state`), and each value of the state it leaves is within
`cInf·Ê` of the exact final state's, where `Ê = stateErrBound_f64 c C M state` and
`L = localErrBound_f64 c C M state`. -/
theorem process_f64_block_error (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hno : NoOverflow_f64 c state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ) :
    let Ê := stateErrBound_f64 c C M state
    let L := localErrBound_f64 c C M state
    let F := filt_real (realCoeffs_f64 c) (realState_f64 state) (buf.val.map real_f64)
    process_f64 c state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f64 y - e| ≤ C.cInf * Ê + L) r.2.val F.2 ∧
        |real_f64 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f64 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê L F
  have hblock := filt_f64_block_error c C state buf.val M hc hs1 hs2 hno hM0 hM hsmall
  apply WP.spec_mono (process_f64_spec c state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **One step does not overflow.** If the coefficients, both state values and the input are
finite, both state values are at most `Sb` in size, the input at most `M` in size, and
`V = stepValueBound (realCoeffs_f64 c) η M Sb` (with binary64's `η`) is at most the largest
finite binary64 value, then none of the step's nine operations overflows (`StepFinite_f64`). -/
theorem stepFinite_f64 (c : CoeffsF64) (s : StateF64) (x : Float) (Sb M : ℝ)
    (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hx : x.isFinite = true) (hS1 : |real_f64 s.s1| ≤ Sb) (hS2 : |real_f64 s.s2| ≤ Sb)
    (hX : |real_f64 x| ≤ M)
    (hcap : stepValueBound (realCoeffs_f64 c) underflowErr_f64 M Sb ≤ maxFinite_f64) :
    StepFinite_f64 c s x := by
  obtain ⟨hb0, hb1, hb2, ha1, ha2⟩ := hc
  obtain ⟨v0, v1, v2, rest⟩ := step_values_le (realCoeffs_f64 c) (u := unitRoundoff_f64)
    (P0 := real_f64 (c.b0 * x)) (Y := real_f64 (c.b0 * x + s.s1)) (P1 := real_f64 (c.b1 * x))
    (Q1 := real_f64 (c.a1 * (c.b0 * x + s.s1)))
    (D1 := real_f64 (c.b1 * x - c.a1 * (c.b0 * x + s.s1))) (P2 := real_f64 (c.b2 * x))
    (Q2 := real_f64 (c.a2 * (c.b0 * x + s.s1)))
    (Model.unitRoundoffAt_pos _).le (Model.unitRoundoffAt_lt_one _).le
    (Model.underflowErrorAt_pos _).le hX hS1 hS2
  -- Each operation in turn: its exact value is at most `V`, so it is finite, so its rounding is
  -- within `u·|e| + η`, which bounds the next operation's exact value.
  have hp0 := isFinite_mul_f64 _ _ hb0 hx (v0.trans hcap)
  obtain ⟨vy, rest⟩ := rest (abs_real_mul_sub_le_f64 _ _ hb0 hx hp0)
  have hy := isFinite_add_f64 _ _ hp0 hs1 (vy.trans hcap)
  obtain ⟨vq1, vq2, r1, r2⟩ := rest (abs_real_add_sub_le_f64 _ _ hp0 hs1 hy)
  have hp1 := isFinite_mul_f64 _ _ hb1 hx (v1.trans hcap)
  have hq1 := isFinite_mul_f64 _ _ ha1 hy (vq1.trans hcap)
  obtain ⟨vd1, r1⟩ := r1 (abs_real_mul_sub_le_f64 _ _ hb1 hx hp1)
    (abs_real_mul_sub_le_f64 _ _ ha1 hy hq1)
  have hd1 := isFinite_sub_f64 _ _ hp1 hq1 (vd1.trans hcap)
  have ht1 := isFinite_add_f64 _ _ hd1 hs2
    ((r1 (abs_real_sub_sub_le_f64 _ _ hp1 hq1 hd1)).trans hcap)
  have hp2 := isFinite_mul_f64 _ _ hb2 hx (v2.trans hcap)
  have hq2 := isFinite_mul_f64 _ _ ha2 hy (vq2.trans hcap)
  have ht2 := isFinite_sub_f64 _ _ hp2 hq2
    ((r2 (abs_real_mul_sub_le_f64 _ _ hb2 hx hp2) (abs_real_mul_sub_le_f64 _ _ ha2 hy hq2)).trans
      hcap)
  exact ⟨hx, hp0, hy, hp1, hq1, hd1, ht1, hp2, hq2, ht2⟩

/-- **No overflow, from the inputs alone.** Let `C` be a `Contraction` for the real values of the
stored coefficients, with `G = inputGain` and `κ = roundGain` of those values, and
`α = localErrBase_f64 c M`, `β = localErrSlope_f64 c`. Suppose the coefficients are finite, and
the numbers `Sb`, `R`, `Ê` satisfy `ρ·R + K·G·M ≤ R`, `ρ·Ê + K·κ·(α + β·Sb) ≤ Ê`,
`cInf·(R + Ê) ≤ Sb`, and
`V = stepValueBound` (binary64's `η`, inputs at most `M`, state values at most `Sb`) is at most
the largest finite binary64 value. Start from a state `s` with both values finite, and a real
state `r` that measures at most `R`, with `s`'s real value minus `r` measuring at most `Ê` (for
the filter's own start, `r` is `s`'s real value). If every input is finite and at most `M` in
size, then no step overflows (`NoOverflow_f64`). -/
theorem noOverflow_f64_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (hc : CoeffsFinite_f64 c) (Sb M R Ê : ℝ)
    (hR : C.ρ * R + C.K * inputGain (realCoeffs_f64 c) * M ≤ R)
    (hE : C.ρ * Ê + C.K * ((localErrBase_f64 c M + localErrSlope_f64 c * Sb) *
        roundGain (realCoeffs_f64 c)) ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb)
    (hcap : stepValueBound (realCoeffs_f64 c) underflowErr_f64 M Sb ≤ maxFinite_f64) :
    ∀ (xs : List Float) (s : StateF64) (r : ℝ × ℝ), s.s1.isFinite = true →
      s.s2.isFinite = true → (∀ x ∈ xs, x.isFinite = true ∧ |real_f64 x| ≤ M) →
      C.N r.1 r.2 ≤ R → C.N (real_f64 s.s1 - r.1) (real_f64 s.s2 - r.2) ≤ Ê →
      NoOverflow_f64 c s xs := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hs1 hs2 hin hr he
    obtain ⟨hx, hX⟩ := hin x (by simp)
    -- The computed state is within `Sb`, so the step does not overflow.
    obtain ⟨hS1, hS2⟩ := block_state_le _ C hS hr he
    have hstep := stepFinite_f64 c s x Sb M hc hs1 hs2 hx hS1 hS2 hX hcap
    -- Its roundings are within `L`, so both bounds carry on to the next step.
    obtain ⟨hdy, hd₁, hd₂⟩ := tdf2_f64_localErr c s x Sb M hc hs1 hs2 hstep hS1 hS2 hX
    obtain ⟨-, hr', he'⟩ := block_step _ C hR hE hX hr he hdy hd₁ hd₂
    let cr := realCoeffs_f64 c
    exact ⟨hstep, ih _ (cr.b1 * real_f64 x - cr.a1 * (cr.b0 * real_f64 x + r.1) + r.2,
      cr.b2 * real_f64 x - cr.a2 * (cr.b0 * real_f64 x + r.1)) hstep.2.2.2.2.2.2.1
      hstep.2.2.2.2.2.2.2.2.2 (fun z hz => hin z (List.mem_cons_of_mem _ hz)) hr' he'⟩

/-- **Whole-block error of the f64 biquad, with conditions on the inputs only.** Let `C` be a
`Contraction` for the real values of the stored coefficients (`realCoeffs_f64 c`), `0 ≤ M`, with
`β = localErrSlope_f64 c` and `κ = roundGain (realCoeffs_f64 c)`. If the coefficients, the
starting state and every input are finite, every input's real value is at most `M` in size,
`cInf·K·κ·β < 1 − ρ`, and `stepValueBound_f64 c C M s` is at most the largest finite binary64
value (about 1.8 × 10³⁰⁸), then no step overflows (`NoOverflow_f64`), and the conclusion of
`filt_f64_block_error` holds: the outputs of `filt_f64` and of `filt_real` (run on the real
values of the inputs from `realState_f64 s`) have the same length, every output's real value is
within `cInf·Ê + L` of the corresponding exact output, and each final state value's real value
within `cInf·Ê` of the exact one, where `Ê = stateErrBound_f64 c C M s` and
`L = localErrBound_f64 c C M s`. -/
theorem filt_f64_block_error_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (s : StateF64) (xs : List Float) (M : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hin : ∀ x ∈ xs, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ)
    (hcap : stepValueBound_f64 c C M s ≤ maxFinite_f64) :
    let Ê := stateErrBound_f64 c C M s
    let L := localErrBound_f64 c C M s
    let F := filt_real (realCoeffs_f64 c) (realState_f64 s) (xs.map real_f64)
    NoOverflow_f64 c s xs ∧
      List.Forall₂ (fun y e => |real_f64 y - e| ≤ C.cInf * Ê + L) (filt_f64 c s xs).2 F.2 ∧
      |real_f64 (filt_f64 c s xs).1.s1 - F.1.1| ≤ C.cInf * Ê ∧
      |real_f64 (filt_f64 c s xs).1.s2 - F.1.2| ≤ C.cInf * Ê := by
  intro Ê L F
  obtain ⟨hR, hE, hS, hr, he⟩ := block_constants (realCoeffs_f64 c) C M _ _ (realState_f64 s)
    hM0
    (localErrBase_nonneg _ (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0)
    (localErrSlope_nonneg _ (Model.unitRoundoffAt_pos _).le) hsmall
  have hno := noOverflow_f64_of_inputs c C hc _ M _ _ hR hE hS hcap xs s (realState_f64 s)
    hs1 hs2 hin hr he
  exact ⟨hno, filt_f64_block_error c C s xs M hc hs1 hs2 hno hM0 (fun x hx => (hin x hx).2)
    hsmall⟩

/-- **Whole-block error of the Rust biquad `process_f64`, with conditions on the inputs only.**
Under the conditions of `filt_f64_block_error_of_inputs` (with `state` as the starting state and
the buffer as the inputs: the coefficients, `state` and every sample finite, every sample's real
value at most `M` in size, `0 ≤ M`, `cInf·K·κ·β < 1 − ρ`, and `stepValueBound_f64 c C M state`
at most the largest finite binary64 value), no step overflows (`NoOverflow_f64`), `process_f64`
never fails, the buffer it returns has one sample per exact output, each sample's real value is
within `cInf·Ê + L` of the corresponding output of `filt_real` (run on the real values of the inputs
from `realState_f64 state`), and each value of the state it leaves is within `cInf·Ê` of the
exact final state's, where `Ê = stateErrBound_f64 c C M state` and
`L = localErrBound_f64 c C M state`. -/
theorem process_f64_block_error_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ)
    (hcap : stepValueBound_f64 c C M state ≤ maxFinite_f64) :
    let Ê := stateErrBound_f64 c C M state
    let L := localErrBound_f64 c C M state
    let F := filt_real (realCoeffs_f64 c) (realState_f64 state) (buf.val.map real_f64)
    NoOverflow_f64 c state buf.val ∧
      process_f64 c state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f64 y - e| ≤ C.cInf * Ê + L) r.2.val F.2 ∧
          |real_f64 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f64 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê L F
  have hno := (filt_f64_block_error_of_inputs c C state buf.val M hc hs1 hs2 hin hM0 hsmall
    hcap).1
  exact ⟨hno, process_f64_block_error c C state buf M hc hs1 hs2 hno hM0
    (fun x hx => (hin x hx).2) hsmall⟩

/-- **The f64 output error bound with `complexPolesContraction`, from rational numbers.** For
stored coefficients with real values `q`, a start of value `(0, 0)` and `M = 1` (inputs at most 1
in size): if `q` has complex poles inside the unit circle (`q.a1² < 4·q.a2`, `q.a2 < 1`),
`0 < ωl`, `0 ≤ ωu`, `ωl² ≤ q.a2 - q.a1²/4 ≤ ωu²`, `0 ≤ ρu`, `q.a2 ≤ ρu²`, and, with
`ci = (1 + |q.a1|/2)/ωl + 1`, `k = ωu + |q.a1|/2 + 1`, `u = 2⁻⁵³`, `η = 2⁻¹⁰⁷⁵`,
`α = localErrBase q u η 1` and `β = localErrSlope q u`: `ci·k·κ·β < 1 − ρu` (`κ = roundGain q`)
and `outErrBoundAt q 1 α β 0 ci k ρu ≤ X`; then for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, and the bound `cInf·Ê + L` on each
output's error is positive and at most `X`. The hypotheses are statements about rational numbers
that `norm_num` checks. -/
theorem block_bound_of_rat_f64 (c : CoeffsF64) (q : CoeffsReal) (hc : realCoeffs_f64 c = q)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) (ωl ωu ρu X : ℝ)
    (h : q.a1 ^ 2 < 4 * q.a2) (h1 : q.a2 < 1) (hωl : 0 < ωl) (hωu : 0 ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ q.a2 - q.a1 ^ 2 / 4) (hωu2 : q.a2 - q.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρu : 0 ≤ ρu) (hρu2 : q.a2 ≤ ρu ^ 2)
    (hsm : ((1 + |q.a1| / 2) / ωl + 1) * (ωu + |q.a1| / 2 + 1) * roundGain q *
      localErrSlope q (2 ^ (-53 : ℤ)) < 1 - ρu)
    (hX : outErrBoundAt q 1 (localErrBase q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1)
      (localErrSlope q (2 ^ (-53 : ℤ))) 0 ((1 + |q.a1| / 2) / ωl + 1) (ωu + |q.a1| / 2 + 1)
      ρu ≤ X) :
    ∃ (h : (realCoeffs_f64 c).a1 ^ 2 < 4 * (realCoeffs_f64 c).a2)
      (h1 : (realCoeffs_f64 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f64 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        0 < C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ X := by
  subst hc
  rw [← unitRoundoff_f64_eq] at hsm hX
  rw [← underflowErr_f64_eq] at hX
  refine ⟨h, h1, ?_⟩
  intro C
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f64)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f64)
  have hα : 0 < localErrBase_f64 c 1 := localErrBase_pos _ hu.le hη zero_le_one
  have hβ : 0 ≤ localErrSlope_f64 c := localErrSlope_nonneg _ hu.le
  have hs0 : complexPoleNorm (realCoeffs_f64 c) (realState_f64 s).1 (realState_f64 s).2 ≤ 0 := by
    rw [hs]; exact (complexPoleNorm_zero _).le
  obtain ⟨hsmall, -, -, hpos, hbd, -⟩ := complexPolesContraction_block_bounds_le
    (realCoeffs_f64 c) h h1 1 (localErrBase_f64 c 1) (localErrSlope_f64 c) underflowErr_f64 0
    ωl ωu ρu (realState_f64 s) zero_le_one hα.le hβ hs0 hωl hωu hωl2 hωu2 hρu hρu2 hsm
  exact ⟨hsmall, hα.trans_le hpos, hbd.trans hX⟩

/-- **The f64 whole-block constants with `complexPolesContraction`, from rational numbers.** Under
the hypotheses of `block_bound_of_rat_f64`, and, with `Sb' = stateBoundAt q 1 α β 0 ci k ρu`,
`Sb' ≤ Sbb` and `stepValueBound q η 1 Sb' ≤ Vb`: its conclusions hold, and also
`Sb = computedStateBound_f64` is at most `Sbb` and `V = stepValueBound_f64` at most `Vb`. -/
theorem block_bounds_of_rat_f64 (c : CoeffsF64) (q : CoeffsReal) (hc : realCoeffs_f64 c = q)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) (ωl ωu ρu X Sbb Vb : ℝ)
    (h : q.a1 ^ 2 < 4 * q.a2) (h1 : q.a2 < 1) (hωl : 0 < ωl) (hωu : 0 ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ q.a2 - q.a1 ^ 2 / 4) (hωu2 : q.a2 - q.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρu : 0 ≤ ρu) (hρu2 : q.a2 ≤ ρu ^ 2)
    (hsm : ((1 + |q.a1| / 2) / ωl + 1) * (ωu + |q.a1| / 2 + 1) * roundGain q *
      localErrSlope q (2 ^ (-53 : ℤ)) < 1 - ρu)
    (hX : outErrBoundAt q 1 (localErrBase q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1)
      (localErrSlope q (2 ^ (-53 : ℤ))) 0 ((1 + |q.a1| / 2) / ωl + 1) (ωu + |q.a1| / 2 + 1)
      ρu ≤ X)
    (hSb : stateBoundAt q 1 (localErrBase q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1)
      (localErrSlope q (2 ^ (-53 : ℤ))) 0 ((1 + |q.a1| / 2) / ωl + 1) (ωu + |q.a1| / 2 + 1) ρu ≤
        Sbb)
    (hV : stepValueBound q (2 ^ (-1075 : ℤ)) 1
      (stateBoundAt q 1 (localErrBase q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1)
        (localErrSlope q (2 ^ (-53 : ℤ))) 0 ((1 + |q.a1| / 2) / ωl + 1) (ωu + |q.a1| / 2 + 1)
        ρu) ≤ Vb) :
    ∃ (h : (realCoeffs_f64 c).a1 ^ 2 < 4 * (realCoeffs_f64 c).a2)
      (h1 : (realCoeffs_f64 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f64 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        0 < C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ X ∧
        computedStateBound_f64 c C 1 s ≤ Sbb ∧ stepValueBound_f64 c C 1 s ≤ Vb := by
  obtain ⟨h', h1', hrest⟩ :=
    block_bound_of_rat_f64 c q hc s hs ωl ωu ρu X h h1 hωl hωu hωl2 hωu2 hρu hρu2 hsm hX
  subst hc
  rw [← unitRoundoff_f64_eq] at hsm hSb hV
  rw [← underflowErr_f64_eq] at hSb hV
  refine ⟨h', h1', ?_⟩
  intro C
  obtain ⟨hsmall, hpos, hX'⟩ := hrest
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f64)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f64)
  have hs0 : complexPoleNorm (realCoeffs_f64 c) (realState_f64 s).1 (realState_f64 s).2 ≤ 0 := by
    rw [hs]; exact (complexPoleNorm_zero _).le
  obtain ⟨-, hSb', -, -, -, hV'⟩ := complexPolesContraction_block_bounds_le
    (realCoeffs_f64 c) h' h1' 1 (localErrBase_f64 c 1) (localErrSlope_f64 c) underflowErr_f64 0
    ωl ωu ρu (realState_f64 s) zero_le_one (localErrBase_pos _ hu.le hη zero_le_one).le
    (localErrSlope_nonneg _ hu.le) hs0 hωl hωu hωl2 hωu2 hρu hρu2 hsm
  exact ⟨hsmall, hpos, hX', hSb'.trans hSb, hV'.trans hV⟩

/-- **The f64 whole-block constants with `realPolesContraction`, from rational numbers.** For
stored coefficients with real values `q`, a start of value `(0, 0)` and `M = 1` (inputs at most 1
in size): if `q` has distinct real poles inside the unit circle (`4·q.a2 < q.a1²`, `q.a2 < 1`,
`|q.a1| < 1 + q.a2`), `0 < dl`, `0 ≤ du`, `dl² ≤ q.a1² - 4·q.a2 ≤ du²`, and, with `ci = 1/dl`,
`k = 2`, `ρu = (|q.a1| + du)/2`, `u = 2⁻⁵³`, `η = 2⁻¹⁰⁷⁵`, `α = localErrBase q u η 1`,
`β = localErrSlope q u` and `Sb' = stateBoundAt q 1 α β 0 ci k ρu`: `ci·k·κ·β < 1 − ρu`
(`κ = roundGain q`), `outErrBoundAt q 1 α β 0 ci k ρu ≤ X`, `Sb' ≤ Sbb` and
`stepValueBound q η 1 Sb' ≤ Vb`; then for `realPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is positive and at most `X`, `Sb = computedStateBound_f64` is at most `Sbb` and
`V = stepValueBound_f64` at most `Vb`. The hypotheses are statements about rational numbers that
`norm_num` checks. -/
theorem realPolesContraction_block_bounds_of_rat_f64 (c : CoeffsF64) (q : CoeffsReal)
    (hc : realCoeffs_f64 c = q) (s : StateF64) (hs : realState_f64 s = (0, 0))
    (dl du X Sbb Vb : ℝ) (h : 4 * q.a2 < q.a1 ^ 2) (h1 : q.a2 < 1) (h2 : |q.a1| < 1 + q.a2)
    (hdl : 0 < dl) (hdu : 0 ≤ du)
    (hdl2 : dl ^ 2 ≤ q.a1 ^ 2 - 4 * q.a2) (hdu2 : q.a1 ^ 2 - 4 * q.a2 ≤ du ^ 2)
    (hsm : 1 / dl * 2 * roundGain q * localErrSlope q (2 ^ (-53 : ℤ)) < 1 - (|q.a1| + du) / 2)
    (hX : outErrBoundAt q 1 (localErrBase q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1)
      (localErrSlope q (2 ^ (-53 : ℤ))) 0 (1 / dl) 2 ((|q.a1| + du) / 2) ≤ X)
    (hSb : stateBoundAt q 1 (localErrBase q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1)
      (localErrSlope q (2 ^ (-53 : ℤ))) 0 (1 / dl) 2 ((|q.a1| + du) / 2) ≤ Sbb)
    (hV : stepValueBound q (2 ^ (-1075 : ℤ)) 1
      (stateBoundAt q 1 (localErrBase q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1)
        (localErrSlope q (2 ^ (-53 : ℤ))) 0 (1 / dl) 2 ((|q.a1| + du) / 2)) ≤ Vb) :
    ∃ (h : 4 * (realCoeffs_f64 c).a2 < (realCoeffs_f64 c).a1 ^ 2)
      (h1 : (realCoeffs_f64 c).a2 < 1) (h2 : |(realCoeffs_f64 c).a1| < 1 + (realCoeffs_f64 c).a2),
      let C := realPolesContraction (realCoeffs_f64 c) h h1 h2
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        0 < C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ X ∧
        computedStateBound_f64 c C 1 s ≤ Sbb ∧ stepValueBound_f64 c C 1 s ≤ Vb := by
  subst hc
  rw [← unitRoundoff_f64_eq] at hsm hX hSb hV
  rw [← underflowErr_f64_eq] at hX hSb hV
  refine ⟨h, h1, h2, ?_⟩
  intro C
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f64)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f64)
  have hα : 0 < localErrBase_f64 c 1 := localErrBase_pos _ hu.le hη zero_le_one
  have hβ : 0 ≤ localErrSlope_f64 c := localErrSlope_nonneg _ hu.le
  have hs0 : realPoleNorm (realCoeffs_f64 c) (realState_f64 s).1 (realState_f64 s).2 ≤ 0 := by
    rw [hs]; exact (realPoleNorm_zero _).le
  obtain ⟨hsmall, hSb', -, hpos, hbd, hV'⟩ := realPolesContraction_block_bounds_le
    (realCoeffs_f64 c) h h1 h2 1 (localErrBase_f64 c 1) (localErrSlope_f64 c) underflowErr_f64 0
    dl du (realState_f64 s) zero_le_one hα.le hβ hs0 hdl hdu hdl2 hdu2 hsm
  exact ⟨hsmall, hα.trans_le hpos, hbd.trans hX, hSb'.trans hSb, hV'.trans hV⟩

/-! ## RBJ low-pass examples, f64

The theorems behind the biquad table and cutoff facts in `proofs/README.md`, for an RBJ-cookbook
Butterworth low-pass with `Q = 0.7071` at 48 kHz. Each `lowPass…_f64` below holds the exact real
values of the stored coefficients at one cutoff `f`. Worked out outside Lean, not proved: they are
what this computation gives, in binary64 in this order: `w = 2π·f/48000`, `α = sin w/(2Q)`,
`a0 = 1 + α`, `b0 = ((1 − cos w)/2)/a0`, `b1 = (1 − cos w)/a0`, `b2 = b0`, `a1 = (−2 cos w)/a0`,
`a2 = (1 − α)/a0`. `cos` and `sin` are outside the model. -/

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at a
100 Hz cutoff. Their bits: `b0 = 0x3F0640A6E580A3DA`, `b1 = 0x3F1640A6E580A3DA`,
`b2 = 0x3F0640A6E580A3DA`, `a1 = 0xBFFFB42D1CBAF721`, `a2 = 0x3FEF69BE43E4464C`. -/
noncomputable def lowPass100Hz_f64 : CoeffsReal where
  b0 := (3131767523398125 / 2 ^ 66)
  b1 := (3131767523398125 / 2 ^ 65)
  b2 := (3131767523398125 / 2 ^ 66)
  a1 := -(8923830126573345 / 2 ^ 52)
  a2 := (2210497545441683 / 2 ^ 51)

-- `norm_num` below evaluates powers such as `2 ^ 1075` and `10 ^ 1999`, above Lean's
-- default limit of 256 on exponents that it evaluates.
set_option exponentiation.threshold 4000 in
/-- **Row 100 Hz of the biquad table in `proofs/README.md`, f64.** For stored binary64 coefficients
whose real values are `lowPass100Hz_f64`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: they have complex poles inside the unit circle, and for `complexPolesContraction` the
condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each
output's error is at most 1.02 × 10⁻⁸, `20·log₁₀` of it (the bound in decibels relative to 1.0) is
at most −159.8, `Sb = computedStateBound_f64` is at most 8.04, `V = stepValueBound_f64` is at most
199, and `V·10³⁵` is at most the largest finite binary64 value. -/
theorem lowPass100Hz_bounds_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass100Hz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (h : (realCoeffs_f64 c).a1 ^ 2 < 4 * (realCoeffs_f64 c).a2)
      (h1 : (realCoeffs_f64 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f64 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ 1.02 * 10 ^ (-8 : ℤ) ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s) ≤
          -159.8 ∧
        computedStateBound_f64 c C 1 s ≤ 8.04 ∧
        stepValueBound_f64 c C 1 s ≤ 199 ∧
        stepValueBound_f64 c C 1 s * 10 ^ 35 ≤ maxFinite_f64 := by
  refine (fun H => ?main) (block_bounds_of_rat_f64 c _ hc s hs
    0.00917076993 0.00917076994 0.9907866109 (1.02 * 10 ^ (-8 : ℤ)) 8.04 (199)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX, hSb, hV⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_, hSb, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 100 799 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f64_eq]; norm_num)
  all_goals bound_norm_num [lowPass100Hz_f64]

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at a
1 kHz cutoff. Their bits: `b0 = 0x3F700A5A64DEF698`, `b1 = 0x3F800A5A64DEF698`,
`b2 = 0x3F700A5A64DEF698`, `a1 = 0xBFFD0BA18C73951A`, `a2 = 0x3FEA9795EC0E21E9`. -/
noncomputable def lowPass1kHz_f64 : CoeffsReal where
  b0 := (564372872879827 / 2 ^ 57)
  b1 := (564372872879827 / 2 ^ 56)
  b2 := (564372872879827 / 2 ^ 57)
  a1 := -(4087781399317133 / 2 ^ 51)
  a2 := (7485019560747497 / 2 ^ 53)

set_option exponentiation.threshold 4000 in
/-- **Row 1 kHz of the biquad table in `proofs/README.md`, f64.** For stored binary64 coefficients
whose real values are `lowPass1kHz_f64`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: they have complex poles inside the unit circle, and for `complexPolesContraction` the
condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each
output's error is at most 1.01 × 10⁻¹⁰, `20·log₁₀` of it (the bound in decibels relative to 1.0) is
at most −199.9, `Sb = computedStateBound_f64` is at most 8.29, `V = stepValueBound_f64` is at most
185, and `V·10³⁵` is at most the largest finite binary64 value. -/
theorem lowPass1kHz_bounds_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass1kHz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (h : (realCoeffs_f64 c).a1 ^ 2 < 4 * (realCoeffs_f64 c).a2)
      (h1 : (realCoeffs_f64 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f64 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ 1.01 * 10 ^ (-10 : ℤ) ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s) ≤
          -199.9 ∧
        computedStateBound_f64 c C 1 s ≤ 8.29 ∧
        stepValueBound_f64 c C 1 s ≤ 185 ∧
        stepValueBound_f64 c C 1 s * 10 ^ 35 ≤ maxFinite_f64 := by
  refine (fun H => ?main) (block_bounds_of_rat_f64 c _ hc s hs
    0.0844963265 0.0844963266 0.9115942659 (1.01 * 10 ^ (-10 : ℤ)) 8.29 (185)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX, hSb, hV⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_, hSb, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 200 1999 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f64_eq]; norm_num)
  all_goals bound_norm_num [lowPass1kHz_f64]

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at a
10 kHz cutoff. Their bits: `b0 = 0x3FCC2F4FD5DBDBFB`, `b1 = 0x3FDC2F4FD5DBDBFB`,
`b2 = 0x3FCC2F4FD5DBDBFB`, `a1 = 0xBFD3AF25CADE37D2`, `a2 = 0x3FC81B8AED2BDF8D`. -/
noncomputable def lowPass10kHz_f64 : CoeffsReal where
  b0 := (7933319284775931 / 2 ^ 55)
  b1 := (7933319284775931 / 2 ^ 54)
  b2 := (7933319284775931 / 2 ^ 55)
  a1 := -(2770300704857065 / 2 ^ 53)
  a2 := (6785682939568013 / 2 ^ 55)

set_option exponentiation.threshold 4000 in
/-- **Row 10 kHz of the biquad table in `proofs/README.md`, f64.** For stored binary64 coefficients
whose real values are `lowPass10kHz_f64`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: they have complex poles inside the unit circle, and for `complexPolesContraction` the
condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each
output's error is at most 3.37 × 10⁻¹³, `20·log₁₀` of it (the bound in decibels relative to 1.0) is
at most −249.4, `Sb = computedStateBound_f64` is at most 7.28, `V = stepValueBound_f64` is at most
41.4, and `V·10³⁵` is at most the largest finite binary64 value. -/
theorem lowPass10kHz_bounds_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass10kHz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (h : (realCoeffs_f64 c).a1 ^ 2 < 4 * (realCoeffs_f64 c).a2)
      (h1 : (realCoeffs_f64 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f64 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ 3.37 * 10 ^ (-13 : ℤ) ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s) ≤
          -249.4 ∧
        computedStateBound_f64 c C 1 s ≤ 7.28 ∧
        stepValueBound_f64 c C 1 s ≤ 41.4 ∧
        stepValueBound_f64 c C 1 s * 10 ^ 35 ≤ maxFinite_f64 := by
  refine (fun H => ?main) (block_bounds_of_rat_f64 c _ hc s hs
    0.405821948 0.405821949 0.433982184 (3.37 * 10 ^ (-13 : ℤ)) 7.28 (41.4)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX, hSb, hV⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_, hSb, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 100 1247 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f64_eq]; norm_num)
  all_goals bound_norm_num [lowPass10kHz_f64]

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at a
1 Hz cutoff. Their bits: `b0 = 0x3E326585D3AF5446`, `b1 = 0x3E426585D3AF5446`,
`b2 = 0x3E326585D3AF5446`, `a1 = 0xBFFFFF3DE2B81CF4`, `a2 = 0x3FEFFE7BCEA2FCD1`. -/
noncomputable def lowPass1Hz_f64 : CoeffsReal where
  b0 := (2589087518665251 / 2 ^ 79)
  b1 := (2589087518665251 / 2 ^ 78)
  b2 := (2589087518665251 / 2 ^ 79)
  a1 := -(2251591384958781 / 2 ^ 50)
  a2 := (9005531979250897 / 2 ^ 53)

set_option exponentiation.threshold 4000 in
/-- **The f64 bound at a 1 Hz cutoff.** For stored binary64 coefficients whose real values are
`lowPass1Hz_f64`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at most 1.02 × 10⁻⁴, and `20·log₁₀` of it (the bound in decibels relative to 1.0) is at
most −79.8. -/
theorem lowPass1Hz_bound_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass1Hz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (h : (realCoeffs_f64 c).a1 ^ 2 < 4 * (realCoeffs_f64 c).a2)
      (h1 : (realCoeffs_f64 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f64 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ 1.02 * 10 ^ (-4 : ℤ) ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s) ≤
          -79.8 := by
  refine (fun H => ?main) (block_bound_of_rat_f64 c _ hc s hs
    0.0000925506062 0.0000925506063 0.9999074433348 (1.02 * 10 ^ (-4 : ℤ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 100 399 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
  all_goals bound_norm_num [lowPass1Hz_f64]

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at a
10 Hz cutoff. Their bits: `b0 = 0x3E9CB880FBD72BC9`, `b1 = 0x3EACB880FBD72BC9`,
`b2 = 0x3E9CB880FBD72BC9`, `a1 = 0xBFFFF86ADB5713E7`, `a2 = 0x3FEFF0D94DBE4749`. -/
noncomputable def lowPass10Hz_f64 : CoeffsReal where
  b0 := (8084163468405705 / 2 ^ 74)
  b1 := (8084163468405705 / 2 ^ 73)
  b2 := (8084163468405705 / 2 ^ 74)
  a1 := -(8998862108169191 / 2 ^ 52)
  a2 := (8990540380915529 / 2 ^ 53)

set_option exponentiation.threshold 4000 in
/-- **The f64 bound at a 10 Hz cutoff.** For stored binary64 coefficients whose real values are
`lowPass10Hz_f64`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at most 1.02 × 10⁻⁶, and `20·log₁₀` of it (the bound in decibels relative to 1.0) is at
most −119.8. -/
theorem lowPass10Hz_bound_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass10Hz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (h : (realCoeffs_f64 c).a1 ^ 2 < 4 * (realCoeffs_f64 c).a2)
      (h1 : (realCoeffs_f64 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f64 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ 1.02 * 10 ^ (-6 : ℤ) ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s) ≤
          -119.8 := by
  refine (fun H => ?main) (block_bound_of_rat_f64 c _ hc s hs
    0.000924735527 0.000924735528 0.999074818756 (1.02 * 10 ^ (-6 : ℤ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 100 599 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
  all_goals bound_norm_num [lowPass10Hz_f64]

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at a
23.8 kHz cutoff. Their bits: `b0 = 0x3FEF69BE3DFA1718`, `b1 = 0x3FFF69BE3DFA1718`,
`b2 = 0x3FEF69BE3DFA1718`, `a1 = 0x3FFF685D7393A96D`, `a2 = 0x3FEED63E10C1098A`. -/
noncomputable def lowPass23800Hz_f64 : CoeffsReal where
  b0 := (1105248760316643 / 2 ^ 50)
  b1 := (1105248760316643 / 2 ^ 49)
  b2 := (1105248760316643 / 2 ^ 50)
  a1 := (8840474858334573 / 2 ^ 52)
  a2 := (4339905679361221 / 2 ^ 52)

set_option exponentiation.threshold 4000 in
/-- **The f64 bound at a 23.8 kHz cutoff.** For stored binary64 coefficients whose real values are
`lowPass23800Hz_f64`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at most 2.73 × 10⁻⁷, and `20·log₁₀` of it (the bound in decibels relative to 1.0) is at
most −131.2. -/
theorem lowPass23800Hz_bound_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass23800Hz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (h : (realCoeffs_f64 c).a1 ^ 2 < 4 * (realCoeffs_f64 c).a2)
      (h1 : (realCoeffs_f64 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f64 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ 2.73 * 10 ^ (-7 : ℤ) ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s) ≤
          -131.2 := by
  refine (fun H => ?main) (block_bound_of_rat_f64 c _ hc s hs
    0.0181733304 0.0181733305 0.9816581086 (2.73 * 10 ^ (-7 : ℤ))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 25 164 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
  all_goals bound_norm_num [lowPass23800Hz_f64]

/-! ## An RBJ low-pass example with real poles, f64

For an RBJ-cookbook low-pass at 48 kHz with `Q < 1/2` the poles are real and distinct.
`lowPass1kHzQ04_f64` holds the exact real values of the stored coefficients at a 1 kHz cutoff with
`Q = 0.4`. Worked out outside Lean, not proved: they are what the computation of the section above
gives with `Q = 0.4` in place of `0.7071`, in binary64. `cos` and `sin` are outside the model. -/

/-- The exact real values of the binary64 coefficients stored for an RBJ low-pass with `Q = 0.4`
at a 1 kHz cutoff. Their bits: `b0 = 0x3F6E2060F5D26D0A`, `b1 = 0x3F7E2060F5D26D0A`,
`b2 = 0x3F6E2060F5D26D0A`, `a1 = 0xBFFB46A4D6E25BDE`, `a2 = 0x3FE705CB319C0170`. -/
noncomputable def lowPass1kHzQ04_f64 : CoeffsReal where
  b0 := (4239925057238661 / 2 ^ 60)
  b1 := (4239925057238661 / 2 ^ 59)
  b2 := (4239925057238661 / 2 ^ 60)
  a1 := -(3838749082463727 / 2 ^ 51)
  a2 := (405018420822039 / 2 ^ 49)

set_option exponentiation.threshold 4000 in
/-- **The f64 bound for a real-pole low-pass (`Q = 0.4`) at 1 kHz.** For stored binary64
coefficients whose real values are `lowPass1kHzQ04_f64`, `M = 1` (inputs at most 1 in size) and a
start of value `(0, 0)`: they have distinct real poles inside the unit circle, and for
`realPolesContraction` the condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the
bound `cInf·Ê + L` on each output's error is at most 1.04 × 10⁻¹¹, `20·log₁₀` of it (the bound in
decibels relative to 1.0) is at most −219.6, `Sb = computedStateBound_f64` is at most 2.75,
`V = stepValueBound_f64` is at most 56.2, and `V·10³⁵` is at most the largest finite binary64
value. -/
theorem lowPass1kHzQ04_bounds_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass1kHzQ04_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (h : 4 * (realCoeffs_f64 c).a2 < (realCoeffs_f64 c).a1 ^ 2)
      (h1 : (realCoeffs_f64 c).a2 < 1) (h2 : |(realCoeffs_f64 c).a1| < 1 + (realCoeffs_f64 c).a2),
      let C := realPolesContraction (realCoeffs_f64 c) h h1 h2
      C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s ≤ 1.04 * 10 ^ (-11 : ℤ) ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f64 c C 1 s + localErrBound_f64 c C 1 s) ≤
          -219.6 ∧
        computedStateBound_f64 c C 1 s ≤ 2.75 ∧
        stepValueBound_f64 c C 1 s ≤ 56.2 ∧
        stepValueBound_f64 c C 1 s * 10 ^ 35 ≤ maxFinite_f64 := by
  refine (fun H => ?main) (realPolesContraction_block_bounds_of_rat_f64 c _ hc s hs
    0.16832565 0.16832566 (1.04 * 10 ^ (-11 : ℤ)) 2.75 (56.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, h2, hsmall, hpos, hX, hSb, hV⟩ := H
    refine ⟨h, h1, h2, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_, hSb, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 50 549 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f64_eq]; norm_num)
  all_goals bound_norm_num [lowPass1kHzQ04_f64]

end conjure_dsp_lib.biquad

end
