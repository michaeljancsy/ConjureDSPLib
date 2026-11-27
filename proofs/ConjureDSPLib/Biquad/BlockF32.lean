module

public import ConjureDSPLib.Biquad.SpecF32
public import ConjureDSPLib.Biquad.Block
public import ConjureDSPLib.Biquad.Contraction
public import ConjureDSPLib.FloatFacts

/-!
# The biquad filter in f32 over a whole block

`process_f32_block_error`: when the Rust `process_f32` filters a block, given a `Contraction`
for the real values of the stored coefficients (see `Block.lean`), finite coefficients and
starting state, inputs at most `M`, no overflow and `cInf·K·κ·β < 1 − ρ`, every output and the
final state are within distances of the exact real-number filter `filt_real` that depend on the
coefficients, the `Contraction`, `M` and the starting state but not on the block length.
`Contraction`s for biquads with complex poles, distinct real poles, a repeated real pole or poles
close together inside the unit circle are in `Biquad/Contraction.lean`.

Each step rounds nine times (`tdf2_f32`); `tdf2_f32_localErr` bounds the effect of those
roundings on the step's output and new state by `α + β·Sb` when the state is at most `Sb` in
size and the input at most `M`, and no intermediate result overflows, with
`α = localErrBase_f32` and `β = localErrSlope_f32`. `block_error_real` in `Block.lean` turns that
into the whole-block bound.

`process_f32_block_error_of_inputs` replaces the no-overflow condition by finite inputs and
`stepValueBound_f32 c C M s ≤ maxFinite_f32`: `stepFinite_f32` shows that a step whose state is
within `Sb` and input within `M` does not overflow when `stepValueBound` at that `Sb` is at most
the largest finite value, and `noOverflow_f32_of_inputs` carries the state bound through the
block with `block_step`.

`block_bound_of_rat_f32`, `block_bounds_of_rat_f32`, `block_bound_ge_of_rat_f32` and
`smallness_fails_of_rat_f32` turn rational bounds on `ω` and `√a2` into bounds on the constants of
these theorems for `complexPolesContraction`, from above and below, and into failures of the
condition `cInf·K·κ·β < 1 − ρ`; `realPolesContraction_block_bounds_of_rat_f32` does the same
from rational bounds on `d = √(a1² − 4·a2)` for `realPolesContraction`, and
`closePolesContraction_block_bounds_of_rat_f32` for `closePolesContraction`, whose constants are
rational when `ε` is. The last sections apply them to RBJ-cookbook low-pass coefficients at chosen
cutoffs (the biquad table and cutoff facts in `proofs/README.md`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.biquad

/-- The exact real values of the five binary32 coefficients. -/
noncomputable def realCoeffs_f32 (c : CoeffsF32) : CoeffsReal where
  b0 := real_f32 c.b0
  b1 := real_f32 c.b1
  b2 := real_f32 c.b2
  a1 := real_f32 c.a1
  a2 := real_f32 c.a2

/-- The exact real values of the two binary32 state values. -/
noncomputable def realState_f32 (s : StateF32) : ℝ × ℝ := (real_f32 s.s1, real_f32 s.s2)

/-- All five coefficients are finite. -/
def CoeffsFinite_f32 (c : CoeffsF32) : Prop :=
  c.b0.isFinite = true ∧ c.b1.isFinite = true ∧ c.b2.isFinite = true ∧
    c.a1.isFinite = true ∧ c.a2.isFinite = true

/-- One step of `tdf2_f32` from state `s` on input `x` does not overflow: `x` and every
intermediate result are finite. With `y = b0 * x + s1` the output, these are `b0 * x`, `y`,
`b1 * x`, `a1 * y`, `b1 * x - a1 * y`, the new `s1 = b1 * x - a1 * y + s2`, `b2 * x`, `a2 * y`
and the new `s2 = b2 * x - a2 * y`. -/
def StepFinite_f32 (c : CoeffsF32) (s : StateF32) (x : Float32) : Prop :=
  let y := c.b0 * x + s.s1
  x.isFinite = true ∧ (c.b0 * x).isFinite = true ∧ y.isFinite = true ∧
    (c.b1 * x).isFinite = true ∧ (c.a1 * y).isFinite = true ∧
    (c.b1 * x - c.a1 * y).isFinite = true ∧ (c.b1 * x - c.a1 * y + s.s2).isFinite = true ∧
    (c.b2 * x).isFinite = true ∧ (c.a2 * y).isFinite = true ∧
    (c.b2 * x - c.a2 * y).isFinite = true

/-- No step overflows: running the filter from state `s` over the inputs, every step is
`StepFinite_f32`. -/
def NoOverflow_f32 (c : CoeffsF32) : StateF32 → List Float32 → Prop
  | _, [] => True
  | s, x :: xs => StepFinite_f32 c s x ∧ NoOverflow_f32 c (tdf2_f32 c s x).2 xs

/-- `α` for binary32: `localErrBase` with binary32's `u` and `η`, for inputs at most `M`. -/
noncomputable abbrev localErrBase_f32 (c : CoeffsF32) (M : ℝ) : ℝ :=
  localErrBase (realCoeffs_f32 c) unitRoundoff_f32 underflowErr_f32 M

/-- `β` for binary32: `localErrSlope` with binary32's `u`. -/
noncomputable abbrev localErrSlope_f32 (c : CoeffsF32) : ℝ :=
  localErrSlope (realCoeffs_f32 c) unitRoundoff_f32

/-- `L` for binary32: `localErrBound` with `α = localErrBase_f32 c M`, `β = localErrSlope_f32 c`,
the real values of the stored coefficients and the real value of the stored starting state `s`. -/
noncomputable abbrev localErrBound_f32 (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c))
    (M : ℝ) (s : StateF32) : ℝ :=
  localErrBound (realCoeffs_f32 c) C M (localErrBase_f32 c M) (localErrSlope_f32 c)
    (realState_f32 s)

/-- `Ê` for binary32: `stateErrBound` with `α = localErrBase_f32 c M`, `β = localErrSlope_f32 c`,
the real values of the stored coefficients and the real value of the stored starting state `s`. -/
noncomputable abbrev stateErrBound_f32 (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c))
    (M : ℝ) (s : StateF32) : ℝ :=
  stateErrBound (realCoeffs_f32 c) C M (localErrBase_f32 c M) (localErrSlope_f32 c)
    (realState_f32 s)

/-- `Sb` for binary32: `computedStateBound` with `α = localErrBase_f32 c M`,
`β = localErrSlope_f32 c`, the real values of the stored coefficients and the real value of the
stored starting state `s`. -/
noncomputable abbrev computedStateBound_f32 (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c))
    (M : ℝ) (s : StateF32) : ℝ :=
  computedStateBound (realCoeffs_f32 c) C M (localErrBase_f32 c M) (localErrSlope_f32 c)
    (realState_f32 s)

/-- `V` for binary32: `stepValueBound` with binary32's `η`, the real values of the stored
coefficients, inputs at most `M`, and `Sb = computedStateBound_f32 c C M s`. -/
noncomputable abbrev stepValueBound_f32 (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c))
    (M : ℝ) (s : StateF32) : ℝ :=
  stepValueBound (realCoeffs_f32 c) underflowErr_f32 M (computedStateBound_f32 c C M s)

/-- **One step's roundings in binary32.** If the coefficients and state are finite, the step
does not overflow, both state values are at most `Sb` in size and the input at most `M`, then
the output and the two new state values of `tdf2_f32` are each within
`α + β·Sb` (`localErrBase_f32`, `localErrSlope_f32`) of the exact step from the same state and
the computed output: `B0·X + S1`, `B1·X - A1·Y + S2` and `B2·X - A2·Y`, where capitals are exact
real values and `Y` is the computed output's. -/
theorem tdf2_f32_localErr (c : CoeffsF32) (s : StateF32) (x : Float32) (Sb M : ℝ)
    (hc : CoeffsFinite_f32 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hstep : StepFinite_f32 c s x) (hS1 : |real_f32 s.s1| ≤ Sb) (hS2 : |real_f32 s.s2| ≤ Sb)
    (hX : |real_f32 x| ≤ M) :
    let cr := realCoeffs_f32 c
    let L := localErrBase_f32 c M + localErrSlope_f32 c * Sb
    let Y := real_f32 (tdf2_f32 c s x).1
    |Y - (cr.b0 * real_f32 x + real_f32 s.s1)| ≤ L ∧
      |real_f32 (tdf2_f32 c s x).2.s1 - (cr.b1 * real_f32 x - cr.a1 * Y + real_f32 s.s2)| ≤ L ∧
      |real_f32 (tdf2_f32 c s x).2.s2 - (cr.b2 * real_f32 x - cr.a2 * Y)| ≤ L := by
  obtain ⟨hb0, hb1, hb2, ha1, ha2⟩ := hc
  obtain ⟨hx, hp0, hy, hp1, hq1, hd1, ht1, hp2, hq2, ht2⟩ := hstep
  exact step_localErr (realCoeffs_f32 c) (Model.unitRoundoffAt_pos _).le
    (Model.unitRoundoffAt_lt_one _).le (Model.underflowErrorAt_pos _).le hX hS1 hS2
    (abs_real_mul_sub_le_f32 _ _ hb0 hx hp0)
    (abs_real_add_sub_le_f32 _ _ hp0 hs1 hy)
    (abs_real_mul_sub_le_f32 _ _ hb1 hx hp1)
    (abs_real_mul_sub_le_f32 _ _ ha1 hy hq1)
    (abs_real_sub_sub_le_f32 _ _ hp1 hq1 hd1)
    (abs_real_add_sub_le_f32 _ _ hd1 hs2 ht1)
    (abs_real_mul_sub_le_f32 _ _ hb2 hx hp2)
    (abs_real_mul_sub_le_f32 _ _ ha2 hy hq2)
    (abs_real_sub_sub_le_f32 _ _ hp2 hq2 ht2)

/-- If the coefficients and starting state are finite and no step overflows (`NoOverflow_f32`),
then for every `Sb` and `M`, the run of `filt_f32` (as real values) satisfies `WithinLocalErr`
with `L = α + β·Sb` (`localErrBase_f32 c M`, `localErrSlope_f32 c`): every step whose state is
within `Sb` and its input within `M` rounds within `L`. -/
theorem filt_f32_withinLocalErr (c : CoeffsF32) (hc : CoeffsFinite_f32 c) (Sb M : ℝ) :
    ∀ (xs : List Float32) (s : StateF32), s.s1.isFinite = true → s.s2.isFinite = true →
      NoOverflow_f32 c s xs →
      WithinLocalErr (realCoeffs_f32 c) Sb M (localErrBase_f32 c M + localErrSlope_f32 c * Sb)
        (realState_f32 s) (xs.map real_f32) (realState_f32 (filt_f32 c s xs).1)
        ((filt_f32 c s xs).2.map real_f32) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _; simp [filt_f32, WithinLocalErr, realState_f32]
  | cons x xs ih =>
    intro s hs1 hs2 hno
    obtain ⟨hstep, hrest⟩ := hno
    have ht1 : (tdf2_f32 c s x).2.s1.isFinite = true := hstep.2.2.2.2.2.2.1
    have ht2 : (tdf2_f32 c s x).2.s2.isFinite = true := hstep.2.2.2.2.2.2.2.2.2
    simp only [filt_f32, List.map_cons, realState_f32, WithinLocalErr]
    exact ⟨_, _, fun h1 h2 hX => tdf2_f32_localErr c s x Sb M hc hs1 hs2 hstep h1 h2 hX,
      ih _ ht1 ht2 hrest⟩

/-- **Whole-block error of the f32 biquad.** Let `C` be a `Contraction` for the real values of the
stored coefficients (`realCoeffs_f32 c`), `0 ≤ M`, every input's real value at most `M` in size,
with `β = localErrSlope_f32 c` and `κ = roundGain (realCoeffs_f32 c)`. If the coefficients and
the starting state are finite, no step overflows (`NoOverflow_f32`), and `cInf·K·κ·β < 1 − ρ`, then
the outputs of `filt_f32` and of `filt_real` (run on the real values of the inputs from
`realState_f32 s`) have the same length, every output's real value is within `cInf·Ê + L` of the
corresponding exact output, and each final state value's real value within `cInf·Ê` of the
exact one, where `Ê = stateErrBound_f32 c C M s` and `L = localErrBound_f32 c C M s`. -/
theorem filt_f32_block_error (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c)) (s : StateF32)
    (xs : List Float32) (M : ℝ) (hc : CoeffsFinite_f32 c) (hs1 : s.s1.isFinite = true)
    (hs2 : s.s2.isFinite = true) (hno : NoOverflow_f32 c s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f32 x| ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ) :
    let Ê := stateErrBound_f32 c C M s
    let L := localErrBound_f32 c C M s
    let F := filt_real (realCoeffs_f32 c) (realState_f32 s) (xs.map real_f32)
    List.Forall₂ (fun y e => |real_f32 y - e| ≤ C.cInf * Ê + L) (filt_f32 c s xs).2 F.2 ∧
      |real_f32 (filt_f32 c s xs).1.s1 - F.1.1| ≤ C.cInf * Ê ∧
      |real_f32 (filt_f32 c s xs).1.s2 - F.1.2| ≤ C.cInf * Ê := by
  intro Ê L F
  have h := block_error_real (realCoeffs_f32 c) C M _ _ hM0
    (localErrBase_nonneg _ (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0)
    (localErrSlope_nonneg _ (Model.unitRoundoffAt_pos _).le) hsmall (xs.map real_f32)
    (realState_f32 s) _ _ (by simpa using hM)
    (filt_f32_withinLocalErr c hc _ M xs s hs1 hs2 hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust biquad `process_f32`.** Under the conditions of
`filt_f32_block_error` (with `state` as the starting state and the buffer as the inputs),
`process_f32` never fails, the buffer it returns has one sample per exact output, each sample's
real value is within `cInf·Ê + L` of the corresponding output of `filt_real` (run on the real
values of the inputs from `realState_f32 state`), and each value of the state it leaves is within
`cInf·Ê` of the exact final state's, where `Ê = stateErrBound_f32 c C M state` and
`L = localErrBound_f32 c C M state`. -/
theorem process_f32_block_error (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c))
    (state : StateF32) (buf : Slice Float32) (M : ℝ) (hc : CoeffsFinite_f32 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hno : NoOverflow_f32 c state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f32 x| ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ) :
    let Ê := stateErrBound_f32 c C M state
    let L := localErrBound_f32 c C M state
    let F := filt_real (realCoeffs_f32 c) (realState_f32 state) (buf.val.map real_f32)
    process_f32 c state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f32 y - e| ≤ C.cInf * Ê + L) r.2.val F.2 ∧
        |real_f32 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f32 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê L F
  have hblock := filt_f32_block_error c C state buf.val M hc hs1 hs2 hno hM0 hM hsmall
  apply WP.spec_mono (process_f32_spec c state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **One step does not overflow.** If the coefficients, both state values and the input are
finite, both state values are at most `Sb` in size, the input at most `M` in size, and
`V = stepValueBound (realCoeffs_f32 c) η M Sb` (with binary32's `η`) is at most the largest
finite binary32 value, then none of the step's nine operations overflows (`StepFinite_f32`). -/
theorem stepFinite_f32 (c : CoeffsF32) (s : StateF32) (x : Float32) (Sb M : ℝ)
    (hc : CoeffsFinite_f32 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hx : x.isFinite = true) (hS1 : |real_f32 s.s1| ≤ Sb) (hS2 : |real_f32 s.s2| ≤ Sb)
    (hX : |real_f32 x| ≤ M)
    (hcap : stepValueBound (realCoeffs_f32 c) underflowErr_f32 M Sb ≤ maxFinite_f32) :
    StepFinite_f32 c s x := by
  obtain ⟨hb0, hb1, hb2, ha1, ha2⟩ := hc
  obtain ⟨v0, v1, v2, rest⟩ := step_values_le (realCoeffs_f32 c) (u := unitRoundoff_f32)
    (P0 := real_f32 (c.b0 * x)) (Y := real_f32 (c.b0 * x + s.s1)) (P1 := real_f32 (c.b1 * x))
    (Q1 := real_f32 (c.a1 * (c.b0 * x + s.s1)))
    (D1 := real_f32 (c.b1 * x - c.a1 * (c.b0 * x + s.s1))) (P2 := real_f32 (c.b2 * x))
    (Q2 := real_f32 (c.a2 * (c.b0 * x + s.s1)))
    (Model.unitRoundoffAt_pos _).le (Model.unitRoundoffAt_lt_one _).le
    (Model.underflowErrorAt_pos _).le hX hS1 hS2
  -- Each operation in turn: its exact value is at most `V`, so it is finite, so its rounding is
  -- within `u·|e| + η`, which bounds the next operation's exact value.
  have hp0 := isFinite_mul_f32 _ _ hb0 hx (v0.trans hcap)
  obtain ⟨vy, rest⟩ := rest (abs_real_mul_sub_le_f32 _ _ hb0 hx hp0)
  have hy := isFinite_add_f32 _ _ hp0 hs1 (vy.trans hcap)
  obtain ⟨vq1, vq2, r1, r2⟩ := rest (abs_real_add_sub_le_f32 _ _ hp0 hs1 hy)
  have hp1 := isFinite_mul_f32 _ _ hb1 hx (v1.trans hcap)
  have hq1 := isFinite_mul_f32 _ _ ha1 hy (vq1.trans hcap)
  obtain ⟨vd1, r1⟩ := r1 (abs_real_mul_sub_le_f32 _ _ hb1 hx hp1)
    (abs_real_mul_sub_le_f32 _ _ ha1 hy hq1)
  have hd1 := isFinite_sub_f32 _ _ hp1 hq1 (vd1.trans hcap)
  have ht1 := isFinite_add_f32 _ _ hd1 hs2
    ((r1 (abs_real_sub_sub_le_f32 _ _ hp1 hq1 hd1)).trans hcap)
  have hp2 := isFinite_mul_f32 _ _ hb2 hx (v2.trans hcap)
  have hq2 := isFinite_mul_f32 _ _ ha2 hy (vq2.trans hcap)
  have ht2 := isFinite_sub_f32 _ _ hp2 hq2
    ((r2 (abs_real_mul_sub_le_f32 _ _ hb2 hx hp2) (abs_real_mul_sub_le_f32 _ _ ha2 hy hq2)).trans
      hcap)
  exact ⟨hx, hp0, hy, hp1, hq1, hd1, ht1, hp2, hq2, ht2⟩

/-- **No overflow, from the inputs alone.** Let `C` be a `Contraction` for the real values of the
stored coefficients, with `G = inputGain` and `κ = roundGain` of those values, and
`α = localErrBase_f32 c M`, `β = localErrSlope_f32 c`. Suppose the coefficients are finite, and
the numbers `Sb`, `R`, `Ê` satisfy `ρ·R + K·G·M ≤ R`, `ρ·Ê + K·κ·(α + β·Sb) ≤ Ê`,
`cInf·(R + Ê) ≤ Sb`, and
`V = stepValueBound` (binary32's `η`, inputs at most `M`, state values at most `Sb`) is at most
the largest finite binary32 value. Start from a state `s` with both values finite, and a real
state `r` that measures at most `R`, with `s`'s real value minus `r` measuring at most `Ê` (for
the filter's own start, `r` is `s`'s real value). If every input is finite and at most `M` in
size, then no step overflows (`NoOverflow_f32`). -/
theorem noOverflow_f32_of_inputs (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c))
    (hc : CoeffsFinite_f32 c) (Sb M R Ê : ℝ)
    (hR : C.ρ * R + C.K * inputGain (realCoeffs_f32 c) * M ≤ R)
    (hE : C.ρ * Ê + C.K * ((localErrBase_f32 c M + localErrSlope_f32 c * Sb) *
        roundGain (realCoeffs_f32 c)) ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb)
    (hcap : stepValueBound (realCoeffs_f32 c) underflowErr_f32 M Sb ≤ maxFinite_f32) :
    ∀ (xs : List Float32) (s : StateF32) (r : ℝ × ℝ), s.s1.isFinite = true →
      s.s2.isFinite = true → (∀ x ∈ xs, x.isFinite = true ∧ |real_f32 x| ≤ M) →
      C.N r.1 r.2 ≤ R → C.N (real_f32 s.s1 - r.1) (real_f32 s.s2 - r.2) ≤ Ê →
      NoOverflow_f32 c s xs := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hs1 hs2 hin hr he
    obtain ⟨hx, hX⟩ := hin x (by simp)
    -- The computed state is within `Sb`, so the step does not overflow.
    obtain ⟨hS1, hS2⟩ := C.state_le hS hr he
    have hstep := stepFinite_f32 c s x Sb M hc hs1 hs2 hx hS1 hS2 hX hcap
    -- Its roundings are within `L`, so both bounds carry on to the next step.
    obtain ⟨hdy, hd₁, hd₂⟩ := tdf2_f32_localErr c s x Sb M hc hs1 hs2 hstep hS1 hS2 hX
    obtain ⟨-, hr', he'⟩ := block_step _ C hR hE hX hr he hdy hd₁ hd₂
    let cr := realCoeffs_f32 c
    exact ⟨hstep, ih _ (cr.b1 * real_f32 x - cr.a1 * (cr.b0 * real_f32 x + r.1) + r.2,
      cr.b2 * real_f32 x - cr.a2 * (cr.b0 * real_f32 x + r.1)) hstep.2.2.2.2.2.2.1
      hstep.2.2.2.2.2.2.2.2.2 (fun z hz => hin z (List.mem_cons_of_mem _ hz)) hr' he'⟩

/-- **Whole-block error of the f32 biquad, with conditions on the inputs only.** Let `C` be a
`Contraction` for the real values of the stored coefficients (`realCoeffs_f32 c`), `0 ≤ M`, with
`β = localErrSlope_f32 c` and `κ = roundGain (realCoeffs_f32 c)`. If the coefficients, the
starting state and every input are finite, every input's real value is at most `M` in size,
`cInf·K·κ·β < 1 − ρ`, and `stepValueBound_f32 c C M s` is at most the largest finite binary32
value (about 3.4 × 10³⁸), then no step overflows (`NoOverflow_f32`), and the conclusion of
`filt_f32_block_error` holds: the outputs of `filt_f32` and of `filt_real` (run on the real
values of the inputs from `realState_f32 s`) have the same length, every output's real value is
within `cInf·Ê + L` of the corresponding exact output, and each final state value's real value
within `cInf·Ê` of the exact one, where `Ê = stateErrBound_f32 c C M s` and
`L = localErrBound_f32 c C M s`. -/
theorem filt_f32_block_error_of_inputs (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c))
    (s : StateF32) (xs : List Float32) (M : ℝ) (hc : CoeffsFinite_f32 c)
    (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hin : ∀ x ∈ xs, x.isFinite = true ∧ |real_f32 x| ≤ M) (hM0 : 0 ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ)
    (hcap : stepValueBound_f32 c C M s ≤ maxFinite_f32) :
    let Ê := stateErrBound_f32 c C M s
    let L := localErrBound_f32 c C M s
    let F := filt_real (realCoeffs_f32 c) (realState_f32 s) (xs.map real_f32)
    NoOverflow_f32 c s xs ∧
      List.Forall₂ (fun y e => |real_f32 y - e| ≤ C.cInf * Ê + L) (filt_f32 c s xs).2 F.2 ∧
      |real_f32 (filt_f32 c s xs).1.s1 - F.1.1| ≤ C.cInf * Ê ∧
      |real_f32 (filt_f32 c s xs).1.s2 - F.1.2| ≤ C.cInf * Ê := by
  intro Ê L F
  obtain ⟨hR, hE, hS, hr, he⟩ := block_constants (realCoeffs_f32 c) C M _ _ (realState_f32 s)
    hM0
    (localErrBase_nonneg _ (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0)
    (localErrSlope_nonneg _ (Model.unitRoundoffAt_pos _).le) hsmall
  have hno := noOverflow_f32_of_inputs c C hc _ M _ _ hR hE hS hcap xs s (realState_f32 s)
    hs1 hs2 hin hr he
  exact ⟨hno, filt_f32_block_error c C s xs M hc hs1 hs2 hno hM0 (fun x hx => (hin x hx).2)
    hsmall⟩

/-- **Whole-block error of the Rust biquad `process_f32`, with conditions on the inputs only.**
Under the conditions of `filt_f32_block_error_of_inputs` (with `state` as the starting state and
the buffer as the inputs: the coefficients, `state` and every sample finite, every sample's real
value at most `M` in size, `0 ≤ M`, `cInf·K·κ·β < 1 − ρ`, and `stepValueBound_f32 c C M state`
at most the largest finite binary32 value), no step overflows (`NoOverflow_f32`), `process_f32`
never fails, the buffer it returns has one sample per exact output, each sample's real value is
within `cInf·Ê + L` of the corresponding output of `filt_real` (run on the real values of the inputs
from `realState_f32 state`), and each value of the state it leaves is within `cInf·Ê` of the
exact final state's, where `Ê = stateErrBound_f32 c C M state` and
`L = localErrBound_f32 c C M state`. -/
theorem process_f32_block_error_of_inputs (c : CoeffsF32) (C : Contraction (realCoeffs_f32 c))
    (state : StateF32) (buf : Slice Float32) (M : ℝ) (hc : CoeffsFinite_f32 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f32 x| ≤ M) (hM0 : 0 ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ)
    (hcap : stepValueBound_f32 c C M state ≤ maxFinite_f32) :
    let Ê := stateErrBound_f32 c C M state
    let L := localErrBound_f32 c C M state
    let F := filt_real (realCoeffs_f32 c) (realState_f32 state) (buf.val.map real_f32)
    NoOverflow_f32 c state buf.val ∧
      process_f32 c state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f32 y - e| ≤ C.cInf * Ê + L) r.2.val F.2 ∧
          |real_f32 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f32 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê L F
  have hno := (filt_f32_block_error_of_inputs c C state buf.val M hc hs1 hs2 hin hM0 hsmall
    hcap).1
  exact ⟨hno, process_f32_block_error c C state buf M hc hs1 hs2 hno hM0
    (fun x hx => (hin x hx).2) hsmall⟩

/-- **The f32 output error bound with `complexPolesContraction`, from rational numbers.** For
stored coefficients with real values `q`, a start of value `(0, 0)` and `M = 1` (inputs at most 1
in size): if `q` has complex poles inside the unit circle (`q.a1² < 4·q.a2`, `q.a2 < 1`),
`0 < ωl`, `0 ≤ ωu`, `ωl² ≤ q.a2 - q.a1²/4 ≤ ωu²`, `0 ≤ ρu`, `q.a2 ≤ ρu²`, and, with
`ci = (1 + |q.a1|/2)/ωl + 1`, `k = ωu + |q.a1|/2 + 1`, `u = 2⁻²⁴`, `η = 2⁻¹⁵⁰`,
`α = localErrBase q u η 1` and `β = localErrSlope q u`: `ci·k·κ·β < 1 − ρu` (`κ = roundGain q`)
and `outErrBoundAt q 1 α β 0 ci k ρu ≤ X`; then for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, and the bound `cInf·Ê + L` on each
output's error is positive and at most `X`. The hypotheses are statements about rational numbers
that `norm_num` checks. -/
theorem block_bound_of_rat_f32 (c : CoeffsF32) (q : CoeffsReal) (hc : realCoeffs_f32 c = q)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) (ωl ωu ρu X : ℝ)
    (h : q.a1 ^ 2 < 4 * q.a2) (h1 : q.a2 < 1) (hωl : 0 < ωl) (hωu : 0 ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ q.a2 - q.a1 ^ 2 / 4) (hωu2 : q.a2 - q.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρu : 0 ≤ ρu) (hρu2 : q.a2 ≤ ρu ^ 2)
    (hsm : ((1 + |q.a1| / 2) / ωl + 1) * (ωu + |q.a1| / 2 + 1) * roundGain q *
      localErrSlope q (2 ^ (-24 : ℤ)) < 1 - ρu)
    (hX : outErrBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
      (localErrSlope q (2 ^ (-24 : ℤ))) 0 ((1 + |q.a1| / 2) / ωl + 1) (ωu + |q.a1| / 2 + 1)
      ρu ≤ X) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        0 < C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ X := by
  subst hc
  rw [← unitRoundoff_f32_eq] at hsm hX
  rw [← underflowErr_f32_eq] at hX
  refine ⟨h, h1, ?_⟩
  intro C
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f32)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f32)
  have hα : 0 < localErrBase_f32 c 1 := localErrBase_pos _ hu.le hη zero_le_one
  have hβ : 0 ≤ localErrSlope_f32 c := localErrSlope_nonneg _ hu.le
  have hs0 : complexPoleNorm (realCoeffs_f32 c) (realState_f32 s).1 (realState_f32 s).2 ≤ 0 := by
    rw [hs]; exact (complexPoleNorm_zero _).le
  obtain ⟨hsmall, -, -, hpos, hbd, -⟩ := complexPolesContraction_block_bounds_le
    (realCoeffs_f32 c) h h1 1 (localErrBase_f32 c 1) (localErrSlope_f32 c) underflowErr_f32 0
    ωl ωu ρu (realState_f32 s) zero_le_one hα.le hβ hs0 hωl hωu hωl2 hωu2 hρu hρu2 hsm
  exact ⟨hsmall, hα.trans_le hpos, hbd.trans hX⟩

/-- **The f32 whole-block constants with `complexPolesContraction`, from rational numbers.** Under
the hypotheses of `block_bound_of_rat_f32`, and, with `Sb' = stateBoundAt q 1 α β 0 ci k ρu`,
`Sb' ≤ Sbb` and `stepValueBound q η 1 Sb' ≤ Vb`: its conclusions hold, and also
`Sb = computedStateBound_f32` is at most `Sbb` and `V = stepValueBound_f32` at most `Vb`. -/
theorem block_bounds_of_rat_f32 (c : CoeffsF32) (q : CoeffsReal) (hc : realCoeffs_f32 c = q)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) (ωl ωu ρu X Sbb Vb : ℝ)
    (h : q.a1 ^ 2 < 4 * q.a2) (h1 : q.a2 < 1) (hωl : 0 < ωl) (hωu : 0 ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ q.a2 - q.a1 ^ 2 / 4) (hωu2 : q.a2 - q.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρu : 0 ≤ ρu) (hρu2 : q.a2 ≤ ρu ^ 2)
    (hsm : ((1 + |q.a1| / 2) / ωl + 1) * (ωu + |q.a1| / 2 + 1) * roundGain q *
      localErrSlope q (2 ^ (-24 : ℤ)) < 1 - ρu)
    (hX : outErrBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
      (localErrSlope q (2 ^ (-24 : ℤ))) 0 ((1 + |q.a1| / 2) / ωl + 1) (ωu + |q.a1| / 2 + 1)
      ρu ≤ X)
    (hSb : stateBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
      (localErrSlope q (2 ^ (-24 : ℤ))) 0 ((1 + |q.a1| / 2) / ωl + 1) (ωu + |q.a1| / 2 + 1) ρu ≤
        Sbb)
    (hV : stepValueBound q (2 ^ (-150 : ℤ)) 1
      (stateBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
        (localErrSlope q (2 ^ (-24 : ℤ))) 0 ((1 + |q.a1| / 2) / ωl + 1) (ωu + |q.a1| / 2 + 1)
        ρu) ≤ Vb) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        0 < C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ X ∧
        computedStateBound_f32 c C 1 s ≤ Sbb ∧ stepValueBound_f32 c C 1 s ≤ Vb := by
  obtain ⟨h', h1', hrest⟩ :=
    block_bound_of_rat_f32 c q hc s hs ωl ωu ρu X h h1 hωl hωu hωl2 hωu2 hρu hρu2 hsm hX
  subst hc
  rw [← unitRoundoff_f32_eq] at hsm hSb hV
  rw [← underflowErr_f32_eq] at hSb hV
  refine ⟨h', h1', ?_⟩
  intro C
  obtain ⟨hsmall, hpos, hX'⟩ := hrest
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f32)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f32)
  have hs0 : complexPoleNorm (realCoeffs_f32 c) (realState_f32 s).1 (realState_f32 s).2 ≤ 0 := by
    rw [hs]; exact (complexPoleNorm_zero _).le
  obtain ⟨-, hSb', -, -, -, hV'⟩ := complexPolesContraction_block_bounds_le
    (realCoeffs_f32 c) h' h1' 1 (localErrBase_f32 c 1) (localErrSlope_f32 c) underflowErr_f32 0
    ωl ωu ρu (realState_f32 s) zero_le_one (localErrBase_pos _ hu.le hη zero_le_one).le
    (localErrSlope_nonneg _ hu.le) hs0 hωl hωu hωl2 hωu2 hρu hρu2 hsm
  exact ⟨hsmall, hpos, hX', hSb'.trans hSb, hV'.trans hV⟩

/-- **The f32 bound on each output's error with `complexPolesContraction`, from below.** For
stored coefficients with real values `q`, any start `s` and `M = 1` (inputs at most 1 in size):
if `q` has complex poles inside the unit circle (`h`, `h1`), the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds for `complexPolesContraction`
(`κ = roundGain`), `0 < ωl ≤ ωu`, `ωl² ≤ q.a2 - q.a1²/4 ≤ ωu²`, `ρl² ≤ q.a2`, and, with
`ci = (1 + |q.a1|/2)/ωu + 1`, `k = ωl + |q.a1|/2 + 1`, `u = 2⁻²⁴`, `η = 2⁻¹⁵⁰`,
`α = localErrBase q u η 1` and `β = localErrSlope q u`: `Y ≤ outErrBoundAt q 1 α β 0 ci k ρl`;
then the bound `cInf·Ê + L` on each output's error is at least `Y`. -/
theorem block_bound_ge_of_rat_f32 (c : CoeffsF32) (q : CoeffsReal) (hc : realCoeffs_f32 c = q)
    (s : StateF32) (ωl ωu ρl Y : ℝ)
    (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2) (h1 : (realCoeffs_f32 c).a2 < 1)
    (hsmall : (complexPolesContraction (realCoeffs_f32 c) h h1).cInf *
      (complexPolesContraction (realCoeffs_f32 c) h h1).K * roundGain (realCoeffs_f32 c) *
      localErrSlope_f32 c < 1 - (complexPolesContraction (realCoeffs_f32 c) h h1).ρ)
    (hωl : 0 < ωl) (hωu : ωl ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ q.a2 - q.a1 ^ 2 / 4) (hωu2 : q.a2 - q.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρl2 : ρl ^ 2 ≤ q.a2)
    (hY : Y ≤ outErrBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
      (localErrSlope q (2 ^ (-24 : ℤ))) 0 ((1 + |q.a1| / 2) / ωu + 1) (ωl + |q.a1| / 2 + 1)
      ρl) :
    let C := complexPolesContraction (realCoeffs_f32 c) h h1
    Y ≤ C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s := by
  subst hc
  rw [← unitRoundoff_f32_eq, ← underflowErr_f32_eq] at hY
  intro C
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f32)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f32)
  have hα : 0 ≤ localErrBase_f32 c 1 := (localErrBase_pos _ hu.le hη zero_le_one).le
  have hβ : 0 ≤ localErrSlope_f32 c := localErrSlope_nonneg _ hu.le
  exact hY.trans (complexPolesContraction_block_bounds_ge (realCoeffs_f32 c) h h1 1 _ _ ωl ωu ρl
    (realState_f32 s) zero_le_one hα hβ hsmall hωl hωu hωl2 hωu2 hρl2).2

/-- **When the f32 condition fails, for `complexPolesContraction`.** For stored coefficients with
real values `q` with complex poles inside the unit circle (`h`, `h1`): if `0 < ωl ≤ ωu`,
`ωl² ≤ q.a2 - q.a1²/4 ≤ ωu²`, `ρl² ≤ q.a2` and, with `ci = (1 + |q.a1|/2)/ωu + 1`,
`k = ωl + |q.a1|/2 + 1` and `u = 2⁻²⁴`, `1 − ρl ≤ ci·k·κ·localErrSlope q u` (`κ = roundGain q`),
then the condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems is false. -/
theorem smallness_fails_of_rat_f32 (c : CoeffsF32) (q : CoeffsReal) (hc : realCoeffs_f32 c = q)
    (ωl ωu ρl : ℝ) (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
    (h1 : (realCoeffs_f32 c).a2 < 1) (hωl : 0 < ωl) (hωu : ωl ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ q.a2 - q.a1 ^ 2 / 4) (hωu2 : q.a2 - q.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρl2 : ρl ^ 2 ≤ q.a2)
    (hfail : 1 - ρl ≤ ((1 + |q.a1| / 2) / ωu + 1) * (ωl + |q.a1| / 2 + 1) * roundGain q *
      localErrSlope q (2 ^ (-24 : ℤ))) :
    ¬ (complexPolesContraction (realCoeffs_f32 c) h h1).cInf *
      (complexPolesContraction (realCoeffs_f32 c) h h1).K * roundGain (realCoeffs_f32 c) *
      localErrSlope_f32 c < 1 - (complexPolesContraction (realCoeffs_f32 c) h h1).ρ := by
  subst hc
  rw [← unitRoundoff_f32_eq] at hfail
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f32)
  exact complexPolesContraction_smallness_fails _ h h1 _ ωl ωu ρl
    (localErrSlope_nonneg _ hu.le) hωl hωu hωl2 hωu2 hρl2 hfail

/-- **The f32 whole-block constants with `realPolesContraction`, from rational numbers.** For
stored coefficients with real values `q`, a start of value `(0, 0)` and `M = 1` (inputs at most 1
in size): if `q` has distinct real poles inside the unit circle (`4·q.a2 < q.a1²`, `q.a2 < 1`,
`|q.a1| < 1 + q.a2`), `0 < dl`, `0 ≤ du`, `dl² ≤ q.a1² - 4·q.a2 ≤ du²`, and, with `ci = 1/dl`,
`k = 2`, `ρu = (|q.a1| + du)/2`, `u = 2⁻²⁴`, `η = 2⁻¹⁵⁰`, `α = localErrBase q u η 1`,
`β = localErrSlope q u` and `Sb' = stateBoundAt q 1 α β 0 ci k ρu`: `ci·k·κ·β < 1 − ρu`
(`κ = roundGain q`), `outErrBoundAt q 1 α β 0 ci k ρu ≤ X`, `Sb' ≤ Sbb` and
`stepValueBound q η 1 Sb' ≤ Vb`; then for `realPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is positive and at most `X`, `Sb = computedStateBound_f32` is at most `Sbb` and
`V = stepValueBound_f32` at most `Vb`. The hypotheses are statements about rational numbers that
`norm_num` checks. -/
theorem realPolesContraction_block_bounds_of_rat_f32 (c : CoeffsF32) (q : CoeffsReal)
    (hc : realCoeffs_f32 c = q) (s : StateF32) (hs : realState_f32 s = (0, 0))
    (dl du X Sbb Vb : ℝ) (h : 4 * q.a2 < q.a1 ^ 2) (h1 : q.a2 < 1) (h2 : |q.a1| < 1 + q.a2)
    (hdl : 0 < dl) (hdu : 0 ≤ du)
    (hdl2 : dl ^ 2 ≤ q.a1 ^ 2 - 4 * q.a2) (hdu2 : q.a1 ^ 2 - 4 * q.a2 ≤ du ^ 2)
    (hsm : 1 / dl * 2 * roundGain q * localErrSlope q (2 ^ (-24 : ℤ)) < 1 - (|q.a1| + du) / 2)
    (hX : outErrBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
      (localErrSlope q (2 ^ (-24 : ℤ))) 0 (1 / dl) 2 ((|q.a1| + du) / 2) ≤ X)
    (hSb : stateBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
      (localErrSlope q (2 ^ (-24 : ℤ))) 0 (1 / dl) 2 ((|q.a1| + du) / 2) ≤ Sbb)
    (hV : stepValueBound q (2 ^ (-150 : ℤ)) 1
      (stateBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
        (localErrSlope q (2 ^ (-24 : ℤ))) 0 (1 / dl) 2 ((|q.a1| + du) / 2)) ≤ Vb) :
    ∃ (h : 4 * (realCoeffs_f32 c).a2 < (realCoeffs_f32 c).a1 ^ 2)
      (h1 : (realCoeffs_f32 c).a2 < 1) (h2 : |(realCoeffs_f32 c).a1| < 1 + (realCoeffs_f32 c).a2),
      let C := realPolesContraction (realCoeffs_f32 c) h h1 h2
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        0 < C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ X ∧
        computedStateBound_f32 c C 1 s ≤ Sbb ∧ stepValueBound_f32 c C 1 s ≤ Vb := by
  subst hc
  rw [← unitRoundoff_f32_eq] at hsm hX hSb hV
  rw [← underflowErr_f32_eq] at hX hSb hV
  refine ⟨h, h1, h2, ?_⟩
  intro C
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f32)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f32)
  have hα : 0 < localErrBase_f32 c 1 := localErrBase_pos _ hu.le hη zero_le_one
  have hβ : 0 ≤ localErrSlope_f32 c := localErrSlope_nonneg _ hu.le
  have hs0 : realPoleNorm (realCoeffs_f32 c) (realState_f32 s).1 (realState_f32 s).2 ≤ 0 := by
    rw [hs]; exact (realPoleNorm_zero _).le
  obtain ⟨hsmall, hSb', -, hpos, hbd, hV'⟩ := realPolesContraction_block_bounds_le
    (realCoeffs_f32 c) h h1 h2 1 (localErrBase_f32 c 1) (localErrSlope_f32 c) underflowErr_f32 0
    dl du (realState_f32 s) zero_le_one hα.le hβ hs0 hdl hdu hdl2 hdu2 hsm
  exact ⟨hsmall, hα.trans_le hpos, hbd.trans hX, hSb'.trans hSb, hV'.trans hV⟩

/-- **The f32 whole-block constants with `closePolesContraction`, from rational numbers.** For
stored coefficients with real values `q`, a start of value `(0, 0)` and `M = 1` (inputs at most 1
in size): let `ε > 0`, `δu` with `-δu ≤ q.a1²/4 - q.a2 ≤ δu`, and `ρu < 1` with
`|q.a1|/2 + ε ≤ ρu` and `|q.a1|/2 + δu/ε ≤ ρu`, so that `ρ ≤ ρu`. With `ci = 1/ε`, `u = 2⁻²⁴`,
`η = 2⁻¹⁵⁰`, `α = localErrBase q u η 1`, `β = localErrSlope q u` and
`Sb' = stateBoundAt q 1 α β 0 ci 1 ρu`: if `ci·1·κ·β < 1 − ρu` (`κ = roundGain q`),
`outErrBoundAt q 1 α β 0 ci 1 ρu ≤ X`, `Sb' ≤ Sbb` and `stepValueBound q η 1 Sb' ≤ Vb`, then the
condition `ρ < 1` of `closePolesContraction` holds and, for it, `cInf·K·κ·β < 1 − ρ`, the bound
`cInf·Ê + L` on each output's error is positive and at most `X`,
`Sb = computedStateBound_f32` is at most `Sbb` and `V = stepValueBound_f32` at most `Vb`. -/
theorem closePolesContraction_block_bounds_of_rat_f32 (c : CoeffsF32) (q : CoeffsReal)
    (hc : realCoeffs_f32 c = q) (s : StateF32) (hs : realState_f32 s = (0, 0))
    (ε δu ρu X Sbb Vb : ℝ) (hε : 0 < ε) (hδl : -δu ≤ q.a1 ^ 2 / 4 - q.a2)
    (hδu : q.a1 ^ 2 / 4 - q.a2 ≤ δu) (hρε : |q.a1| / 2 + ε ≤ ρu)
    (hρδ : |q.a1| / 2 + δu / ε ≤ ρu) (hρ1 : ρu < 1)
    (hsm : 1 / ε * 1 * roundGain q * localErrSlope q (2 ^ (-24 : ℤ)) < 1 - ρu)
    (hX : outErrBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
      (localErrSlope q (2 ^ (-24 : ℤ))) 0 (1 / ε) 1 ρu ≤ X)
    (hSb : stateBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
      (localErrSlope q (2 ^ (-24 : ℤ))) 0 (1 / ε) 1 ρu ≤ Sbb)
    (hV : stepValueBound q (2 ^ (-150 : ℤ)) 1
      (stateBoundAt q 1 (localErrBase q (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) 1)
        (localErrSlope q (2 ^ (-24 : ℤ))) 0 (1 / ε) 1 ρu) ≤ Vb) :
    ∃ (h1 : |(realCoeffs_f32 c).a1| / 2 +
        max ε (|(realCoeffs_f32 c).a1 ^ 2 / 4 - (realCoeffs_f32 c).a2| / ε) < 1),
      let C := closePolesContraction (realCoeffs_f32 c) hε h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        0 < C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ X ∧
        computedStateBound_f32 c C 1 s ≤ Sbb ∧ stepValueBound_f32 c C 1 s ≤ Vb := by
  subst hc
  rw [← unitRoundoff_f32_eq] at hsm hX hSb hV
  rw [← underflowErr_f32_eq] at hX hSb hV
  have hρ : |(realCoeffs_f32 c).a1| / 2 +
      max ε (|(realCoeffs_f32 c).a1 ^ 2 / 4 - (realCoeffs_f32 c).a2| / ε) ≤ ρu := by
    have hd : |(realCoeffs_f32 c).a1 ^ 2 / 4 - (realCoeffs_f32 c).a2| / ε ≤ δu / ε :=
      div_le_div_of_nonneg_right (abs_le.mpr ⟨hδl, hδu⟩) hε.le
    have hm : max ε (|(realCoeffs_f32 c).a1 ^ 2 / 4 - (realCoeffs_f32 c).a2| / ε) ≤
        ρu - |(realCoeffs_f32 c).a1| / 2 := max_le (by linarith) (by linarith)
    linarith
  refine ⟨hρ.trans_lt hρ1, ?_⟩
  intro C
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f32)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f32)
  have hα : 0 < localErrBase_f32 c 1 := localErrBase_pos _ hu.le hη zero_le_one
  have hβ : 0 ≤ localErrSlope_f32 c := localErrSlope_nonneg _ hu.le
  have hs0 :
      repeatedPoleNorm (realCoeffs_f32 c) ε (realState_f32 s).1 (realState_f32 s).2 ≤ 0 := by
    rw [hs]; simp [repeatedPoleNorm]
  obtain ⟨hsmall, hSb', -, hpos, hbd, hV'⟩ := block_bounds_le (realCoeffs_f32 c) C 1
    (localErrBase_f32 c 1) (localErrSlope_f32 c) underflowErr_f32 0 (1 / ε) 1 ρu
    (realState_f32 s) zero_le_one hα.le hβ hs0 le_rfl le_rfl hρ hsm
  exact ⟨hsmall, hα.trans_le hpos, hbd.trans hX, hSb'.trans hSb, hV'.trans hV⟩

/-! ## RBJ low-pass examples, f32

The theorems behind the biquad table and cutoff facts in `proofs/README.md`, for an RBJ-cookbook
Butterworth low-pass with `Q = 0.7071` at 48 kHz. Each `lowPass…_f32` below holds the exact real
values of the stored coefficients at one cutoff `f`. Worked out outside Lean, not proved: they are
what this computation gives, in binary64 in this order and then each rounded to binary32:
`w = 2π·f/48000`, `α = sin w/(2Q)`, `a0 = 1 + α`, `b0 = ((1 − cos w)/2)/a0`, `b1 = (1 − cos w)/a0`,
`b2 = b0`, `a1 = (−2 cos w)/a0`, `a2 = (1 − α)/a0`. `cos` and `sin` are outside the model. -/

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at a
100 Hz cutoff. Their bits: `b0 = 0x38320537`, `b1 = 0x38B20537`, `b2 = 0x38320537`,
`a1 = 0xBFFDA169`, `a2 = 0x3F7B4DF2`. -/
noncomputable def lowPass100Hz_f32 : CoeffsReal where
  b0 := (11666743 / 2 ^ 38)
  b1 := (11666743 / 2 ^ 37)
  b2 := (11666743 / 2 ^ 38)
  a1 := -(16621929 / 2 ^ 23)
  a2 := (8234745 / 2 ^ 23)

/-- **Row 100 Hz of the biquad table in `proofs/README.md`, f32.** For stored binary32 coefficients
whose real values are `lowPass100Hz_f32`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: they have complex poles inside the unit circle, and for `complexPolesContraction` the
condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each
output's error is at least 17 and at most 17.1, `Sb = computedStateBound_f32` is at most 25.1,
`V = stepValueBound_f32` is at most 619, and `V·10³⁵` is at most the largest finite binary32 value.
-/
theorem lowPass100Hz_bounds_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass100Hz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        17 ≤ C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 17.1 ∧
        computedStateBound_f32 c C 1 s ≤ 25.1 ∧
        stepValueBound_f32 c C 1 s ≤ 619 ∧
        stepValueBound_f32 c C 1 s * 10 ^ 35 ≤ maxFinite_f32 := by
  refine (fun H => ?main) (block_bounds_of_rat_f32 c _ hc s hs
    0.00916971671 0.00916971672 0.99078660724 (17.1) 25.1 (619)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, -, hX, hSb, hV⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine (fun hY => ?main2) (block_bound_ge_of_rat_f32 c _ hc s
      0.00916971671 0.00916971672 0.99078660723 17 h h1 hsmall ?_ ?_ ?_ ?_ ?_ ?_)
    case main2 =>
      refine ⟨hsmall, hY, hX, hSb, hV, ?_⟩
      · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
          (by rw [maxFinite_f32_eq]; norm_num)
    all_goals bound_norm_num [lowPass100Hz_f32]
  all_goals bound_norm_num [lowPass100Hz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at a
1 kHz cutoff. Their bits: `b0 = 0x3B8052D3`, `b1 = 0x3C0052D3`, `b2 = 0x3B8052D3`,
`a1 = 0xBFE85D0C`, `a2 = 0x3F54BCAF`. -/
noncomputable def lowPass1kHz_f32 : CoeffsReal where
  b0 := (8409811 / 2 ^ 31)
  b1 := (8409811 / 2 ^ 30)
  b2 := (8409811 / 2 ^ 31)
  a1 := -(3807043 / 2 ^ 21)
  a2 := (13941935 / 2 ^ 24)

/-- **Row 1 kHz of the biquad table in `proofs/README.md`, f32.** For stored binary32 coefficients
whose real values are `lowPass1kHz_f32`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: they have complex poles inside the unit circle, and for `complexPolesContraction` the
condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each
output's error is at most 0.0542, `20·log₁₀` of it (the bound in decibels relative to 1.0) is at
most −25.3, `Sb = computedStateBound_f32` is at most 8.35, `V = stepValueBound_f32` is at most 186,
and `V·10³⁵` is at most the largest finite binary32 value. -/
theorem lowPass1kHz_bounds_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass1kHz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 0.0542 ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s) ≤
          -25.3 ∧
        computedStateBound_f32 c C 1 s ≤ 8.35 ∧
        stepValueBound_f32 c C 1 s ≤ 186 ∧
        stepValueBound_f32 c C 1 s * 10 ^ 35 ≤ maxFinite_f32 := by
  refine (fun H => ?main) (block_bounds_of_rat_f32 c _ hc s hs
    0.0844964427 0.0844964428 0.9115942536 (0.0542) 8.35 (186)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX, hSb, hV⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_, hSb, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 200 253 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f32_eq]; norm_num)
  all_goals bound_norm_num [lowPass1kHz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at a
10 kHz cutoff. Their bits: `b0 = 0x3E617A7F`, `b1 = 0x3EE17A7F`, `b2 = 0x3E617A7F`,
`a1 = 0xBE9D792E`, `a2 = 0x3E40DC57`. -/
noncomputable def lowPass10kHz_f32 : CoeffsReal where
  b0 := (14776959 / 2 ^ 26)
  b1 := (14776959 / 2 ^ 25)
  b2 := (14776959 / 2 ^ 26)
  a1 := -(5160087 / 2 ^ 24)
  a2 := (12639319 / 2 ^ 26)

/-- **Row 10 kHz of the biquad table in `proofs/README.md`, f32.** For stored binary32 coefficients
whose real values are `lowPass10kHz_f32`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: they have complex poles inside the unit circle, and for `complexPolesContraction` the
condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each
output's error is at most 1.81 × 10⁻⁴, `20·log₁₀` of it (the bound in decibels relative to 1.0) is
at most −74.8, `Sb = computedStateBound_f32` is at most 7.28, `V = stepValueBound_f32` is at most
41.4, and `V·10³⁵` is at most the largest finite binary32 value. -/
theorem lowPass10kHz_bounds_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass10kHz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 1.81 * 10 ^ (-4 : ℤ) ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s) ≤
          -74.8 ∧
        computedStateBound_f32 c C 1 s ≤ 7.28 ∧
        stepValueBound_f32 c C 1 s ≤ 41.4 ∧
        stepValueBound_f32 c C 1 s * 10 ^ 35 ≤ maxFinite_f32 := by
  refine (fun H => ?main) (block_bounds_of_rat_f32 c _ hc s hs
    0.405821942 0.405821943 0.433982177 (1.81 * 10 ^ (-4 : ℤ)) 7.28 (41.4)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX, hSb, hV⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_, hSb, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 50 187 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f32_eq]; norm_num)
  all_goals bound_norm_num [lowPass10kHz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at an
82 Hz cutoff. Their bits: `b0 = 0x37EFCC7B`, `b1 = 0x386FCC7B`, `b2 = 0x37EFCC7B`,
`a1 = 0xBFFE0E97`, `a2 = 0x3F7C24AD`. -/
noncomputable def lowPass82Hz_f32 : CoeffsReal where
  b0 := (15715451 / 2 ^ 39)
  b1 := (15715451 / 2 ^ 38)
  b2 := (15715451 / 2 ^ 39)
  a1 := -(16649879 / 2 ^ 23)
  a2 := (16524461 / 2 ^ 24)

/-- **At 82 Hz the f32 condition fails.** For stored binary32 coefficients whose real values are
`lowPass82Hz_f32`: they have complex poles inside the unit circle, and for `complexPolesContraction`
the condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems (`κ = roundGain`,
`β = localErrSlope_f32`) is false, so those theorems prove nothing here. -/
theorem lowPass82Hz_smallness_fails_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass82Hz_f32) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      ¬ C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ := by
  have h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2 := by
    rw [hc]; norm_num [lowPass82Hz_f32]
  have h1 : (realCoeffs_f32 c).a2 < 1 := by rw [hc]; norm_num [lowPass82Hz_f32]
  refine ⟨h, h1, smallness_fails_of_rat_f32 c _ hc 0.0075349244 0.00753492441 0.99243872758 h h1
    ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals bound_norm_num [lowPass82Hz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at an
83 Hz cutoff. Their bits: `b0 = 0x37F5A919`, `b1 = 0x3875A919`, `b2 = 0x37F5A919`,
`a1 = 0xBFFE0887`, `a2 = 0x3F7C18BA`. -/
noncomputable def lowPass83Hz_f32 : CoeffsReal where
  b0 := (16099609 / 2 ^ 39)
  b1 := (16099609 / 2 ^ 38)
  b2 := (16099609 / 2 ^ 39)
  a1 := -(16648327 / 2 ^ 23)
  a2 := (8260701 / 2 ^ 23)

/-- **The f32 bound at an 83 Hz cutoff.** For stored binary32 coefficients whose real values are
`lowPass83Hz_f32`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at most 606. -/
theorem lowPass83Hz_bound_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass83Hz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 606 := by
  refine (fun H => ?main) (block_bound_of_rat_f32 c _ hc s hs
    0.00761869495 0.00761869496 0.99234686346 (606)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, -, hX⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    exact ⟨hsmall, hX⟩
  all_goals bound_norm_num [lowPass83Hz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at a
240 Hz cutoff. Their bits: `b0 = 0x397D1550`, `b1 = 0x39FD1550`, `b2 = 0x397D1550`,
`a1 = 0xBFFA5060`, `a2 = 0x3F74E005`. -/
noncomputable def lowPass240Hz_f32 : CoeffsReal where
  b0 := (1036629 / 2 ^ 32)
  b1 := (1036629 / 2 ^ 31)
  b2 := (1036629 / 2 ^ 32)
  a1 := -(512643 / 2 ^ 18)
  a2 := (16048133 / 2 ^ 24)

/-- **The f32 bound at a 240 Hz cutoff.** For stored binary32 coefficients whose real values are
`lowPass240Hz_f32`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at least 1.07. -/
theorem lowPass240Hz_bound_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass240Hz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        1.07 ≤ C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s := by
  refine (fun H => ?main) (block_bound_of_rat_f32 c _ hc s hs
    0.0217275075 0.0217275076 0.9780302996 (1.08)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, -, -⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine (fun hY => ?main2) (block_bound_ge_of_rat_f32 c _ hc s
      0.0217275075 0.0217275076 0.9780302995 1.07 h h1 hsmall ?_ ?_ ?_ ?_ ?_ ?_)
    case main2 =>
      exact ⟨hsmall, hY⟩
    all_goals bound_norm_num [lowPass240Hz_f32]
  all_goals bound_norm_num [lowPass240Hz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at a
250 Hz cutoff. Their bits: `b0 = 0x39892E6C`, `b1 = 0x3A092E6C`, `b2 = 0x39892E6C`,
`a1 = 0xBFFA13BE`, `a2 = 0x3F746C14`. -/
noncomputable def lowPass250Hz_f32 : CoeffsReal where
  b0 := (2247579 / 2 ^ 33)
  b1 := (2247579 / 2 ^ 32)
  b2 := (2247579 / 2 ^ 33)
  a1 := -(8194527 / 2 ^ 22)
  a2 := (4004613 / 2 ^ 22)

/-- **The f32 bound at a 250 Hz cutoff.** For stored binary32 coefficients whose real values are
`lowPass250Hz_f32`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at most 0.979. -/
theorem lowPass250Hz_bound_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass250Hz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 0.979 := by
  refine (fun H => ?main) (block_bound_of_rat_f32 c _ hc s hs
    0.0226135163 0.0226135164 0.9771254481 (0.979)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, -, hX⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    exact ⟨hsmall, hX⟩
  all_goals bound_norm_num [lowPass250Hz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at a
20 kHz cutoff. Their bits: `b0 = 0x3F307642`, `b1 = 0x3FB07642`, `b2 = 0x3F307642`,
`a1 = 0x3FA3CAE4`, `a2 = 0x3EF4867C`. -/
noncomputable def lowPass20kHz_f32 : CoeffsReal where
  b0 := (5782305 / 2 ^ 23)
  b1 := (5782305 / 2 ^ 22)
  b2 := (5782305 / 2 ^ 23)
  a1 := (2683577 / 2 ^ 21)
  a2 := (4006303 / 2 ^ 23)

/-- **The f32 bound at a 20 kHz cutoff.** For stored binary32 coefficients whose real values are
`lowPass20kHz_f32`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at least 0.0127 and at most 0.0128, and `20·log₁₀` of it (the bound in decibels relative to
1.0) is at most −37.8. -/
theorem lowPass20kHz_bound_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass20kHz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        0.0127 ≤ C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 0.0128 ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s) ≤
          -37.8 := by
  refine (fun H => ?main) (block_bound_of_rat_f32 c _ hc s hs
    0.261200674 0.261200675 0.691077807 (0.0128)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine (fun hY => ?main2) (block_bound_ge_of_rat_f32 c _ hc s
      0.261200674 0.261200675 0.691077806 0.0127 h h1 hsmall ?_ ?_ ?_ ?_ ?_ ?_)
    case main2 =>
      refine ⟨hsmall, hY, hX, ?_⟩
      · exact (twenty_logb_le_of_pow_le _ _ 100 189 hpos hX (by norm_num)
          (by norm_num)).trans (by norm_num)
    all_goals bound_norm_num [lowPass20kHz_f32]
  all_goals bound_norm_num [lowPass20kHz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at a
21 kHz cutoff. Their bits: `b0 = 0x3F41CFA8`, `b1 = 0x3FC1CFA8`, `b2 = 0x3F41CFA8`,
`a1 = 0x3FBA248E`, `a2 = 0x3F12F583`. -/
noncomputable def lowPass21kHz_f32 : CoeffsReal where
  b0 := (1587701 / 2 ^ 21)
  b1 := (1587701 / 2 ^ 20)
  b2 := (1587701 / 2 ^ 21)
  a1 := (6099527 / 2 ^ 22)
  a2 := (9631107 / 2 ^ 24)

/-- **The f32 bound at a 21 kHz cutoff.** For stored binary32 coefficients whose real values are
`lowPass21kHz_f32`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at most 0.0346, and `20·log₁₀` of it (the bound in decibels relative to 1.0) is at most
−29.2. -/
theorem lowPass21kHz_bound_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass21kHz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 0.0346 ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s) ≤
          -29.2 := by
  refine (fun H => ?main) (block_bound_of_rat_f32 c _ hc s hs
    0.212966686 0.212966687 0.757666623 (0.0346)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, hpos, hX⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 50 73 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
  all_goals bound_norm_num [lowPass21kHz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section at a
23 kHz cutoff. Their bits: `b0 = 0x3F695DB2`, `b1 = 0x3FE95DB2`, `b2 = 0x3F695DB2`,
`a1 = 0x3FE85D0C`, `a2 = 0x3F54BCAF`. -/
noncomputable def lowPass23kHz_f32 : CoeffsReal where
  b0 := (7646937 / 2 ^ 23)
  b1 := (7646937 / 2 ^ 22)
  b2 := (7646937 / 2 ^ 23)
  a1 := (3807043 / 2 ^ 21)
  a2 := (13941935 / 2 ^ 24)

/-- **The f32 bound at a 23 kHz cutoff.** For stored binary32 coefficients whose real values are
`lowPass23kHz_f32`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`: they have
complex poles inside the unit circle, and for `complexPolesContraction` the condition
`cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the bound `cInf·Ê + L` on each output's
error is at least 1.13. -/
theorem lowPass23kHz_bound_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass23kHz_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : (realCoeffs_f32 c).a1 ^ 2 < 4 * (realCoeffs_f32 c).a2)
      (h1 : (realCoeffs_f32 c).a2 < 1),
      let C := complexPolesContraction (realCoeffs_f32 c) h h1
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        1.13 ≤ C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s := by
  refine (fun H => ?main) (block_bound_of_rat_f32 c _ hc s hs
    0.0844964427 0.0844964428 0.9115942536 (1.14)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, hsmall, -, -⟩ := H
    refine ⟨h, h1, ?_⟩
    intro C
    refine (fun hY => ?main2) (block_bound_ge_of_rat_f32 c _ hc s
      0.0844964427 0.0844964428 0.9115942535 1.13 h h1 hsmall ?_ ?_ ?_ ?_ ?_ ?_)
    case main2 =>
      exact ⟨hsmall, hY⟩
    all_goals bound_norm_num [lowPass23kHz_f32]
  all_goals bound_norm_num [lowPass23kHz_f32]

/-- The exact real values of the binary32 coefficients stored for the low-pass of this section
at a 1 Hz cutoff. Their bits: `b0 = 0x31932C2F`, `b1 = 0x32132C2F`, `b2 = 0x31932C2F`,
`a1 = 0xBFFFF9EF`, `a2 = 0x3F7FF3DE`. -/
noncomputable def lowPass1Hz_f32 : CoeffsReal where
  b0 := (9645103 / 2 ^ 51)
  b1 := (9645103 / 2 ^ 50)
  b2 := (9645103 / 2 ^ 51)
  a1 := -(16775663 / 2 ^ 23)
  a2 := (8387055 / 2 ^ 23)

/-- **At 1 Hz the f32 poles are real.** The coefficients `lowPass1Hz_f32` do not satisfy
`a1² < 4·a2`, so `complexPolesContraction` does not apply to them. -/
theorem lowPass1Hz_real_poles_f32 : ¬ lowPass1Hz_f32.a1 ^ 2 < 4 * lowPass1Hz_f32.a2 := by
  norm_num [lowPass1Hz_f32]

/-- **At 1 Hz the f32 coefficients have a pole at 1.** `1 + a1 + a2 = 0` for `lowPass1Hz_f32`, so
no `Contraction` exists for them (`isEmpty_contraction_of_pole_one`), and the whole-block
theorems give no bound there with any measure. -/
theorem lowPass1Hz_pole_one_f32 :
    1 + lowPass1Hz_f32.a1 + lowPass1Hz_f32.a2 = 0 ∧ IsEmpty (Contraction lowPass1Hz_f32) := by
  have h : 1 + lowPass1Hz_f32.a1 + lowPass1Hz_f32.a2 = 0 := by norm_num [lowPass1Hz_f32]
  exact ⟨h, isEmpty_contraction_of_pole_one _ h⟩

/-! ## RBJ low-pass examples with real poles, f32

Worked out outside Lean, not proved: for an RBJ-cookbook low-pass at 48 kHz with `Q < 1/2` the
poles are real and distinct, and with `Q = 1/2` they are equal in exact arithmetic. Each
`lowPass…_f32` below holds the exact real values of the stored coefficients at a 1 kHz cutoff.
Worked out outside Lean, not proved: they are what the computation of the section above gives
with `Q = 0.4` or `Q = 0.5` in place of `0.7071`, in binary64 and then each rounded to binary32.
`cos` and `sin` are outside the model. -/

/-- The exact real values of the binary32 coefficients stored for an RBJ low-pass with `Q = 0.4`
at a 1 kHz cutoff. Their bits: `b0 = 0x3B710308`, `b1 = 0x3BF10308`, `b2 = 0x3B710308`,
`a1 = 0xBFDA3527`, `a2 = 0x3F382E5A`. -/
noncomputable def lowPass1kHzQ04_f32 : CoeffsReal where
  b0 := (1974369 / 2 ^ 29)
  b1 := (1974369 / 2 ^ 28)
  b2 := (1974369 / 2 ^ 29)
  a1 := -(14300455 / 2 ^ 23)
  a2 := (6035245 / 2 ^ 23)

/-- **The f32 bound for a real-pole low-pass (`Q = 0.4`) at 1 kHz.** For stored binary32
coefficients whose real values are `lowPass1kHzQ04_f32`, `M = 1` (inputs at most 1 in size) and a
start of value `(0, 0)`: they have distinct real poles inside the unit circle, and for
`realPolesContraction` the condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the
bound `cInf·Ê + L` on each output's error is at most 0.00559, `20·log₁₀` of it (the bound in
decibels relative to 1.0) is at most −45, `Sb = computedStateBound_f32` is at most 2.75,
`V = stepValueBound_f32` is at most 56.3, and `V·10³⁵` is at most the largest finite binary32
value. -/
theorem lowPass1kHzQ04_bounds_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass1kHzQ04_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : 4 * (realCoeffs_f32 c).a2 < (realCoeffs_f32 c).a1 ^ 2)
      (h1 : (realCoeffs_f32 c).a2 < 1) (h2 : |(realCoeffs_f32 c).a1| < 1 + (realCoeffs_f32 c).a2),
      let C := realPolesContraction (realCoeffs_f32 c) h h1 h2
      C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 0.00559 ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s) ≤
          -45 ∧
        computedStateBound_f32 c C 1 s ≤ 2.75 ∧
        stepValueBound_f32 c C 1 s ≤ 56.3 ∧
        stepValueBound_f32 c C 1 s * 10 ^ 35 ≤ maxFinite_f32 := by
  refine (fun H => ?main) (realPolesContraction_block_bounds_of_rat_f32 c _ hc s hs
    0.16832568 0.16832569 (0.00559) 2.75 (56.3)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, h2, hsmall, hpos, hX, hSb, hV⟩ := H
    refine ⟨h, h1, h2, ?_⟩
    intro C
    refine ⟨hsmall, hX, ?_, hSb, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 4 9 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f32_eq]; norm_num)
  all_goals bound_norm_num [lowPass1kHzQ04_f32]

/-- The exact real values of the binary32 coefficients stored for an RBJ low-pass with `Q = 0.5`
at a 1 kHz cutoff. Their bits: `b0 = 0x3B77F7EA`, `b1 = 0x3BF7F7EA`, `b2 = 0x3B77F7EA`,
`a1 = 0xBFE08188`, `a2 = 0x3F44E2EF`. -/
noncomputable def lowPass1kHzQ05_f32 : CoeffsReal where
  b0 := (8125429 / 2 ^ 31)
  b1 := (8125429 / 2 ^ 30)
  b2 := (8125429 / 2 ^ 31)
  a1 := -(1839153 / 2 ^ 20)
  a2 := (12903151 / 2 ^ 24)

/-- **The f32 bound for a nearly repeated pole (`Q = 0.5`) at 1 kHz.** For stored binary32
coefficients whose real values are `lowPass1kHzQ05_f32`, `M = 1` (inputs at most 1 in size) and a
start of value `(0, 0)`: they have distinct real poles inside the unit circle (`a1² - 4·a2` is
positive but below 1.3 × 10⁻⁷, so `cInf = 1/d` is above 2700), and for `realPolesContraction` the
condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds and the bound `cInf·Ê + L` on each
output's error is at most 734. -/
theorem lowPass1kHzQ05_bound_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass1kHzQ05_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h : 4 * (realCoeffs_f32 c).a2 < (realCoeffs_f32 c).a1 ^ 2)
      (h1 : (realCoeffs_f32 c).a2 < 1) (h2 : |(realCoeffs_f32 c).a1| < 1 + (realCoeffs_f32 c).a2),
      let C := realPolesContraction (realCoeffs_f32 c) h h1 h2
      (realCoeffs_f32 c).a1 ^ 2 - 4 * (realCoeffs_f32 c).a2 < 1.3 * 10 ^ (-7 : ℤ) ∧
        2700 < C.cInf ∧
        C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 734 := by
  refine (fun H => ?main) (realPolesContraction_block_bounds_of_rat_f32 c _ hc s hs
    0.00035894 0.00035895 (734) 1418 (30029)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h, h1, h2, hsmall, -, hX, -, -⟩ := H
    have hd : (realCoeffs_f32 c).a1 ^ 2 - 4 * (realCoeffs_f32 c).a2 < 1.3 * 10 ^ (-7 : ℤ) := by
      rw [hc]; norm_num [lowPass1kHzQ05_f32]
    refine ⟨h, h1, h2, ?_⟩
    intro C
    obtain ⟨hci, -⟩ := realPolesContraction_bounds (realCoeffs_f32 c) h h1 h2
      (dl := 0.00035894) (du := 0.00035895) (by norm_num) (by norm_num)
      (by rw [hc]; norm_num [lowPass1kHzQ05_f32]) (by rw [hc]; norm_num [lowPass1kHzQ05_f32])
    exact ⟨hd, lt_of_lt_of_le (by norm_num) hci, hsmall, hX⟩
  all_goals bound_norm_num [lowPass1kHzQ05_f32]

/-- **The f32 bounds for a nearly repeated pole (`Q = 0.5`) at 1 kHz, with
`closePolesContraction`.** For stored binary32 coefficients whose real values are
`lowPass1kHzQ05_f32`, `M = 1` (inputs at most 1 in size) and a start of value `(0, 0)`, with
`ε = 0.06`: the condition `ρ < 1` of `closePolesContraction` holds, `cInf = 1/ε` is below 17, and
for this `Contraction` the condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems holds, the
bound `cInf·Ê + L` on each output's error is at most 0.0122, `20·log₁₀` of it (the bound in
decibels relative to 1.0) is at most −38, `Sb = computedStateBound_f32` is at most 4.01,
`V = stepValueBound_f32` is at most 85, and `V·10³⁵` is at most the largest finite binary32
value. With `realPolesContraction` the same bound is only shown to be at most 734
(`lowPass1kHzQ05_bound_f32`). -/
theorem lowPass1kHzQ05_bounds_f32 (c : CoeffsF32) (hc : realCoeffs_f32 c = lowPass1kHzQ05_f32)
    (s : StateF32) (hs : realState_f32 s = (0, 0)) :
    ∃ (h1 : |(realCoeffs_f32 c).a1| / 2 +
        max 0.06 (|(realCoeffs_f32 c).a1 ^ 2 / 4 - (realCoeffs_f32 c).a2| / 0.06) < 1),
      let C := closePolesContraction (realCoeffs_f32 c) (ε := 0.06) (by norm_num) h1
      C.cInf < 17 ∧
        C.cInf * C.K * roundGain (realCoeffs_f32 c) * localErrSlope_f32 c < 1 - C.ρ ∧
        C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s ≤ 0.0122 ∧
        20 * Real.logb 10 (C.cInf * stateErrBound_f32 c C 1 s + localErrBound_f32 c C 1 s) ≤
          -38 ∧
        computedStateBound_f32 c C 1 s ≤ 4.01 ∧
        stepValueBound_f32 c C 1 s ≤ 85 ∧
        stepValueBound_f32 c C 1 s * 10 ^ 35 ≤ maxFinite_f32 := by
  refine (fun H => ?main) (closePolesContraction_block_bounds_of_rat_f32 c _ hc s hs
    0.06 (1 / 10 ^ 7) (1839153 / 2 ^ 21 + 0.06) 0.0122 4.01 85 (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨h1, hsmall, hpos, hX, hSb, hV⟩ := H
    refine ⟨h1, ?_⟩
    intro C
    refine ⟨?_, hsmall, hX, ?_, hSb, hV, ?_⟩
    · show 1 / (0.06 : ℝ) < 17
      norm_num
    · exact (twenty_logb_le_of_pow_le _ _ 10 19 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f32_eq]; norm_num)
  all_goals bound_norm_num [lowPass1kHzQ05_f32]

end conjure_dsp_lib.biquad

end
