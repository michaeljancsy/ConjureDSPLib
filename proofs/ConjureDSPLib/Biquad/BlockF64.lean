module

public import ConjureDSPLib.Biquad.SpecF64
public import ConjureDSPLib.Biquad.Block
public import ConjureDSPLib.FloatFacts

/-!
# The biquad filter in f64 over a whole block

`process_f64_block_error`: when the Rust `process_f64` filters a block, given a `Contraction`
for the real values of the stored coefficients (see `Block.lean`), finite coefficients and
starting state, inputs at most `M`, no overflow and `cInf·K·κ·β < 1 − ρ`, every output and the
final state are within distances of the exact real-number filter `filt_real` that depend on the
coefficients, the `Contraction`, `M` and the starting state but not on the block length. A
`Contraction` for biquads with complex poles inside the unit circle is in
`Biquad/Contraction.lean`.

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
with
`β = localErrSlope_f64 c` and `κ = roundGain (realCoeffs_f64 c)`. If the coefficients and the
starting state are finite, no step overflows (`NoOverflow_f64`), and `cInf·K·κ·β < 1 − ρ`, then
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
never fails, the buffer it returns has one sample per exact output, each sample's real value is within
`cInf·Ê + L` of the corresponding output of `filt_real` (run on the real values of the inputs
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

end conjure_dsp_lib.biquad

end
