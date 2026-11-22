module

public import ConjureDSPLib.Biquad.SpecF64
public import ConjureDSPLib.Biquad.Block
public import ConjureDSPLib.FloatFacts

/-!
# The biquad filter in f64 over a whole block

`process_f64_block_error`: when the Rust `process_f64` filters a block and no step overflows,
every output sample and the final state are within fixed distances of the exact real-number
filter `filt_real`, for a block of any length. The bound is parametric in a `Contraction` for
the filter's coefficients (see `Block.lean`): one for typical filters is in
`Biquad/Contraction.lean`.

Each step rounds nine times (`tdf2_f64`); `tdf2_f64_localErr` bounds the effect of those
roundings on the step's output and new state by `α + β·Sb` when the state is at most `Sb` in
size, with `α = localErrBase_f64` and `β = localErrSlope_f64`. `block_error_real` in
`Block.lean` turns that into the whole-block bound.
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
    let C := realCoeffs_f64 c
    let L := localErrBase_f64 c M + localErrSlope_f64 c * Sb
    let Y := real_f64 (tdf2_f64 c s x).1
    |Y - (C.b0 * real_f64 x + real_f64 s.s1)| ≤ L ∧
      |real_f64 (tdf2_f64 c s x).2.s1 - (C.b1 * real_f64 x - C.a1 * Y + real_f64 s.s2)| ≤ L ∧
      |real_f64 (tdf2_f64 c s x).2.s2 - (C.b2 * real_f64 x - C.a2 * Y)| ≤ L := by
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

/-- Without overflow, every step of `filt_f64` (as real values) rounds within `α + β·Sb` while
its state is within `Sb`: the trajectory satisfies `LocalErrOK`, for every `Sb`. -/
theorem filt_f64_localErrOK (c : CoeffsF64) (hc : CoeffsFinite_f64 c) (Sb M : ℝ) :
    ∀ (xs : List Float) (s : StateF64), s.s1.isFinite = true → s.s2.isFinite = true →
      NoOverflow_f64 c s xs →
      LocalErrOK (realCoeffs_f64 c) Sb M (localErrBase_f64 c M + localErrSlope_f64 c * Sb)
        (realState_f64 s) (xs.map real_f64) (realState_f64 (filt_f64 c s xs).1)
        ((filt_f64 c s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _; simp [filt_f64, LocalErrOK, realState_f64]
  | cons x xs ih =>
    intro s hs1 hs2 hno
    obtain ⟨hstep, hrest⟩ := hno
    have ht1 : (tdf2_f64 c s x).2.s1.isFinite = true := hstep.2.2.2.2.2.2.1
    have ht2 : (tdf2_f64 c s x).2.s2.isFinite = true := hstep.2.2.2.2.2.2.2.2.2
    simp only [filt_f64, List.map_cons, realState_f64, LocalErrOK]
    exact ⟨_, _, fun h1 h2 hX => tdf2_f64_localErr c s x Sb M hc hs1 hs2 hstep h1 h2 hX,
      ih _ ht1 ht2 hrest⟩

/-- **Whole-block error of the f64 biquad.** Let `C` be a `Contraction` for the exact
coefficients, `S` the exact starting state and every input at most `M` in size, with
`α = localErrBase_f64 c M` and `β = localErrSlope_f64 c`. If the coefficients and the starting
state are finite, no step overflows, and `cInf·K·(2 + |A1| + |A2|)·β < 1 - ρ`, then every
output of `filt_f64` is within `cInf·Ê + L` of the exact filter `filt_real`'s output, and each
final state value within `cInf·Ê`, where `Ê = stateErrBound` and `L = stepRoundBound` (see
`Block.lean`). -/
theorem filt_f64_block_error (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c)) (s : StateF64)
    (xs : List Float) (M : ℝ) (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true)
    (hs2 : s.s2.isFinite = true) (hno : NoOverflow_f64 c s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f64 x| ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ) :
    let Ê := stateErrBound (realCoeffs_f64 c) C M (localErrBase_f64 c M) (localErrSlope_f64 c)
      (realState_f64 s)
    let L := stepRoundBound (realCoeffs_f64 c) C M (localErrBase_f64 c M) (localErrSlope_f64 c)
      (realState_f64 s)
    let F := filt_real (realCoeffs_f64 c) (realState_f64 s) (xs.map real_f64)
    List.Forall₂ (fun y e => |real_f64 y - e| ≤ C.cInf * Ê + L) (filt_f64 c s xs).2 F.2 ∧
      |real_f64 (filt_f64 c s xs).1.s1 - F.1.1| ≤ C.cInf * Ê ∧
      |real_f64 (filt_f64 c s xs).1.s2 - F.1.2| ≤ C.cInf * Ê := by
  intro Ê L F
  have h := block_error_real (realCoeffs_f64 c) C M _ _ hM0
    (localErrBase_nonneg _ (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0)
    (localErrSlope_nonneg _ (Model.unitRoundoffAt_pos _).le) hsmall (xs.map real_f64)
    (realState_f64 s) _ _ (by simpa using hM)
    (filt_f64_localErrOK c hc _ M xs s hs1 hs2 hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust biquad `process_f64`.** Under the conditions of
`filt_f64_block_error`, `process_f64` never fails, every sample it writes into the buffer is
within `cInf·Ê + L` of the exact real-number filter's output, and each value of the state it
leaves within `cInf·Ê`. -/
theorem process_f64_block_error (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hno : NoOverflow_f64 c state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ) :
    let Ê := stateErrBound (realCoeffs_f64 c) C M (localErrBase_f64 c M) (localErrSlope_f64 c)
      (realState_f64 state)
    let L := stepRoundBound (realCoeffs_f64 c) C M (localErrBase_f64 c M) (localErrSlope_f64 c)
      (realState_f64 state)
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

end conjure_dsp_lib.biquad

end
