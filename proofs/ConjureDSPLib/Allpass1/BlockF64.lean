module

public import ConjureDSPLib.Allpass1.SpecF64
public import ConjureDSPLib.Allpass1.Block
public import ConjureDSPLib.FloatFacts
public import ConjureDSPLib.FmaFacts

/-!
# The first-order all-pass filter in f64 over a whole block

`process_f64_block_error`: when the Rust `process_f64` filters a block with `|C| < 1` (with a
little room for rounding) and no step overflows, every output sample and the final previous
output are within a fixed distance `E` of the exact real-number filter, for a block of any
length; the final previous input is exactly the last input. `process_f64_block_error_of_inputs`
proves the no-overflow condition from the inputs instead. The fused functions meet the same
bounds (`process_fma_f64_block_error`, `process_fma_f64_block_error_of_inputs`).

Here `C` is the value of the stored `c`, the inputs are the values of the stored samples, and the
exact filter starts from the values of the stored state.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.allpass1

/-- The real values of a stored state, `(x1, y1)`. -/
noncomputable def realState_f64 (s : StateF64) : ℝ × ℝ := (real_f64 s.x1, real_f64 s.y1)

/-- **One step's rounding.** When `c`, the state, `x` and the step's three rounded results
(`x - y1`, `c * (x - y1)` and the output) are finite, the output of one step is within
`stepErr C u η X1 Y1 X` of the exact step `C·(X - Y1) + X1`, where `C`, `X1`, `Y1`, `X` are the
values of `c`, `s.x1`, `s.y1`, `x` and `u`, `η` binary64's rounding constants. -/
theorem apStep_f64_error (c : Float) (s : StateF64) (x : Float) (hc : c.isFinite = true)
    (hx1 : s.x1.isFinite = true) (hy1 : s.y1.isFinite = true) (hx : x.isFinite = true)
    (hd : (x - s.y1).isFinite = true) (hp : (c * (x - s.y1)).isFinite = true)
    (hr : (c * (x - s.y1) + s.x1).isFinite = true) :
    |real_f64 (apStep_f64 c s x).1 -
        (real_f64 c * (real_f64 x - real_f64 s.y1) + real_f64 s.x1)| ≤
      stepErr (real_f64 c) unitRoundoff_f64 underflowErr_f64 (real_f64 s.x1) (real_f64 s.y1)
        (real_f64 x) := by
  have e1 := abs_real_sub_sub_le_f64 x s.y1 hx hy1 hd
  have e2 := abs_real_mul_sub_le_f64 c (x - s.y1) hc hd hp
  have e3 := abs_real_add_sub_le_f64 (c * (x - s.y1)) s.x1 hp hx1 hr
  exact stepErr_of_roundings _ _ _ _ _ _ _ _ _ (Model.unitRoundoffAt_pos _).le e1 e2 e3

/-- No step overflows: running the filter from state `s` over the inputs, every input, every
difference `x - y1`, every product `c * (x - y1)` and every output is finite. -/
def NoOverflow_f64 (c : Float) : StateF64 → List Float → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (x - s.y1).isFinite = true ∧ (c * (x - s.y1)).isFinite = true ∧
      (c * (x - s.y1) + s.x1).isFinite = true ∧ NoOverflow_f64 c (apStep_f64 c s x).2 xs

/-- Without overflow, each step of `filt_f64` is within the per-step bound `stepErr`. -/
theorem filt_f64_withinStepErr (c : Float) (hc : c.isFinite = true) :
    ∀ (xs : List Float) (s : StateF64), s.x1.isFinite = true → s.y1.isFinite = true →
      NoOverflow_f64 c s xs →
      WithinStepErr (real_f64 c) unitRoundoff_f64 underflowErr_f64 (real_f64 s.x1)
        (real_f64 s.y1) (xs.map real_f64) (realState_f64 (filt_f64 c s xs).1)
        ((filt_f64 c s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _; simp [filt_f64, WithinStepErr, realState_f64]
  | cons x xs ih =>
    intro s hx1 hy1 hno
    obtain ⟨hx, hd, hp, hr, hrest⟩ := hno
    simp only [filt_f64, List.map_cons, WithinStepErr]
    have h := ih (apStep_f64 c s x).2 hx hr hrest
    have e1 : (apStep_f64 c s x).2.x1 = x := rfl
    have e2 : (apStep_f64 c s x).2.y1 = (apStep_f64 c s x).1 := rfl
    rw [e1, e2] at h
    exact ⟨apStep_f64_error c s x hc hx1 hy1 hx hd hp hr, h⟩

/-- **Whole-block error of the f64 filter.** Let `C`, `X1`, `S` and the inputs be the values of
`c`, the starting state's `x1` and `y1`, and the samples. If `c` and the starting state are
finite, no step overflows, `X1` and every input are at most `M ≥ 0` in size, and
`|C| + κ < 1` with `κ = errGrowth C u = |C|·u·(1 + (1 + u)·(2 + u))` and `u = 2⁻⁵³`, then every
output of `filt_f64` and the final `y1` are within `E = errBound C u η M S` of the exact filter
`filt_real C (X1, S)`, and the final `x1` is exactly its final previous input. -/
theorem filt_f64_block_error (c : Float) (s : StateF64) (xs : List Float) (M : ℝ)
    (hc : c.isFinite = true) (hx1 : s.x1.isFinite = true) (hy1 : s.y1.isFinite = true)
    (hno : NoOverflow_f64 c s xs) (hM0 : 0 ≤ M) (hX1 : |real_f64 s.x1| ≤ M)
    (hM : ∀ x ∈ xs, |real_f64 x| ≤ M)
    (hstab : |real_f64 c| + errGrowth (real_f64 c) unitRoundoff_f64 < 1) :
    let E := errBound (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 s.y1)
    let ex := filt_real (real_f64 c) (realState_f64 s) (xs.map real_f64)
    List.Forall₂ (fun y e => |real_f64 y - e| ≤ E) (filt_f64 c s xs).2 ex.2 ∧
      real_f64 (filt_f64 c s xs).1.x1 = ex.1.1 ∧
      |real_f64 (filt_f64 c s xs).1.y1 - ex.1.2| ≤ E := by
  intro E ex
  have h := block_error_real (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 s.x1)
    (real_f64 s.y1) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab
    (xs.map real_f64) _ _ hX1 (by simpa using hM) (filt_f64_withinStepErr c hc xs s hx1 hy1 hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2.1, h.2.2⟩

/-- **Whole-block error of the Rust `process_f64`.** Under the conditions of
`filt_f64_block_error`, `process_f64` never fails, every sample it writes is within `E` of the
exact filter's output, the state's `y1` it leaves is within `E` of the exact final previous
output, and its `x1` has exactly the exact final previous input's value. -/
theorem process_f64_block_error (c : Float) (state : StateF64) (buf : Slice Float) (M : ℝ)
    (hc : c.isFinite = true) (hx1 : state.x1.isFinite = true) (hy1 : state.y1.isFinite = true)
    (hno : NoOverflow_f64 c state buf.val) (hM0 : 0 ≤ M) (hX1 : |real_f64 state.x1| ≤ M)
    (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M)
    (hstab : |real_f64 c| + errGrowth (real_f64 c) unitRoundoff_f64 < 1) :
    let E := errBound (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 state.y1)
    let ex := filt_real (real_f64 c) (realState_f64 state) (buf.val.map real_f64)
    process_f64 c state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f64 y - e| ≤ E) r.2.val ex.2 ∧
        real_f64 r.1.x1 = ex.1.1 ∧ |real_f64 r.1.y1 - ex.1.2| ≤ E ⦄ := by
  intro E ex
  have hblock := filt_f64_block_error c state buf.val M hc hx1 hy1 hno hM0 hX1 hM hstab
  apply WP.spec_mono (process_f64_spec c state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **No overflow, from the inputs alone.** Let `C` be the value of `c`, and `u`, `η` binary64's
rounding constants. Suppose `c` is finite with `|C| ≤ 1`, the bounds `B` and `E` satisfy the two
inequalities of `block_step`, and `M + (1 + u)·((1 + u)·(M + B + E) + η) + η` is at most the
largest finite binary64 value. Then from any finite state whose `x1` is at most `M` in size and
whose `y1` is within `E` of a real `r` with `|r| ≤ B`, with every input finite and at most `M` in
size, no step of the filter overflows. -/
theorem noOverflow_f64_of_inputs (c : Float) (hc : c.isFinite = true) (M B E : ℝ)
    (hB : (1 + |real_f64 c|) * M + |real_f64 c| * B ≤ B)
    (hE : errGrowth (real_f64 c) unitRoundoff_f64 * (M + (B + E)) +
        errBase (real_f64 c) unitRoundoff_f64 underflowErr_f64 M + |real_f64 c| * E ≤ E)
    (hC1 : |real_f64 c| ≤ 1)
    (hcap : M + (1 + unitRoundoff_f64) * ((1 + unitRoundoff_f64) * (M + (B + E)) +
        underflowErr_f64) + underflowErr_f64 ≤ maxFinite_f64) :
    ∀ (xs : List Float) (s : StateF64) (r : ℝ), s.x1.isFinite = true → s.y1.isFinite = true →
      |real_f64 s.x1| ≤ M → (∀ x ∈ xs, x.isFinite = true ∧ |real_f64 x| ≤ M) →
      |real_f64 s.y1 - r| ≤ E → |r| ≤ B → NoOverflow_f64 c s xs := by
  have hu : 0 ≤ unitRoundoff_f64 := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ underflowErr_f64 := (Model.underflowErrorAt_pos _).le
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hx1 hy1 hX1 hin hsr hr
    obtain ⟨hx, hxM⟩ := hin x (by simp)
    have hE0 : 0 ≤ E := (abs_nonneg _).trans hsr
    have hY : |real_f64 s.y1| ≤ B + E := by
      calc |real_f64 s.y1| = |(real_f64 s.y1 - r) + r| := by ring_nf
        _ ≤ |real_f64 s.y1 - r| + |r| := abs_add_le _ _
        _ ≤ B + E := by linarith
    set G := M + (B + E) with hG
    have hG0 : 0 ≤ G := (abs_nonneg _).trans ((abs_sub _ _).trans (add_le_add hxM hY))
    have hcapG : (1 + unitRoundoff_f64) * G + underflowErr_f64 ≤ maxFinite_f64 := by
      have h1 : 0 ≤ M := (abs_nonneg _).trans hxM
      have : (1 + unitRoundoff_f64) * G + underflowErr_f64 ≤
          (1 + unitRoundoff_f64) * ((1 + unitRoundoff_f64) * G + underflowErr_f64) := by
        nlinarith [mul_nonneg hu (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + unitRoundoff_f64) hG0),
          mul_nonneg hu hη]
      linarith
    -- The difference is finite, and at most `(1 + u)·G + η` in size.
    have hD : |real_f64 x - real_f64 s.y1| ≤ G := (abs_sub _ _).trans (add_le_add hxM hY)
    have hd : (x - s.y1).isFinite = true :=
      isFinite_sub_f64 x s.y1 hx hy1 (hD.trans (by nlinarith))
    have hdv : |real_f64 (x - s.y1)| ≤ (1 + unitRoundoff_f64) * G + underflowErr_f64 := by
      have e := abs_real_sub_sub_le_f64 x s.y1 hx hy1 hd
      calc |real_f64 (x - s.y1)|
          = |(real_f64 (x - s.y1) - (real_f64 x - real_f64 s.y1)) +
              (real_f64 x - real_f64 s.y1)| := by ring_nf
        _ ≤ |real_f64 (x - s.y1) - (real_f64 x - real_f64 s.y1)| +
              |real_f64 x - real_f64 s.y1| := abs_add_le _ _
        _ ≤ (1 + unitRoundoff_f64) * G + underflowErr_f64 := by nlinarith
    -- The product is finite, and at most `(1 + u)·((1 + u)·G + η) + η` in size.
    have hCd : |real_f64 c * real_f64 (x - s.y1)| ≤ (1 + unitRoundoff_f64) * G + underflowErr_f64 := by
      rw [abs_mul]
      calc |real_f64 c| * |real_f64 (x - s.y1)| ≤ 1 * ((1 + unitRoundoff_f64) * G + underflowErr_f64) :=
            mul_le_mul hC1 hdv (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hp : (c * (x - s.y1)).isFinite = true :=
      isFinite_mul_f64 c (x - s.y1) hc hd (hCd.trans hcapG)
    have hpv : |real_f64 (c * (x - s.y1))| ≤
        (1 + unitRoundoff_f64) * ((1 + unitRoundoff_f64) * G + underflowErr_f64) +
          underflowErr_f64 := by
      have e := abs_real_mul_sub_le_f64 c (x - s.y1) hc hd hp
      calc |real_f64 (c * (x - s.y1))|
          = |(real_f64 (c * (x - s.y1)) - real_f64 c * real_f64 (x - s.y1)) +
              real_f64 c * real_f64 (x - s.y1)| := by ring_nf
        _ ≤ |real_f64 (c * (x - s.y1)) - real_f64 c * real_f64 (x - s.y1)| +
              |real_f64 c * real_f64 (x - s.y1)| := abs_add_le _ _
        _ ≤ _ := by nlinarith
    -- So the sum is finite too.
    have hsum : (c * (x - s.y1) + s.x1).isFinite = true := by
      refine isFinite_add_f64 _ _ hp hx1 ?_
      calc |real_f64 (c * (x - s.y1)) + real_f64 s.x1|
          ≤ |real_f64 (c * (x - s.y1))| + |real_f64 s.x1| := abs_add_le _ _
        _ ≤ maxFinite_f64 := by linarith
    -- The step is within its error bound, so both bounds carry on to the next step.
    obtain ⟨herr, hr'⟩ := block_step (real_f64 c) _ _ M B E (real_f64 s.x1) (real_f64 x)
      (real_f64 s.y1) r _ hu hη hB hE hxM hX1 hsr hr
      (apStep_f64_error c s x hc hx1 hy1 hx hd hp hsum)
    exact ⟨hx, hd, hp, hsum, ih (apStep_f64 c s x).2 _ hx hsum hxM
      (fun z hz => hin z (List.mem_cons_of_mem _ hz)) herr hr'⟩

/-- **Whole-block error of `process_f64`, with conditions on the inputs only.** Let `C`, `X1` and
`S` be the values of `c` and the starting state's `x1` and `y1`, and `u`, `η` binary64's rounding
constants. If `c`, the starting state and every sample are finite, `X1` and every sample are at
most `M ≥ 0` in size, `|C| + κ < 1` (`κ = errGrowth C u`), and
`M + (1 + u)·((1 + u)·(M + B + E) + η) + η` is at most the largest finite binary64 value (about
1.8 × 10³⁰⁸), with `B = outBound C M S` and `E = errBound C u η M S`, then no step overflows and
the conclusion of `process_f64_block_error` holds. -/
theorem process_f64_block_error_of_inputs (c : Float) (state : StateF64) (buf : Slice Float)
    (M : ℝ) (hc : c.isFinite = true) (hx1 : state.x1.isFinite = true)
    (hy1 : state.y1.isFinite = true) (hX1 : |real_f64 state.x1| ≤ M)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M)
    (hstab : |real_f64 c| + errGrowth (real_f64 c) unitRoundoff_f64 < 1)
    (hcap : M + (1 + unitRoundoff_f64) * ((1 + unitRoundoff_f64) *
        (M + (outBound (real_f64 c) M (real_f64 state.y1) +
          errBound (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 state.y1))) +
        underflowErr_f64) + underflowErr_f64 ≤ maxFinite_f64) :
    let E := errBound (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 state.y1)
    let ex := filt_real (real_f64 c) (realState_f64 state) (buf.val.map real_f64)
    NoOverflow_f64 c state buf.val ∧
      process_f64 c state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f64 y - e| ≤ E) r.2.val ex.2 ∧
          real_f64 r.1.x1 = ex.1.1 ∧ |real_f64 r.1.y1 - ex.1.2| ≤ E ⦄ := by
  intro E ex
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants (real_f64 c) unitRoundoff_f64 underflowErr_f64
    M (real_f64 state.y1) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0
    hstab
  have hC1 : |real_f64 c| ≤ 1 := by
    have : 0 ≤ errGrowth (real_f64 c) unitRoundoff_f64 := by
      unfold errGrowth
      have := (Model.unitRoundoffAt_pos FloatFormat.binary64).le
      positivity
    linarith
  have hno := noOverflow_f64_of_inputs c hc M _ _ hB hE hC1 hcap buf.val state
    (real_f64 state.y1) hx1 hy1 hX1 hin (by simpa using hE0) hSB
  exact ⟨hno, process_f64_block_error c state buf M hc hx1 hy1 hno hM0 hX1
    (fun x hx => (hin x hx).2) hstab⟩

/-! ## The fused functions -/

/-- **One fused step's rounding.** When `c`, the state, `x`, the rounded difference `x - y1` and
the output are finite, one fused step is within the unfused step's bound
`stepErr C u η X1 Y1 X` of the exact step. -/
theorem apStep_fma_f64_error (c : Float) (s : StateF64) (x : Float) (hc : c.isFinite = true)
    (hx1 : s.x1.isFinite = true) (hy1 : s.y1.isFinite = true) (hx : x.isFinite = true)
    (hd : (x - s.y1).isFinite = true) (hr : (c.fma (x - s.y1) s.x1).isFinite = true) :
    |real_f64 (apStep_fma_f64 c s x).1 -
        (real_f64 c * (real_f64 x - real_f64 s.y1) + real_f64 s.x1)| ≤
      stepErr (real_f64 c) unitRoundoff_f64 underflowErr_f64 (real_f64 s.x1) (real_f64 s.y1)
        (real_f64 x) := by
  have e1 := abs_real_sub_sub_le_f64 x s.y1 hx hy1 hd
  have e2 := abs_real_fma_sub_le_f64 c (x - s.y1) s.x1 hc hd hx1 hr
  exact stepErr_of_roundings_fma _ _ _ _ _ _ _ _ (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le e1 e2

/-- No fused step overflows: every input, every difference `x - y1` and every output is
finite. -/
def NoOverflowFma_f64 (c : Float) : StateF64 → List Float → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (x - s.y1).isFinite = true ∧ (c.fma (x - s.y1) s.x1).isFinite = true ∧
      NoOverflowFma_f64 c (apStep_fma_f64 c s x).2 xs

/-- Without overflow, each step of `filt_fma_f64` is within the per-step bound `stepErr`. -/
theorem filt_fma_f64_withinStepErr (c : Float) (hc : c.isFinite = true) :
    ∀ (xs : List Float) (s : StateF64), s.x1.isFinite = true → s.y1.isFinite = true →
      NoOverflowFma_f64 c s xs →
      WithinStepErr (real_f64 c) unitRoundoff_f64 underflowErr_f64 (real_f64 s.x1)
        (real_f64 s.y1) (xs.map real_f64) (realState_f64 (filt_fma_f64 c s xs).1)
        ((filt_fma_f64 c s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _; simp [filt_fma_f64, WithinStepErr, realState_f64]
  | cons x xs ih =>
    intro s hx1 hy1 hno
    obtain ⟨hx, hd, hr, hrest⟩ := hno
    simp only [filt_fma_f64, List.map_cons, WithinStepErr]
    have h := ih (apStep_fma_f64 c s x).2 hx hr hrest
    have e1 : (apStep_fma_f64 c s x).2.x1 = x := rfl
    have e2 : (apStep_fma_f64 c s x).2.y1 = (apStep_fma_f64 c s x).1 := rfl
    rw [e1, e2] at h
    exact ⟨apStep_fma_f64_error c s x hc hx1 hy1 hx hd hr, h⟩

/-- **Whole-block error of the fused Rust `process_fma_f64`.** The statement of
`process_f64_block_error`, with the same `E` and conditions, except that no fused step
overflows (`NoOverflowFma_f64`) in place of `NoOverflow_f64`. -/
theorem process_fma_f64_block_error (c : Float) (state : StateF64) (buf : Slice Float) (M : ℝ)
    (hc : c.isFinite = true) (hx1 : state.x1.isFinite = true) (hy1 : state.y1.isFinite = true)
    (hno : NoOverflowFma_f64 c state buf.val) (hM0 : 0 ≤ M) (hX1 : |real_f64 state.x1| ≤ M)
    (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M)
    (hstab : |real_f64 c| + errGrowth (real_f64 c) unitRoundoff_f64 < 1) :
    let E := errBound (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 state.y1)
    let ex := filt_real (real_f64 c) (realState_f64 state) (buf.val.map real_f64)
    process_fma_f64 c state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f64 y - e| ≤ E) r.2.val ex.2 ∧
        real_f64 r.1.x1 = ex.1.1 ∧ |real_f64 r.1.y1 - ex.1.2| ≤ E ⦄ := by
  intro E ex
  have h := block_error_real (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 state.x1)
    (real_f64 state.y1) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0
    hstab (buf.val.map real_f64) _ _ hX1 (by simpa using hM)
    (filt_fma_f64_withinStepErr c hc buf.val state hx1 hy1 hno)
  apply WP.spec_mono (process_fma_f64_spec c state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2.1, h.2.2⟩

/-- **No fused step overflows, from the inputs alone**, under the conditions of
`noOverflow_f64_of_inputs`. -/
theorem noOverflowFma_f64_of_inputs (c : Float) (hc : c.isFinite = true) (M B E : ℝ)
    (hB : (1 + |real_f64 c|) * M + |real_f64 c| * B ≤ B)
    (hE : errGrowth (real_f64 c) unitRoundoff_f64 * (M + (B + E)) +
        errBase (real_f64 c) unitRoundoff_f64 underflowErr_f64 M + |real_f64 c| * E ≤ E)
    (hC1 : |real_f64 c| ≤ 1)
    (hcap : M + (1 + unitRoundoff_f64) * ((1 + unitRoundoff_f64) * (M + (B + E)) +
        underflowErr_f64) + underflowErr_f64 ≤ maxFinite_f64) :
    ∀ (xs : List Float) (s : StateF64) (r : ℝ), s.x1.isFinite = true → s.y1.isFinite = true →
      |real_f64 s.x1| ≤ M → (∀ x ∈ xs, x.isFinite = true ∧ |real_f64 x| ≤ M) →
      |real_f64 s.y1 - r| ≤ E → |r| ≤ B → NoOverflowFma_f64 c s xs := by
  have hu : 0 ≤ unitRoundoff_f64 := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ underflowErr_f64 := (Model.underflowErrorAt_pos _).le
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hx1 hy1 hX1 hin hsr hr
    obtain ⟨hx, hxM⟩ := hin x (by simp)
    have hY : |real_f64 s.y1| ≤ B + E := by
      calc |real_f64 s.y1| = |(real_f64 s.y1 - r) + r| := by ring_nf
        _ ≤ |real_f64 s.y1 - r| + |r| := abs_add_le _ _
        _ ≤ B + E := by linarith
    set G := M + (B + E) with hG
    have hG0 : 0 ≤ G := (abs_nonneg _).trans ((abs_sub _ _).trans (add_le_add hxM hY))
    have hgrow : (1 + unitRoundoff_f64) * G + underflowErr_f64 ≤
        (1 + unitRoundoff_f64) * ((1 + unitRoundoff_f64) * G + underflowErr_f64) := by
      nlinarith [mul_nonneg hu (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + unitRoundoff_f64) hG0),
        mul_nonneg hu hη]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hxM
    have hcapG : (1 + unitRoundoff_f64) * G + underflowErr_f64 ≤ maxFinite_f64 := by linarith
    have hD : |real_f64 x - real_f64 s.y1| ≤ G := (abs_sub _ _).trans (add_le_add hxM hY)
    have hd : (x - s.y1).isFinite = true :=
      isFinite_sub_f64 x s.y1 hx hy1 (hD.trans (by nlinarith))
    have hdv : |real_f64 (x - s.y1)| ≤ (1 + unitRoundoff_f64) * G + underflowErr_f64 := by
      have e := abs_real_sub_sub_le_f64 x s.y1 hx hy1 hd
      calc |real_f64 (x - s.y1)|
          = |(real_f64 (x - s.y1) - (real_f64 x - real_f64 s.y1)) +
              (real_f64 x - real_f64 s.y1)| := by ring_nf
        _ ≤ |real_f64 (x - s.y1) - (real_f64 x - real_f64 s.y1)| +
              |real_f64 x - real_f64 s.y1| := abs_add_le _ _
        _ ≤ (1 + unitRoundoff_f64) * G + underflowErr_f64 := by nlinarith
    have hCd : |real_f64 c * real_f64 (x - s.y1)| ≤ (1 + unitRoundoff_f64) * G + underflowErr_f64 := by
      rw [abs_mul]
      calc |real_f64 c| * |real_f64 (x - s.y1)| ≤ 1 * ((1 + unitRoundoff_f64) * G + underflowErr_f64) :=
            mul_le_mul hC1 hdv (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hsum : (c.fma (x - s.y1) s.x1).isFinite = true := by
      refine isFinite_fma_f64 _ _ _ hc hd hx1 ?_
      calc |real_f64 c * real_f64 (x - s.y1) + real_f64 s.x1|
          ≤ |real_f64 c * real_f64 (x - s.y1)| + |real_f64 s.x1| := abs_add_le _ _
        _ ≤ maxFinite_f64 := by linarith
    obtain ⟨herr, hr'⟩ := block_step (real_f64 c) _ _ M B E (real_f64 s.x1) (real_f64 x)
      (real_f64 s.y1) r _ hu hη hB hE hxM hX1 hsr hr
      (apStep_fma_f64_error c s x hc hx1 hy1 hx hd hsum)
    exact ⟨hx, hd, hsum, ih (apStep_fma_f64 c s x).2 _ hx hsum hxM
      (fun z hz => hin z (List.mem_cons_of_mem _ hz)) herr hr'⟩

/-- **Whole-block error of `process_fma_f64`, with conditions on the inputs only**: exactly the
conditions of `process_f64_block_error_of_inputs`; no fused step overflows, and the conclusion
of `process_fma_f64_block_error` holds. -/
theorem process_fma_f64_block_error_of_inputs (c : Float) (state : StateF64)
    (buf : Slice Float) (M : ℝ) (hc : c.isFinite = true) (hx1 : state.x1.isFinite = true)
    (hy1 : state.y1.isFinite = true) (hX1 : |real_f64 state.x1| ≤ M)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M)
    (hstab : |real_f64 c| + errGrowth (real_f64 c) unitRoundoff_f64 < 1)
    (hcap : M + (1 + unitRoundoff_f64) * ((1 + unitRoundoff_f64) *
        (M + (outBound (real_f64 c) M (real_f64 state.y1) +
          errBound (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 state.y1))) +
        underflowErr_f64) + underflowErr_f64 ≤ maxFinite_f64) :
    let E := errBound (real_f64 c) unitRoundoff_f64 underflowErr_f64 M (real_f64 state.y1)
    let ex := filt_real (real_f64 c) (realState_f64 state) (buf.val.map real_f64)
    NoOverflowFma_f64 c state buf.val ∧
      process_fma_f64 c state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f64 y - e| ≤ E) r.2.val ex.2 ∧
          real_f64 r.1.x1 = ex.1.1 ∧ |real_f64 r.1.y1 - ex.1.2| ≤ E ⦄ := by
  intro E ex
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants (real_f64 c) unitRoundoff_f64 underflowErr_f64
    M (real_f64 state.y1) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0
    hstab
  have hC1 : |real_f64 c| ≤ 1 := by
    have : 0 ≤ errGrowth (real_f64 c) unitRoundoff_f64 := by
      unfold errGrowth
      have := (Model.unitRoundoffAt_pos FloatFormat.binary64).le
      positivity
    linarith
  have hno := noOverflowFma_f64_of_inputs c hc M _ _ hB hE hC1 hcap buf.val state
    (real_f64 state.y1) hx1 hy1 hX1 hin (by simpa using hE0) hSB
  exact ⟨hno, process_fma_f64_block_error c state buf M hc hx1 hy1 hno hM0 hX1
    (fun x hx => (hin x hx).2) hstab⟩

end conjure_dsp_lib.allpass1

end
