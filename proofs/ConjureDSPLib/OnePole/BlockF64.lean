module

public import ConjureDSPLib.OnePole.BridgeF64
public import ConjureDSPLib.OnePole.Block

/-!
# The one-pole filter in f64 over a whole block

`process_f64_block_error`: when the Rust `process_f64` filters a block with a stable
coefficient (with a little room for rounding) and no step overflows, every output sample and the
final state are within a fixed distance `E` of the exact real-number filter, for a block of any
length. `E` depends only on the input bound `M`, the coefficient, the starting state and
binary64's rounding constants.

`process_f64_block_error_of_inputs` gives the same bound with the no-overflow condition proved
from the inputs instead of assumed.

The last theorems are about inputs at most 1 in size and a start from 0: the f64 rows of the
one-pole table in `proofs/README.md` (`table_row_le_of_abs_le_*_f64`), and how `E` grows
as `|A|` approaches 1 (`errBound_between_of_abs_le_f64`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.one_pole

/-- No step overflows: running the filter from state `s` over the inputs, every input, every
product `a * state` and every new output is finite. -/
def NoOverflow_f64 (a : Float) : Float → List Float → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (a * s).isFinite = true ∧ (x + a * s).isFinite = true ∧
      NoOverflow_f64 a (x + a * s) xs

/-- Without overflow, each step of `filt_f64` is within the per-step error `step_f64_error`. -/
theorem filt_f64_withinStepErr (a : Float) (ha : a.isFinite = true) :
    ∀ (xs : List Float) (s : Float), s.isFinite = true → NoOverflow_f64 a s xs →
      WithinStepErr (real_f64 a) (Model.unitRoundoffAt FloatFormat.binary64)
        (Model.underflowErrorAt FloatFormat.binary64) (real_f64 s) (xs.map real_f64)
        (real_f64 (filt_f64 a s xs).1) ((filt_f64 a s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _; simp [filt_f64, WithinStepErr]
  | cons x xs ih =>
    intro s hs hno
    obtain ⟨hx, hp, hr, hrest⟩ := hno
    simp only [filt_f64, List.map_cons, WithinStepErr]
    exact ⟨step_f64_error a s x ha hs hx hp hr, ih (x + a * s) hr hrest⟩

/-- **Whole-block error of the f64 filter.** Let `A`, `S` and the inputs be the exact values of
`a`, the starting state and the samples, with every input at most `M` in size. If no step
overflows and `|A| + |A|·u·(2 + u) < 1` (`u = 2⁻⁵³`; this is `|A|·(1 + u)² < 1`, which any
`|A| ≤ 1 - 2⁻⁵¹` satisfies), then every output of `filt_f64` and its
final state are within `E` of the exact real-number filter `filt_real`, where
`B = |S| + M / (1 - |A|)` and
`E = (u·M + η·(2 + u) + |A|·u·(2 + u)·B) / (1 - |A| - |A|·u·(2 + u))`. -/
theorem filt_f64_block_error (a s : Float) (xs : List Float) (M : ℝ)
    (ha : a.isFinite = true) (hs : s.isFinite = true) (hno : NoOverflow_f64 a s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f64 x| ≤ M)
    (hstab : |real_f64 a| + |real_f64 a| * Model.unitRoundoffAt FloatFormat.binary64 *
      (2 + Model.unitRoundoffAt FloatFormat.binary64) < 1) :
    let A := real_f64 a
    let S := real_f64 s
    let u := Model.unitRoundoffAt FloatFormat.binary64
    let η := Model.underflowErrorAt FloatFormat.binary64
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    List.Forall₂ (fun c e => |real_f64 c - e| ≤ E) (filt_f64 a s xs).2
        (filt_real A S (xs.map real_f64)).2 ∧
      |real_f64 (filt_f64 a s xs).1 - (filt_real A S (xs.map real_f64)).1| ≤ E := by
  intro A S u η B E
  have h := block_error_real A u η M S (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hM0 hstab (xs.map real_f64) _ _
    (by simpa using hM) (filt_f64_withinStepErr a ha xs s hs hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust `process_f64`.** Under the conditions of
`filt_f64_block_error`, `process_f64` never fails, and every sample it writes into the buffer,
and the state it leaves, are within `E` of the exact real-number filter. See
`process_f64_block_error_of_inputs` for a version whose conditions are on the inputs only. -/
theorem process_f64_block_error (a state : Float) (buf : Slice Float) (M : ℝ)
    (ha : a.isFinite = true) (hs : state.isFinite = true) (hno : NoOverflow_f64 a state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M)
    (hstab : |real_f64 a| + |real_f64 a| * Model.unitRoundoffAt FloatFormat.binary64 *
      (2 + Model.unitRoundoffAt FloatFormat.binary64) < 1) :
    let A := real_f64 a
    let S := real_f64 state
    let u := Model.unitRoundoffAt FloatFormat.binary64
    let η := Model.underflowErrorAt FloatFormat.binary64
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    process_f64 a state buf ⦃ fun r =>
      List.Forall₂ (fun c e => |real_f64 c - e| ≤ E) r.2.val
          (filt_real A S (buf.val.map real_f64)).2 ∧
        |real_f64 r.1 - (filt_real A S (buf.val.map real_f64)).1| ≤ E ⦄ := by
  intro A S u η B E
  have hblock := filt_f64_block_error a state buf.val M ha hs hno hM0 hM hstab
  apply WP.spec_mono (process_f64_spec a state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **No overflow, from the inputs alone.** Let `A` be the value of `a`, and `u`, `η` binary64's
rounding constants. Suppose `a` and every input are finite, every input is at most `M` in size,
`|A| ≤ 1`, and the bounds `B` and `E` satisfy the two inequalities of `block_step`. Start from
any finite state `s` within `E` of a real state `r` with `|r| ≤ B` (for the filter's own start,
`r` is the state's value). If `M + (1 + u)·(B + E) + η` is at most the largest finite binary64
value, then no step of the filter overflows. -/
theorem noOverflow_f64_of_inputs (a : Float) (ha : a.isFinite = true) (M B E : ℝ)
    (hB : M + |real_f64 a| * B ≤ B)
    (hE : unitRoundoff_f64 * M + underflowErr_f64 * (2 + unitRoundoff_f64) +
        |real_f64 a| * unitRoundoff_f64 * (2 + unitRoundoff_f64) * (B + E) +
        |real_f64 a| * E ≤ E)
    (hA1 : |real_f64 a| ≤ 1)
    (hcap : M + (1 + unitRoundoff_f64) * (B + E) + underflowErr_f64 ≤ maxFinite_f64) :
    ∀ (xs : List Float) (s : Float) (r : ℝ), s.isFinite = true →
      (∀ x ∈ xs, x.isFinite = true ∧ |real_f64 x| ≤ M) →
      |real_f64 s - r| ≤ E → |r| ≤ B → NoOverflow_f64 a s xs := by
  have hu : 0 ≤ Model.unitRoundoffAt FloatFormat.binary64 := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ Model.underflowErrorAt FloatFormat.binary64 := (Model.underflowErrorAt_pos _).le
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hs hin hsr hr
    obtain ⟨hx, hxM⟩ := hin x (by simp)
    have hE0 : 0 ≤ E := (abs_nonneg _).trans hsr
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hr
    have hS : |real_f64 s| ≤ B + E := by
      calc |real_f64 s| = |(real_f64 s - r) + r| := by ring_nf
        _ ≤ |real_f64 s - r| + |r| := abs_add_le _ _
        _ ≤ B + E := by linarith
    have hAS : |real_f64 a * real_f64 s| ≤ B + E := by
      rw [abs_mul]
      calc |real_f64 a| * |real_f64 s| ≤ 1 * (B + E) :=
            mul_le_mul hA1 hS (abs_nonneg _) zero_le_one
        _ = B + E := one_mul _
    have hBEcap : B + E ≤ maxFinite_f64 := by
      have : B + E ≤ (1 + Model.unitRoundoffAt FloatFormat.binary64) * (B + E) := by nlinarith
      linarith [(abs_nonneg _).trans hxM]
    -- The product is finite, and its value is the exact product rounded once.
    have hp : (a * s).isFinite = true := isFinite_mul_f64 a s ha hs (hAS.trans hBEcap)
    have hP : |real_f64 (a * s)| ≤
        (1 + Model.unitRoundoffAt FloatFormat.binary64) * (B + E) +
          Model.underflowErrorAt FloatFormat.binary64 := by
      have hprod := isFinite_ofFloat _ hp
      have e : real_f64 (a * s) =
          Model.roundAt FloatFormat.binary64 (real_f64 a * real_f64 s) := by
        unfold real_f64
        rw [ofFloat_mul_of_isFinite a s ha hs] at hprod ⊢
        rw [toReal_mul_eq_roundAt hprod]
        rfl
      rw [e]
      obtain ⟨δ, η1, h1, hd, he, -⟩ :=
        Model.roundAt_standardModel FloatFormat.binary64 (real_f64 a * real_f64 s)
      rw [h1]
      have k : |1 + δ| ≤ 1 + Model.unitRoundoffAt FloatFormat.binary64 :=
        (abs_add_le _ _).trans (by simpa using hd)
      calc |real_f64 a * real_f64 s * (1 + δ) + η1|
          ≤ |real_f64 a * real_f64 s| * |1 + δ| + |η1| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (B + E) * (1 + Model.unitRoundoffAt FloatFormat.binary64) +
              Model.underflowErrorAt FloatFormat.binary64 :=
            add_le_add (mul_le_mul hAS k (abs_nonneg _) (by linarith)) he
        _ = _ := by ring
    -- So the sum is finite too.
    have hsum : (x + a * s).isFinite = true := by
      refine isFinite_add_f64 x (a * s) hx hp ?_
      calc |real_f64 x + real_f64 (a * s)| ≤ |real_f64 x| + |real_f64 (a * s)| :=
            abs_add_le _ _
        _ ≤ M + ((1 + Model.unitRoundoffAt FloatFormat.binary64) * (B + E) +
              Model.underflowErrorAt FloatFormat.binary64) := add_le_add hxM hP
        _ ≤ maxFinite_f64 := by linarith
    -- The step is within its error bound, so both bounds carry on to the next step.
    obtain ⟨herr, hr'⟩ := block_step (real_f64 a) _ _ M B E (real_f64 x) (real_f64 s) r
      (real_f64 (x + a * s)) hu hB hE hxM hsr hr (step_f64_error a s x ha hs hx hp hsum)
    exact ⟨hx, hp, hsum, ih (x + a * s) _ hsum
      (fun z hz => hin z (List.mem_cons_of_mem _ hz)) herr hr'⟩

/-- **Whole-block error of `process_f64`, with conditions on the inputs only.** Let `A` and `S`
be the values of `a` and the starting state, and `u`, `η` binary64's rounding constants (as in
`filt_f64_block_error`). If `a`, the starting state and every sample in the buffer are finite,
every sample is at most `M` in size, `|A| + |A|·u·(2 + u) < 1`, and `M + (1 + u)·(B + E) + η` is
at most the largest finite binary64 value (about 1.8 × 10³⁰⁸), then no step overflows,
`process_f64` never fails, and every sample it writes and the state it leaves are within `E` of
the exact real-number filter. `B` and `E` are `outBound` and `errBound`, the same as in
`process_f64_block_error`. -/
theorem process_f64_block_error_of_inputs (a state : Float) (buf : Slice Float) (M : ℝ)
    (ha : a.isFinite = true) (hs : state.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M)
    (hstab : |real_f64 a| + |real_f64 a| * unitRoundoff_f64 * (2 + unitRoundoff_f64) < 1)
    (hcap : M + (1 + unitRoundoff_f64) *
        (outBound (real_f64 a) M (real_f64 state) +
          errBound (real_f64 a) unitRoundoff_f64 underflowErr_f64 M (real_f64 state)) +
      underflowErr_f64 ≤ maxFinite_f64) :
    let E := errBound (real_f64 a) unitRoundoff_f64 underflowErr_f64 M (real_f64 state)
    NoOverflow_f64 a state buf.val ∧
      process_f64 a state buf ⦃ fun r =>
        List.Forall₂ (fun c e => |real_f64 c - e| ≤ E) r.2.val
          (filt_real (real_f64 a) (real_f64 state) (buf.val.map real_f64)).2 ∧
        |real_f64 r.1 - (filt_real (real_f64 a) (real_f64 state) (buf.val.map real_f64)).1|
          ≤ E ⦄ := by
  intro E
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants (real_f64 a)
    (Model.unitRoundoffAt FloatFormat.binary64) (Model.underflowErrorAt FloatFormat.binary64)
    M (real_f64 state) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab
  have hA1 : |real_f64 a| ≤ 1 := by
    have : 0 ≤ |real_f64 a| * Model.unitRoundoffAt FloatFormat.binary64 *
        (2 + Model.unitRoundoffAt FloatFormat.binary64) := by
      have := (Model.unitRoundoffAt_pos FloatFormat.binary64).le
      positivity
    linarith
  have hno := noOverflow_f64_of_inputs a ha M _ _ hB hE hA1 hcap buf.val state (real_f64 state)
    hs hin (by simpa using hE0) hSB
  exact ⟨hno, process_f64_block_error a state buf M ha hs hno hM0
    (fun x hx => (hin x hx).2) hstab⟩

/-- **A simple sufficient condition for the stability condition, f64.** Every real `A` with
`|A| ≤ 1 - 2⁻⁵¹` satisfies `|A| + |A|·u·(2 + u) < 1`, where `u` is binary64's unit roundoff. -/
theorem stability_of_abs_le_f64 (A : ℝ) (hA : |A| ≤ 1 - 2 ^ (-51 : ℤ)) :
    |A| + |A| * unitRoundoff_f64 * (2 + unitRoundoff_f64) < 1 := by
  rw [unitRoundoff_f64_eq]
  norm_num at hA ⊢
  nlinarith [abs_nonneg A]

-- The dB step checks a power of 10 with up to 1800 digits; norm_num needs a higher limit for that.
set_option exponentiation.threshold 4000 in
/-- **Row `a = 0.99` of the one-pole table in `proofs/README.md`, f64.** For every real `A` with
`|A| ≤ 0.99`, inputs at most `M = 1` in size and a starting state of value `S = 0`, in binary64: the
stability condition holds, `B ≤ 100`, `E ≤ 2.21 × 10⁻¹²`, `E / B ≤ 2.21 × 10⁻¹⁴` and
`20·log₁₀(E / B) ≤ −273.1`. `B` and `E` are `outBound` and `errBound`, `u` and `η` binary64's
rounding constants. The bound 0.99 covers 0.99 itself, which f64 stores as 0.98999999999999999112,
just below 0.99 (worked out outside Lean, not proved). -/
theorem table_row_le_of_abs_le_099_f64 (A : ℝ) (hA : |A| ≤ 0.99) :
    |A| + |A| * unitRoundoff_f64 * (2 + unitRoundoff_f64) < 1 ∧
      outBound A 1 0 ≤ 100 ∧
      errBound A unitRoundoff_f64 underflowErr_f64 1 0 ≤ 2.21 * 10 ^ (-12 : ℤ) ∧
      errBound A unitRoundoff_f64 underflowErr_f64 1 0 / outBound A 1 0 ≤
        2.21 * 10 ^ (-14 : ℤ) ∧
      20 * Real.logb 10 (errBound A unitRoundoff_f64 underflowErr_f64 1 0 / outBound A 1 0) ≤
        -273.1 := by
  have hu : 0 < unitRoundoff_f64 := by rw [unitRoundoff_f64_eq]; positivity
  have hη : 0 ≤ underflowErr_f64 := underflowErr_f64_nonneg
  obtain ⟨hB, hE, hr, hdB⟩ := table_row_le_of_abs_le A 0.99 _ _ (2 ^ (-200 : ℤ)) 100
    (2.21 * 10 ^ (-12 : ℤ)) 221 16 200 2731 hu hη underflowErr_f64_le hA
    (by rw [unitRoundoff_f64_eq]; norm_num) (by norm_num) (by norm_num)
    (by rw [unitRoundoff_f64_eq]; norm_num) (by rw [unitRoundoff_f64_eq]; norm_num) (by norm_num)
  exact ⟨stability_of_abs_le_f64 A (by norm_num; linarith), hB, hE, hr.trans (by norm_num),
    hdB.trans (by norm_num)⟩

set_option exponentiation.threshold 4000 in
/-- **Row `a = 0.999` of the one-pole table in `proofs/README.md`, f64.** For every real `A` with
`|A| ≤ 0.999`, inputs at most `M = 1` in size and a starting state of value `S = 0`, in binary64:
the stability condition holds, `B ≤ 1000`, `E ≤ 2.22 × 10⁻¹⁰`, `E / B ≤ 2.22 × 10⁻¹³` and
`20·log₁₀(E / B) ≤ −253`. `B` and `E` are `outBound` and `errBound`, `u` and `η` binary64's rounding
constants. The bound 0.999 covers 0.999 itself, which f64 stores as 0.99899999999999999911, just
below 0.999 (worked out outside Lean, not proved). -/
theorem table_row_le_of_abs_le_0999_f64 (A : ℝ) (hA : |A| ≤ 0.999) :
    |A| + |A| * unitRoundoff_f64 * (2 + unitRoundoff_f64) < 1 ∧
      outBound A 1 0 ≤ 1000 ∧
      errBound A unitRoundoff_f64 underflowErr_f64 1 0 ≤ 2.22 * 10 ^ (-10 : ℤ) ∧
      errBound A unitRoundoff_f64 underflowErr_f64 1 0 / outBound A 1 0 ≤
        2.22 * 10 ^ (-13 : ℤ) ∧
      20 * Real.logb 10 (errBound A unitRoundoff_f64 underflowErr_f64 1 0 / outBound A 1 0) ≤
        -253 := by
  have hu : 0 < unitRoundoff_f64 := by rw [unitRoundoff_f64_eq]; positivity
  have hη : 0 ≤ underflowErr_f64 := underflowErr_f64_nonneg
  obtain ⟨hB, hE, hr, hdB⟩ := table_row_le_of_abs_le A 0.999 _ _ (2 ^ (-200 : ℤ)) 1000
    (2.22 * 10 ^ (-10 : ℤ)) 222 15 20 253 hu hη underflowErr_f64_le hA
    (by rw [unitRoundoff_f64_eq]; norm_num) (by norm_num) (by norm_num)
    (by rw [unitRoundoff_f64_eq]; norm_num) (by rw [unitRoundoff_f64_eq]; norm_num) (by norm_num)
  exact ⟨stability_of_abs_le_f64 A (by norm_num; linarith), hB, hE, hr.trans (by norm_num),
    hdB.trans (by norm_num)⟩

/-- **How the f64 whole-block bound grows as `|A|` approaches 1.** For every real `A` with
`1/2 ≤ |A| ≤ 1 - 2⁻⁴⁹`, inputs at most `M = 1` in size and a starting state of value `S = 0`, in
binary64: `u / (1 - |A|)² ≤ E ≤ 3·u / (1 - |A|)²`, where `E` is `errBound` and `u = 2⁻⁵³`
binary64's unit roundoff. -/
theorem errBound_between_of_abs_le_f64 (A : ℝ) (hA1 : 1 / 2 ≤ |A|)
    (hA2 : |A| ≤ 1 - 2 ^ (-49 : ℤ)) :
    unitRoundoff_f64 / (1 - |A|) ^ 2 ≤ errBound A unitRoundoff_f64 underflowErr_f64 1 0 ∧
      errBound A unitRoundoff_f64 underflowErr_f64 1 0 ≤
        3 * unitRoundoff_f64 / (1 - |A|) ^ 2 := by
  refine errBound_between_of_abs_le A _ _ _ (by rw [unitRoundoff_f64_eq]; positivity)
    (by rw [unitRoundoff_f64_eq]; norm_num) underflowErr_f64_nonneg ?_
    (by rw [unitRoundoff_f64_eq]; norm_num) hA1 hA2
  have hu : 0 ≤ unitRoundoff_f64 := by rw [unitRoundoff_f64_eq]; positivity
  calc underflowErr_f64 * (2 + unitRoundoff_f64) ≤ 2 ^ (-200 : ℤ) * (2 + unitRoundoff_f64) :=
        mul_le_mul_of_nonneg_right underflowErr_f64_le (by linarith)
    _ ≤ unitRoundoff_f64 / 100 := by rw [unitRoundoff_f64_eq]; norm_num

end conjure_dsp_lib.one_pole

end
