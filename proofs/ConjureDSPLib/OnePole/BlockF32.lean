module

public import ConjureDSPLib.OnePole.BridgeF32
public import ConjureDSPLib.OnePole.Block

/-!
# The one-pole filter in f32 over a whole block

`process_f32_block_error`: when the Rust `process_f32` filters a block with a stable
coefficient (with a little room for rounding) and no step overflows, every output sample and the
final state are within a fixed distance `E` of the exact real-number filter, for a block of any
length. `E` depends only on the input bound `M`, the coefficient, the starting state and
binary32's rounding constants.

`process_f32_block_error_of_inputs` gives the same bound with the no-overflow condition proved
from the inputs instead of assumed.

The last theorems are about inputs at most 1 in size and a start from 0: the f32 rows of the
one-pole table in `proofs/README.md` (`table_row_le_of_abs_le_*_f32`), and how `E` grows
as `|A|` approaches 1 (`errBound_between_of_abs_le_f32`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.one_pole

/-- No step overflows: running the filter from state `s` over the inputs, every input, every
product `a * state` and every new output is finite. -/
def NoOverflow_f32 (a : Float32) : Float32 → List Float32 → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (a * s).isFinite = true ∧ (x + a * s).isFinite = true ∧
      NoOverflow_f32 a (x + a * s) xs

/-- Without overflow, each step of `filt_f32` is within the per-step error `step_f32_error`. -/
theorem filt_f32_withinStepErr (a : Float32) (ha : a.isFinite = true) :
    ∀ (xs : List Float32) (s : Float32), s.isFinite = true → NoOverflow_f32 a s xs →
      WithinStepErr (real_f32 a) (Model.unitRoundoffAt FloatFormat.binary32)
        (Model.underflowErrorAt FloatFormat.binary32) (real_f32 s) (xs.map real_f32)
        (real_f32 (filt_f32 a s xs).1) ((filt_f32 a s xs).2.map real_f32) := by
  intro xs
  induction xs with
  | nil => intro s _ _; simp [filt_f32, WithinStepErr]
  | cons x xs ih =>
    intro s hs hno
    obtain ⟨hx, hp, hr, hrest⟩ := hno
    simp only [filt_f32, List.map_cons, WithinStepErr]
    exact ⟨step_f32_error a s x ha hs hx hp hr, ih (x + a * s) hr hrest⟩

/-- **Whole-block error of the f32 filter.** Let `A`, `S` and the inputs be the exact values of
`a`, the starting state and the samples, with every input at most `M` in size. If no step
overflows and `|A| + |A|·u·(2 + u) < 1` (`u = 2⁻²⁴`; this is `|A|·(1 + u)² < 1`, which any
`|A| ≤ 1 - 2⁻²²` satisfies), then every output of `filt_f32` and its
final state are within `E` of the exact real-number filter `filt_real`, where
`B = |S| + M / (1 - |A|)` and
`E = (u·M + η·(2 + u) + |A|·u·(2 + u)·B) / (1 - |A| - |A|·u·(2 + u))`. -/
theorem filt_f32_block_error (a s : Float32) (xs : List Float32) (M : ℝ)
    (ha : a.isFinite = true) (hs : s.isFinite = true) (hno : NoOverflow_f32 a s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f32 x| ≤ M)
    (hstab : |real_f32 a| + |real_f32 a| * Model.unitRoundoffAt FloatFormat.binary32 *
      (2 + Model.unitRoundoffAt FloatFormat.binary32) < 1) :
    let A := real_f32 a
    let S := real_f32 s
    let u := Model.unitRoundoffAt FloatFormat.binary32
    let η := Model.underflowErrorAt FloatFormat.binary32
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    List.Forall₂ (fun c e => |real_f32 c - e| ≤ E) (filt_f32 a s xs).2
        (filt_real A S (xs.map real_f32)).2 ∧
      |real_f32 (filt_f32 a s xs).1 - (filt_real A S (xs.map real_f32)).1| ≤ E := by
  intro A S u η B E
  have h := block_error_real A u η M S (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hM0 hstab (xs.map real_f32) _ _
    (by simpa using hM) (filt_f32_withinStepErr a ha xs s hs hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust `process_f32`.** Under the conditions of
`filt_f32_block_error`, `process_f32` never fails, and every sample it writes into the buffer,
and the state it leaves, are within `E` of the exact real-number filter. See
`process_f32_block_error_of_inputs` for a version whose conditions are on the inputs only. -/
theorem process_f32_block_error (a state : Float32) (buf : Slice Float32) (M : ℝ)
    (ha : a.isFinite = true) (hs : state.isFinite = true) (hno : NoOverflow_f32 a state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f32 x| ≤ M)
    (hstab : |real_f32 a| + |real_f32 a| * Model.unitRoundoffAt FloatFormat.binary32 *
      (2 + Model.unitRoundoffAt FloatFormat.binary32) < 1) :
    let A := real_f32 a
    let S := real_f32 state
    let u := Model.unitRoundoffAt FloatFormat.binary32
    let η := Model.underflowErrorAt FloatFormat.binary32
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    process_f32 a state buf ⦃ fun r =>
      List.Forall₂ (fun c e => |real_f32 c - e| ≤ E) r.2.val
          (filt_real A S (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real A S (buf.val.map real_f32)).1| ≤ E ⦄ := by
  intro A S u η B E
  have hblock := filt_f32_block_error a state buf.val M ha hs hno hM0 hM hstab
  apply WP.spec_mono (process_f32_spec a state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **No overflow, from the inputs alone.** Let `A` be the value of `a`, and `u`, `η` binary32's
rounding constants. Suppose `a` and every input are finite, every input is at most `M` in size,
`|A| ≤ 1`, and the bounds `B` and `E` satisfy the two inequalities of `block_step`. Start from
any finite state `s` within `E` of a real state `r` with `|r| ≤ B` (for the filter's own start,
`r` is the state's value). If `M + (1 + u)·(B + E) + η` is at most the largest finite binary32
value, then no step of the filter overflows. -/
theorem noOverflow_f32_of_inputs (a : Float32) (ha : a.isFinite = true) (M B E : ℝ)
    (hB : M + |real_f32 a| * B ≤ B)
    (hE : unitRoundoff_f32 * M + underflowErr_f32 * (2 + unitRoundoff_f32) +
        |real_f32 a| * unitRoundoff_f32 * (2 + unitRoundoff_f32) * (B + E) +
        |real_f32 a| * E ≤ E)
    (hA1 : |real_f32 a| ≤ 1)
    (hcap : M + (1 + unitRoundoff_f32) * (B + E) + underflowErr_f32 ≤ maxFinite_f32) :
    ∀ (xs : List Float32) (s : Float32) (r : ℝ), s.isFinite = true →
      (∀ x ∈ xs, x.isFinite = true ∧ |real_f32 x| ≤ M) →
      |real_f32 s - r| ≤ E → |r| ≤ B → NoOverflow_f32 a s xs := by
  have hu : 0 ≤ Model.unitRoundoffAt FloatFormat.binary32 := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ Model.underflowErrorAt FloatFormat.binary32 := (Model.underflowErrorAt_pos _).le
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hs hin hsr hr
    obtain ⟨hx, hxM⟩ := hin x (by simp)
    have hE0 : 0 ≤ E := (abs_nonneg _).trans hsr
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hr
    have hS : |real_f32 s| ≤ B + E := by
      calc |real_f32 s| = |(real_f32 s - r) + r| := by ring_nf
        _ ≤ |real_f32 s - r| + |r| := abs_add_le _ _
        _ ≤ B + E := by linarith
    have hAS : |real_f32 a * real_f32 s| ≤ B + E := by
      rw [abs_mul]
      calc |real_f32 a| * |real_f32 s| ≤ 1 * (B + E) :=
            mul_le_mul hA1 hS (abs_nonneg _) zero_le_one
        _ = B + E := one_mul _
    have hBEcap : B + E ≤ maxFinite_f32 := by
      have : B + E ≤ (1 + Model.unitRoundoffAt FloatFormat.binary32) * (B + E) := by nlinarith
      linarith [(abs_nonneg _).trans hxM]
    -- The product is finite, and its value is the exact product rounded once.
    have hp : (a * s).isFinite = true := isFinite_mul_f32 a s ha hs (hAS.trans hBEcap)
    have hP : |real_f32 (a * s)| ≤
        (1 + Model.unitRoundoffAt FloatFormat.binary32) * (B + E) +
          Model.underflowErrorAt FloatFormat.binary32 := by
      have hprod := isFinite_ofFloat32 _ hp
      have e : real_f32 (a * s) =
          Model.roundAt FloatFormat.binary32 (real_f32 a * real_f32 s) := by
        unfold real_f32
        rw [ofFloat32_mul_of_isFinite a s ha hs] at hprod ⊢
        rw [toReal_mul_eq_roundAt hprod]
        rfl
      rw [e]
      obtain ⟨δ, η1, h1, hd, he, -⟩ :=
        Model.roundAt_standardModel FloatFormat.binary32 (real_f32 a * real_f32 s)
      rw [h1]
      have k : |1 + δ| ≤ 1 + Model.unitRoundoffAt FloatFormat.binary32 :=
        (abs_add_le _ _).trans (by simpa using hd)
      calc |real_f32 a * real_f32 s * (1 + δ) + η1|
          ≤ |real_f32 a * real_f32 s| * |1 + δ| + |η1| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (B + E) * (1 + Model.unitRoundoffAt FloatFormat.binary32) +
              Model.underflowErrorAt FloatFormat.binary32 :=
            add_le_add (mul_le_mul hAS k (abs_nonneg _) (by linarith)) he
        _ = _ := by ring
    -- So the sum is finite too.
    have hsum : (x + a * s).isFinite = true := by
      refine isFinite_add_f32 x (a * s) hx hp ?_
      calc |real_f32 x + real_f32 (a * s)| ≤ |real_f32 x| + |real_f32 (a * s)| :=
            abs_add_le _ _
        _ ≤ M + ((1 + Model.unitRoundoffAt FloatFormat.binary32) * (B + E) +
              Model.underflowErrorAt FloatFormat.binary32) := add_le_add hxM hP
        _ ≤ maxFinite_f32 := by linarith
    -- The step is within its error bound, so both bounds carry on to the next step.
    obtain ⟨herr, hr'⟩ := block_step (real_f32 a) _ _ M B E (real_f32 x) (real_f32 s) r
      (real_f32 (x + a * s)) hu hB hE hxM hsr hr (step_f32_error a s x ha hs hx hp hsum)
    exact ⟨hx, hp, hsum, ih (x + a * s) _ hsum
      (fun z hz => hin z (List.mem_cons_of_mem _ hz)) herr hr'⟩

/-- **Whole-block error of `process_f32`, with conditions on the inputs only.** Let `A` and `S`
be the values of `a` and the starting state, and `u`, `η` binary32's rounding constants (as in
`filt_f32_block_error`). If `a`, the starting state and every sample in the buffer are finite,
every sample is at most `M` in size, `|A| + |A|·u·(2 + u) < 1`, and `M + (1 + u)·(B + E) + η` is
at most the largest finite binary32 value (about 3.4 × 10³⁸), then no step overflows,
`process_f32` never fails, and every sample it writes and the state it leaves are within `E` of
the exact real-number filter. `B` and `E` are `outBound` and `errBound`, the same as in
`process_f32_block_error`. -/
theorem process_f32_block_error_of_inputs (a state : Float32) (buf : Slice Float32) (M : ℝ)
    (ha : a.isFinite = true) (hs : state.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f32 x| ≤ M) (hM0 : 0 ≤ M)
    (hstab : |real_f32 a| + |real_f32 a| * unitRoundoff_f32 * (2 + unitRoundoff_f32) < 1)
    (hcap : M + (1 + unitRoundoff_f32) *
        (outBound (real_f32 a) M (real_f32 state) +
          errBound (real_f32 a) unitRoundoff_f32 underflowErr_f32 M (real_f32 state)) +
      underflowErr_f32 ≤ maxFinite_f32) :
    let E := errBound (real_f32 a) unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    NoOverflow_f32 a state buf.val ∧
      process_f32 a state buf ⦃ fun r =>
        List.Forall₂ (fun c e => |real_f32 c - e| ≤ E) r.2.val
          (filt_real (real_f32 a) (real_f32 state) (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real (real_f32 a) (real_f32 state) (buf.val.map real_f32)).1|
          ≤ E ⦄ := by
  intro E
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants (real_f32 a)
    (Model.unitRoundoffAt FloatFormat.binary32) (Model.underflowErrorAt FloatFormat.binary32)
    M (real_f32 state) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab
  have hA1 : |real_f32 a| ≤ 1 := by
    have : 0 ≤ |real_f32 a| * Model.unitRoundoffAt FloatFormat.binary32 *
        (2 + Model.unitRoundoffAt FloatFormat.binary32) := by
      have := (Model.unitRoundoffAt_pos FloatFormat.binary32).le
      positivity
    linarith
  have hno := noOverflow_f32_of_inputs a ha M _ _ hB hE hA1 hcap buf.val state (real_f32 state)
    hs hin (by simpa using hE0) hSB
  exact ⟨hno, process_f32_block_error a state buf M ha hs hno hM0
    (fun x hx => (hin x hx).2) hstab⟩

/-- **A simple sufficient condition for the stability condition, f32.** Every real `A` with
`|A| ≤ 1 - 2⁻²²` satisfies `|A| + |A|·u·(2 + u) < 1`, where `u` is binary32's unit roundoff. -/
theorem stability_of_abs_le_f32 (A : ℝ) (hA : |A| ≤ 1 - 2 ^ (-22 : ℤ)) :
    |A| + |A| * unitRoundoff_f32 * (2 + unitRoundoff_f32) < 1 := by
  rw [unitRoundoff_f32_eq]
  norm_num at hA ⊢
  nlinarith [abs_nonneg A]

-- The dB step checks a power of 10 with up to 1800 digits; norm_num needs a higher limit for that.
set_option exponentiation.threshold 4000 in
/-- **Row `a = 0.5` of the one-pole table in `proofs/README.md`, f32.** For every real `A` with
`|A| ≤ 0.5`, inputs at most `M = 1` in size and a starting state of value `S = 0`, in binary32: the
stability condition holds, `B ≤ 2`, `E ≤ 3.6 × 10⁻⁷`, `E / B ≤ 1.79 × 10⁻⁷` and
`20·log₁₀(E / B) ≤ −134.9`. `B` and `E` are `outBound` and `errBound`, `u` and `η` binary32's
rounding constants. f32 stores 0.5 exactly (0.5 is a power of 2). -/
theorem table_row_le_of_abs_le_05_f32 (A : ℝ) (hA : |A| ≤ 0.5) :
    |A| + |A| * unitRoundoff_f32 * (2 + unitRoundoff_f32) < 1 ∧
      outBound A 1 0 ≤ 2 ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 ≤ 3.6 * 10 ^ (-7 : ℤ) ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 / outBound A 1 0 ≤
        1.79 * 10 ^ (-7 : ℤ) ∧
      20 * Real.logb 10 (errBound A unitRoundoff_f32 underflowErr_f32 1 0 / outBound A 1 0) ≤
        -134.9 := by
  have hu : 0 < unitRoundoff_f32 := by rw [unitRoundoff_f32_eq]; positivity
  have hη : 0 ≤ underflowErr_f32 := underflowErr_f32_nonneg
  obtain ⟨hB, hE, hr, hdB⟩ := table_row_le_of_abs_le A 0.5 _ _ (2 ^ (-150 : ℤ)) 2
    (3.6 * 10 ^ (-7 : ℤ)) 179 9 200 1349 hu hη underflowErr_f32_eq.le hA
    (by rw [unitRoundoff_f32_eq]; norm_num) (by norm_num) (by norm_num)
    (by rw [unitRoundoff_f32_eq]; norm_num) (by rw [unitRoundoff_f32_eq]; norm_num) (by norm_num)
  exact ⟨stability_of_abs_le_f32 A (by norm_num; linarith), hB, hE, hr.trans (by norm_num),
    hdB.trans (by norm_num)⟩

set_option exponentiation.threshold 4000 in
/-- **Row `a = 0.99` of the one-pole table in `proofs/README.md`, f32.** For every real `A` with
`|A| ≤ 0.990001`, inputs at most `M = 1` in size and a starting state of value `S = 0`, in binary32:
the stability condition holds, `B ≤ 100.02`, `E ≤ 1.19 × 10⁻³`, `E / B ≤ 1.187 × 10⁻⁵` and
`20·log₁₀(E / B) ≤ −98.5`. `B` and `E` are `outBound` and `errBound`, `u` and `η` binary32's
rounding constants. The bound 0.990001 leaves room for 0.99 itself, which f32 stores as 0.9900000095
(worked out outside Lean, not proved). -/
theorem table_row_le_of_abs_le_099_f32 (A : ℝ) (hA : |A| ≤ 0.990001) :
    |A| + |A| * unitRoundoff_f32 * (2 + unitRoundoff_f32) < 1 ∧
      outBound A 1 0 ≤ 100.02 ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 ≤ 1.19 * 10 ^ (-3 : ℤ) ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 / outBound A 1 0 ≤
        1.187 * 10 ^ (-5 : ℤ) ∧
      20 * Real.logb 10 (errBound A unitRoundoff_f32 underflowErr_f32 1 0 / outBound A 1 0) ≤
        -98.5 := by
  have hu : 0 < unitRoundoff_f32 := by rw [unitRoundoff_f32_eq]; positivity
  have hη : 0 ≤ underflowErr_f32 := underflowErr_f32_nonneg
  obtain ⟨hB, hE, hr, hdB⟩ := table_row_le_of_abs_le A 0.990001 _ _ (2 ^ (-150 : ℤ)) 100.02
    (1.19 * 10 ^ (-3 : ℤ)) 1187 8 40 197 hu hη underflowErr_f32_eq.le hA
    (by rw [unitRoundoff_f32_eq]; norm_num) (by norm_num) (by norm_num)
    (by rw [unitRoundoff_f32_eq]; norm_num) (by rw [unitRoundoff_f32_eq]; norm_num) (by norm_num)
  exact ⟨stability_of_abs_le_f32 A (by norm_num; linarith), hB, hE, hr.trans (by norm_num),
    hdB.trans (by norm_num)⟩

set_option exponentiation.threshold 4000 in
/-- **Row `a = 0.999` of the one-pole table in `proofs/README.md`, f32.** For every real `A` with
`|A| ≤ 0.999001`, inputs at most `M = 1` in size and a starting state of value `S = 0`, in binary32:
the stability condition holds, `B ≤ 1001.01`, `E ≤ 0.12`, `E / B ≤ 1.193 × 10⁻⁴` and
`20·log₁₀(E / B) ≤ −78.4`. `B` and `E` are `outBound` and `errBound`, `u` and `η` binary32's
rounding constants. The bound 0.999001 leaves room for 0.999 itself, which f32 stores as
0.9990000129 (worked out outside Lean, not proved). -/
theorem table_row_le_of_abs_le_0999_f32 (A : ℝ) (hA : |A| ≤ 0.999001) :
    |A| + |A| * unitRoundoff_f32 * (2 + unitRoundoff_f32) < 1 ∧
      outBound A 1 0 ≤ 1001.01 ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 ≤ 0.12 ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 / outBound A 1 0 ≤
        1.193 * 10 ^ (-4 : ℤ) ∧
      20 * Real.logb 10 (errBound A unitRoundoff_f32 underflowErr_f32 1 0 / outBound A 1 0) ≤
        -78.4 := by
  have hu : 0 < unitRoundoff_f32 := by rw [unitRoundoff_f32_eq]; positivity
  have hη : 0 ≤ underflowErr_f32 := underflowErr_f32_nonneg
  obtain ⟨hB, hE, hr, hdB⟩ := table_row_le_of_abs_le A 0.999001 _ _ (2 ^ (-150 : ℤ)) 1001.01
    0.12 1193 7 25 98 hu hη underflowErr_f32_eq.le hA
    (by rw [unitRoundoff_f32_eq]; norm_num) (by norm_num) (by norm_num)
    (by rw [unitRoundoff_f32_eq]; norm_num) (by rw [unitRoundoff_f32_eq]; norm_num) (by norm_num)
  exact ⟨stability_of_abs_le_f32 A (by norm_num; linarith), hB, hE, hr.trans (by norm_num),
    hdB.trans (by norm_num)⟩

/-- **The size limit of `process_f32_block_error_of_inputs` holds for a slow smoother, f32.**
For every real `A` with `|A| ≤ 0.999001`, inputs at most `M = 1` in size and a
starting state of value `S = 0`, in binary32: the stability condition holds, `B ≤ 1001.01`,
`E ≤ 0.12`, and `M + (1 + u)·(B + E) + η` is at most the largest finite binary32 value. `B` and
`E` are `outBound` and `errBound`, `u` and `η` binary32's rounding constants. f32 only: it is
the tighter of the two precisions. The stability, `B` and `E` bounds come from
`table_row_le_of_abs_le_0999_f32`. -/
theorem block_constants_le_of_abs_le_f32 (A : ℝ) (hA : |A| ≤ 0.999001) :
    |A| + |A| * unitRoundoff_f32 * (2 + unitRoundoff_f32) < 1 ∧
      outBound A 1 0 ≤ 1001.01 ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 ≤ 0.12 ∧
      1 + (1 + unitRoundoff_f32) *
          (outBound A 1 0 + errBound A unitRoundoff_f32 underflowErr_f32 1 0) +
        underflowErr_f32 ≤ maxFinite_f32 := by
  obtain ⟨hstab, hB, hE, -, -⟩ := table_row_le_of_abs_le_0999_f32 A hA
  refine ⟨hstab, hB, hE, ?_⟩
  have hu0 : 0 ≤ unitRoundoff_f32 := by rw [unitRoundoff_f32_eq]; norm_num
  have hη0 : 0 ≤ underflowErr_f32 := by rw [underflowErr_f32_eq]; norm_num
  obtain ⟨hE0, hSB, -, -⟩ := block_constants A _ _ 1 0 hu0 hη0 zero_le_one hstab
  have hB0 : 0 ≤ outBound A 1 0 := (abs_nonneg _).trans hSB
  rw [maxFinite_f32_eq]
  have hu : unitRoundoff_f32 ≤ 1 := by rw [unitRoundoff_f32_eq]; norm_num
  have hη : underflowErr_f32 ≤ 1 := by rw [underflowErr_f32_eq]; norm_num
  nlinarith

/-- **How the f32 whole-block bound grows as `|A|` approaches 1.** For every real `A` with
`1/2 ≤ |A| ≤ 1 - 2⁻²⁰`, inputs at most `M = 1` in size and a starting state of value `S = 0`, in
binary32: `u / (1 - |A|)² ≤ E ≤ 3·u / (1 - |A|)²`, where `E` is `errBound` and `u = 2⁻²⁴`
binary32's unit roundoff. -/
theorem errBound_between_of_abs_le_f32 (A : ℝ) (hA1 : 1 / 2 ≤ |A|)
    (hA2 : |A| ≤ 1 - 2 ^ (-20 : ℤ)) :
    unitRoundoff_f32 / (1 - |A|) ^ 2 ≤ errBound A unitRoundoff_f32 underflowErr_f32 1 0 ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 ≤
        3 * unitRoundoff_f32 / (1 - |A|) ^ 2 :=
  errBound_between_of_abs_le A _ _ _ (by rw [unitRoundoff_f32_eq]; positivity)
    (by rw [unitRoundoff_f32_eq]; norm_num) underflowErr_f32_nonneg
    (by rw [unitRoundoff_f32_eq, underflowErr_f32_eq]; norm_num)
    (by rw [unitRoundoff_f32_eq]; norm_num) hA1 hA2

end conjure_dsp_lib.one_pole

end
