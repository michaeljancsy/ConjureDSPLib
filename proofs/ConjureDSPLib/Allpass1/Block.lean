module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring

/-!
# The first-order all-pass filter over a whole block: the real-number argument

Each floating-point step of the filter `y = c·(x - y1) + x1` is close to the exact step (the
per-step bounds in `BlockF64.lean` and `BlockF32.lean`). This file shows, on real numbers only,
that with `|C| < 1` (with a little room for rounding) those per-step errors do not pile up: over
a block of any length, every computed output stays within one fixed distance `E` of the exact
real-number filter's output.

The previous input `x1` is never rounded (it is a stored input), so only the previous output
`y1` carries an error from step to step, and each step multiplies that error by `C`: the
recursion is the one-pole filter's, with factor `|C|`, plus each step's own rounding.
-/

@[expose] public section

namespace conjure_dsp_lib.allpass1

/-- The filter in exact real arithmetic: run it over a list of inputs from the state
`(x1, y1)` (previous input, previous output), returning the final state and the outputs. -/
noncomputable def filt_real (C : ℝ) : ℝ × ℝ → List ℝ → (ℝ × ℝ) × List ℝ
  | s, [] => (s, [])
  | s, x :: xs =>
    let y := C * (x - s.2) + s.1
    let t := filt_real C (x, y) xs
    (t.1, y :: t.2)

/-- The per-step rounding bound of the unfused step `y = c·(x - y1) + x1`, with its three
roundings (the difference, the product and the sum), for exact values `C`, `x1`, `y1`, `x`, unit
roundoff `u` and underflow error `η`. With `D = x - y1`, `d = u·|D| + η` bounds the difference's
error and `p = u·|C|·(|D| + d) + η + |C|·d` the product's; the bound is
`u·(|C·D + x1| + p) + η + p`. -/
noncomputable def stepErr (C u η x1 y1 x : ℝ) : ℝ :=
  let D := x - y1
  let d := u * |D| + η
  let p := u * |C| * (|D| + d) + η + |C| * d
  u * (|C * D + x1| + p) + η + p

/-- `WithinStepErr C u η x1 y1 xs f ys`: starting from the computed state `(x1, y1)`, the
computed outputs `ys` and final state `f` come from the inputs `xs`, each output within
`stepErr` of the exact step taken from the previous computed state. The new previous input is
the input itself, unrounded. -/
def WithinStepErr (C u η : ℝ) : ℝ → ℝ → List ℝ → ℝ × ℝ → List ℝ → Prop
  | x1, y1, [], f, [] => f = (x1, y1)
  | x1, y1, x :: xs, f, y' :: ys =>
    |y' - (C * (x - y1) + x1)| ≤ stepErr C u η x1 y1 x ∧ WithinStepErr C u η x y' xs f ys
  | _, _, _, _, _ => False

/-- **From three roundings to `stepErr`.** If `rd` is within `u·|D| + η` of `D = x - y1` (the
rounded difference), `rp` within `u·|C·rd| + η` of `C·rd` (the rounded product) and `ry` within
`u·|rp + x1| + η` of `rp + x1` (the rounded sum), then `ry` is within `stepErr C u η x1 y1 x` of
the exact step `C·(x - y1) + x1`. -/
theorem stepErr_of_roundings (C u η x1 y1 x rd rp ry : ℝ) (hu : 0 ≤ u)
    (h1 : |rd - (x - y1)| ≤ u * |x - y1| + η) (h2 : |rp - C * rd| ≤ u * |C * rd| + η)
    (h3 : |ry - (rp + x1)| ≤ u * |rp + x1| + η) :
    |ry - (C * (x - y1) + x1)| ≤ stepErr C u η x1 y1 x := by
  have hC := abs_nonneg C
  set D := x - y1 with hDdef
  have hrd : |rd| ≤ |D| + (u * |D| + η) := by
    calc |rd| = |(rd - D) + D| := by ring_nf
      _ ≤ |rd - D| + |D| := abs_add_le _ _
      _ ≤ |D| + (u * |D| + η) := by linarith
  have hP : |rp - C * D| ≤ u * |C| * (|D| + (u * |D| + η)) + η + |C| * (u * |D| + η) := by
    have e : rp - C * D = (rp - C * rd) + C * (rd - D) := by ring
    rw [e]
    calc |(rp - C * rd) + C * (rd - D)| ≤ |rp - C * rd| + |C * (rd - D)| := abs_add_le _ _
      _ ≤ (u * |C * rd| + η) + |C| * (u * |D| + η) := by
        rw [abs_mul C (rd - D)]
        exact add_le_add h2 (mul_le_mul_of_nonneg_left h1 hC)
      _ ≤ u * |C| * (|D| + (u * |D| + η)) + η + |C| * (u * |D| + η) := by
        rw [abs_mul]
        have := mul_le_mul_of_nonneg_left hrd (mul_nonneg hu hC)
        nlinarith
  have hS : |rp + x1| ≤ |C * D + x1| +
      (u * |C| * (|D| + (u * |D| + η)) + η + |C| * (u * |D| + η)) := by
    calc |rp + x1| = |(rp - C * D) + (C * D + x1)| := by ring_nf
      _ ≤ |rp - C * D| + |C * D + x1| := abs_add_le _ _
      _ ≤ _ := by linarith
  unfold stepErr
  simp only [← hDdef]
  have e : ry - (C * D + x1) = (ry - (rp + x1)) + (rp - C * D) := by ring
  rw [e]
  calc |(ry - (rp + x1)) + (rp - C * D)| ≤ |ry - (rp + x1)| + |rp - C * D| := abs_add_le _ _
    _ ≤ (u * |rp + x1| + η) + |rp - C * D| := add_le_add h3 le_rfl
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hS hu
      linarith

/-- **The fused step is within the same bound.** If `rd` is within `u·|D| + η` of
`D = x - y1` and `ry` within `u·|C·rd + x1| + η` of `C·rd + x1` (one rounding of the fused
multiply-add), then `ry` is within `stepErr C u η x1 y1 x` of the exact step, the bound of the
unfused step. -/
theorem stepErr_of_roundings_fma (C u η x1 y1 x rd ry : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (h1 : |rd - (x - y1)| ≤ u * |x - y1| + η)
    (h2 : |ry - (C * rd + x1)| ≤ u * |C * rd + x1| + η) :
    |ry - (C * (x - y1) + x1)| ≤ stepErr C u η x1 y1 x := by
  have hC := abs_nonneg C
  set D := x - y1 with hDdef
  have hcd : |C * rd - C * D| ≤ |C| * (u * |D| + η) := by
    rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left h1 hC
  have hp0 : 0 ≤ u * |C| * (|D| + (u * |D| + η)) + η := by positivity
  have hS : |C * rd + x1| ≤ |C * D + x1| + |C| * (u * |D| + η) := by
    calc |C * rd + x1| = |(C * rd - C * D) + (C * D + x1)| := by ring_nf
      _ ≤ |C * rd - C * D| + |C * D + x1| := abs_add_le _ _
      _ ≤ _ := by linarith
  unfold stepErr
  simp only [← hDdef]
  have e : ry - (C * D + x1) = (ry - (C * rd + x1)) + (C * rd - C * D) := by ring
  rw [e]
  calc |(ry - (C * rd + x1)) + (C * rd - C * D)|
      ≤ |ry - (C * rd + x1)| + |C * rd - C * D| := abs_add_le _ _
    _ ≤ (u * (|C * D + x1| + |C| * (u * |D| + η)) + η) + |C| * (u * |D| + η) := by
      have := mul_le_mul_of_nonneg_left hS hu
      linarith
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hp0 hu
      nlinarith

/-- The growth of the rounding error with the state's size: `κ = |C|·u·(1 + (1 + u)·(2 + u))`. -/
noncomputable def errGrowth (C u : ℝ) : ℝ := |C| * u * (1 + (1 + u) * (2 + u))

/-- The part of one step's rounding bound that does not grow with the state:
`u·M + ((1 + u)·(1 + |C|·(1 + u)) + 1)·η`, for inputs at most `M` in size. -/
noncomputable def errBase (C u η M : ℝ) : ℝ := u * M + ((1 + u) * (1 + |C| * (1 + u)) + 1) * η

/-- `B`: when `|C| < 1`, a bound on the exact filter's outputs from a previous output `S`, with
inputs (the previous input included) at most `M` in size: `|S| + (1 + |C|)·M / (1 - |C|)`. -/
noncomputable def outBound (C M S : ℝ) : ℝ := |S| + (1 + |C|) * M / (1 - |C|)

/-- `E`: the whole-block error bound,
`(κ·(M + B) + errBase) / (1 - |C| - κ)` with `κ = errGrowth C u` and `B = outBound C M S`. -/
noncomputable def errBound (C u η M S : ℝ) : ℝ :=
  (errGrowth C u * (M + outBound C M S) + errBase C u η M) / (1 - |C| - errGrowth C u)

/-- **One step's rounding, bounded by the sizes.** If the inputs `x`, `x1` are at most `M` and
the previous output `y1` at most `W` in size, then `stepErr ≤ κ·(M + W) + errBase`. -/
theorem stepErr_le (C u η M W x1 y1 x : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hx : |x| ≤ M)
    (hx1 : |x1| ≤ M) (hy1 : |y1| ≤ W) :
    stepErr C u η x1 y1 x ≤ errGrowth C u * (M + W) + errBase C u η M := by
  have hC := abs_nonneg C
  have hD : |x - y1| ≤ M + W := (abs_sub _ _).trans (add_le_add hx hy1)
  have hA : |C * (x - y1) + x1| ≤ |C| * (M + W) + M := by
    calc |C * (x - y1) + x1| ≤ |C * (x - y1)| + |x1| := abs_add_le _ _
      _ = |C| * |x - y1| + |x1| := by rw [abs_mul]
      _ ≤ |C| * (M + W) + M := add_le_add (mul_le_mul_of_nonneg_left hD hC) hx1
  have hp : u * |C| * (|x - y1| + (u * |x - y1| + η)) + η + |C| * (u * |x - y1| + η) ≤
      u * |C| * ((M + W) + (u * (M + W) + η)) + η + |C| * (u * (M + W) + η) := by
    gcongr
  have hp0 : 0 ≤ u * |C| * (|x - y1| + (u * |x - y1| + η)) + η + |C| * (u * |x - y1| + η) := by
    positivity
  have key : stepErr C u η x1 y1 x ≤
      u * ((|C| * (M + W) + M) + (u * |C| * ((M + W) + (u * (M + W) + η)) + η +
        |C| * (u * (M + W) + η))) + η +
      (u * |C| * ((M + W) + (u * (M + W) + η)) + η + |C| * (u * (M + W) + η)) := by
    unfold stepErr
    simp only
    have := mul_le_mul_of_nonneg_left (add_le_add hA hp) hu
    linarith
  refine key.trans (le_of_eq ?_)
  unfold errGrowth errBase
  ring

/-- One step keeps both bounds: if the computed previous output `y1` is within `E` of the exact
one `r`, `|r| ≤ B`, both inputs are at most `M` in size, and the step's rounding is within
`stepErr`, then the new computed output is within `E` of the new exact output, which is at most
`B` in size. -/
theorem block_step (C u η M B E x1 x y1 r y' : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hB : (1 + |C|) * M + |C| * B ≤ B)
    (hE : errGrowth C u * (M + (B + E)) + errBase C u η M + |C| * E ≤ E)
    (hx : |x| ≤ M) (hx1 : |x1| ≤ M) (hyr : |y1 - r| ≤ E) (hr : |r| ≤ B)
    (hstep : |y' - (C * (x - y1) + x1)| ≤ stepErr C u η x1 y1 x) :
    |y' - (C * (x - r) + x1)| ≤ E ∧ |C * (x - r) + x1| ≤ B := by
  have hC := abs_nonneg C
  have hy : |y1| ≤ B + E := by
    calc |y1| = |(y1 - r) + r| := by ring_nf
      _ ≤ |y1 - r| + |r| := abs_add_le _ _
      _ ≤ B + E := by linarith
  have hs := stepErr_le C u η M (B + E) x1 y1 x hu hη hx hx1 hy
  constructor
  · -- The new error: this step's rounding plus the old error, multiplied by `-C`.
    have e : y' - (C * (x - r) + x1) = (y' - (C * (x - y1) + x1)) + C * (r - y1) := by ring
    rw [e]
    calc |(y' - (C * (x - y1) + x1)) + C * (r - y1)|
        ≤ |y' - (C * (x - y1) + x1)| + |C * (r - y1)| := abs_add_le _ _
      _ = |y' - (C * (x - y1) + x1)| + |C| * |y1 - r| := by rw [abs_mul, abs_sub_comm r]
      _ ≤ (errGrowth C u * (M + (B + E)) + errBase C u η M) + |C| * E :=
        add_le_add (hstep.trans hs) (mul_le_mul_of_nonneg_left hyr hC)
      _ ≤ E := hE
  · -- The exact filter stays within `B` (stability).
    calc |C * (x - r) + x1| ≤ |C * (x - r)| + |x1| := abs_add_le _ _
      _ = |C| * |x - r| + |x1| := by rw [abs_mul]
      _ ≤ |C| * (M + B) + M :=
        add_le_add (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hx hr)) hC) hx1
      _ = (1 + |C|) * M + |C| * B := by ring
      _ ≤ B := hB

/-- The induction behind `block_error_real`, with the bounds `B` (on the exact filter) and `E`
(on the error) as parameters satisfying the two inequalities that make them invariant. The
previous inputs of the computed and exact filters are equal throughout. -/
theorem block_error_core (C u η M B E : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hB : (1 + |C|) * M + |C| * B ≤ B)
    (hE : errGrowth C u * (M + (B + E)) + errBase C u η M + |C| * E ≤ E) :
    ∀ (xs : List ℝ) (x1 y1 r : ℝ) (f : ℝ × ℝ) (ys : List ℝ),
      |x1| ≤ M → (∀ x ∈ xs, |x| ≤ M) → |y1 - r| ≤ E → |r| ≤ B →
      WithinStepErr C u η x1 y1 xs f ys →
      List.Forall₂ (fun c e => |c - e| ≤ E) ys (filt_real C (x1, r) xs).2 ∧
        f.1 = (filt_real C (x1, r) xs).1.1 ∧ |f.2 - (filt_real C (x1, r) xs).1.2| ≤ E := by
  intro xs
  induction xs with
  | nil =>
    intro x1 y1 r f ys _ _ hyr _ hw
    cases ys with
    | nil =>
      simp only [WithinStepErr] at hw
      subst hw
      exact ⟨List.Forall₂.nil, rfl, hyr⟩
    | cons => simp [WithinStepErr] at hw
  | cons x xs ih =>
    intro x1 y1 r f ys hx1 hM hyr hr hw
    cases ys with
    | nil => simp [WithinStepErr] at hw
    | cons y' ys =>
      simp only [WithinStepErr] at hw
      obtain ⟨hstep, hrest⟩ := hw
      have hx := hM x (by simp)
      obtain ⟨herr, hr'⟩ :=
        block_step C u η M B E x1 x y1 r y' hu hη hB hE hx hx1 hyr hr hstep
      obtain ⟨h1, h2, h3⟩ := ih x y' (C * (x - r) + x1) f ys hx
        (fun z hz => hM z (List.mem_cons_of_mem _ hz)) herr hr' hrest
      exact ⟨List.Forall₂.cons herr h1, h2, h3⟩

/-- `B = outBound` and `E = errBound` satisfy what `block_step` needs: `E ≥ 0`, `|S| ≤ B`, and
the two inequalities. -/
theorem block_constants (C u η M S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hstab : |C| + errGrowth C u < 1) :
    let B := outBound C M S
    let E := errBound C u η M S
    0 ≤ E ∧ |S| ≤ B ∧ (1 + |C|) * M + |C| * B ≤ B ∧
      errGrowth C u * (M + (B + E)) + errBase C u η M + |C| * E ≤ E := by
  intro B E
  have hBdef : B = |S| + (1 + |C|) * M / (1 - |C|) := rfl
  have hEdef : E = (errGrowth C u * (M + B) + errBase C u η M) / (1 - |C| - errGrowth C u) := rfl
  have hC := abs_nonneg C
  have hκ : 0 ≤ errGrowth C u := by unfold errGrowth; positivity
  have hb : 0 ≤ errBase C u η M := by unfold errBase; positivity
  have hα : 0 < 1 - |C| := by linarith
  have hden : 0 < 1 - |C| - errGrowth C u := by linarith
  have hB0 : 0 ≤ (1 + |C|) * M / (1 - |C|) := div_nonneg (by positivity) hα.le
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hE0 : 0 ≤ E := by rw [hEdef]; exact div_nonneg (by positivity) hden.le
  have hB : (1 + |C|) * M + |C| * B ≤ B := by
    have : (1 + |C|) * M = (1 - |C|) * ((1 + |C|) * M / (1 - |C|)) := by field_simp
    rw [hBdef]
    nlinarith [abs_nonneg S]
  have hEeq : E * (1 - |C| - errGrowth C u) = errGrowth C u * (M + B) + errBase C u η M := by
    rw [hEdef]; exact div_mul_cancel₀ _ hden.ne'
  have hE : errGrowth C u * (M + (B + E)) + errBase C u η M + |C| * E ≤ E := by
    nlinarith [hEeq]
  exact ⟨hE0, by rw [hBdef]; linarith, hB, hE⟩

/-- **Whole-block error, on real numbers.** Suppose the inputs and the starting previous input
`x1` are at most `M` in size, the filter starts from previous output `S`, and each computed step
is within the per-step rounding bound of the exact step (`WithinStepErr`). If
`|C| + κ < 1` (stability, with room for rounding; `κ = errGrowth C u`), then every computed
output, and the final previous output, is within `E = errBound C u η M S` of the exact
real-number filter's, however long the block; the final previous input is the exact one. -/
theorem block_error_real (C u η M x1 S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hstab : |C| + errGrowth C u < 1) (xs : List ℝ) (f : ℝ × ℝ) (ys : List ℝ)
    (hx1 : |x1| ≤ M) (hM : ∀ x ∈ xs, |x| ≤ M) (hw : WithinStepErr C u η x1 S xs f ys) :
    let E := errBound C u η M S
    List.Forall₂ (fun c e => |c - e| ≤ E) ys (filt_real C (x1, S) xs).2 ∧
      f.1 = (filt_real C (x1, S) xs).1.1 ∧ |f.2 - (filt_real C (x1, S) xs).1.2| ≤ E := by
  intro E
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants C u η M S hu hη hM0 hstab
  have h0 : |S - S| ≤ E := by rw [sub_self, abs_zero]; exact hE0
  exact block_error_core C u η M (outBound C M S) E hu hη hB hE xs x1 S S f ys hx1 hM h0 hSB hw

/-- **Stability in exact arithmetic.** When `|C| < 1`: from the state `(x1, S)`, with the
starting previous input and every input at most `M ≥ 0` in size, every output of `filt_real` and
its final previous output are at most `outBound C M S = |S| + (1 + |C|)·M / (1 - |C|)` in size,
for a block of any length. -/
theorem filt_real_abs_le_outBound (C M x1 S : ℝ) (hC1 : |C| < 1) (hM0 : 0 ≤ M)
    (hx1 : |x1| ≤ M) (xs : List ℝ) (hM : ∀ x ∈ xs, |x| ≤ M) :
    (∀ y ∈ (filt_real C (x1, S) xs).2, |y| ≤ outBound C M S) ∧
      |(filt_real C (x1, S) xs).1.2| ≤ outBound C M S := by
  have hC := abs_nonneg C
  have hα : 0 < 1 - |C| := by linarith
  have hB : (1 + |C|) * M + |C| * outBound C M S ≤ outBound C M S := by
    have : (1 + |C|) * M = (1 - |C|) * ((1 + |C|) * M / (1 - |C|)) := by field_simp
    unfold outBound
    nlinarith [abs_nonneg S, div_nonneg (by positivity : 0 ≤ (1 + |C|) * M) hα.le]
  have hSB : |S| ≤ outBound C M S := by
    unfold outBound
    have := div_nonneg (by positivity : 0 ≤ (1 + |C|) * M) hα.le
    linarith
  -- Induction with any previous input at most `M` and previous output at most `B`.
  suffices h : ∀ (xs : List ℝ) (a r : ℝ), |a| ≤ M → (∀ x ∈ xs, |x| ≤ M) →
      |r| ≤ outBound C M S →
      (∀ y ∈ (filt_real C (a, r) xs).2, |y| ≤ outBound C M S) ∧
        |(filt_real C (a, r) xs).1.2| ≤ outBound C M S from h xs x1 S hx1 hM hSB
  intro xs
  induction xs with
  | nil => intro a r _ _ hr; simpa [filt_real] using hr
  | cons x xs ih =>
    intro a r ha hM hr
    have hx := hM x (by simp)
    have hy : |C * (x - r) + a| ≤ outBound C M S := by
      calc |C * (x - r) + a| ≤ |C * (x - r)| + |a| := abs_add_le _ _
        _ = |C| * |x - r| + |a| := by rw [abs_mul]
        _ ≤ |C| * (M + outBound C M S) + M :=
          add_le_add (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hx hr)) hC) ha
        _ = (1 + |C|) * M + |C| * outBound C M S := by ring
        _ ≤ outBound C M S := hB
    obtain ⟨h1, h2⟩ := ih x (C * (x - r) + a) hx (fun z hz => hM z (List.mem_cons_of_mem _ hz)) hy
    refine ⟨?_, h2⟩
    intro y hy'
    simp only [filt_real, List.mem_cons] at hy'
    rcases hy' with rfl | hy'
    · exact hy
    · exact h1 y hy'

end conjure_dsp_lib.allpass1

end
