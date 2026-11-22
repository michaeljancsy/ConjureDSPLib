module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The one-pole filter over a whole block: the real-number argument

Each floating-point step of the filter `y = x + a * y_prev` is close to the exact step (the
per-step bounds in `BridgeF64.lean` and `BridgeF32.lean`, not imported here). This file shows,
on real numbers only, that with a stable coefficient (`|A| < 1`, with a little room to spare)
those per-step errors do not pile up: over a block of any length, every computed output stays
within one fixed distance `E` of the exact real-number filter's output.

It uses real numbers only, so it serves both precisions: `BlockF64.lean` and `BlockF32.lean`
apply it to the Rust functions. The last part bounds `B` and `E` for inputs at most 1 in size
and a starting state of 0: how they depend on `|A|`, and the tools for stating `E / B` in
decibels.
-/

@[expose] public section

namespace conjure_dsp_lib.one_pole

/-- The filter in exact real arithmetic: run it over a list of inputs from state `r`, returning
the final state and the list of outputs. -/
noncomputable def filt_real (A : ℝ) : ℝ → List ℝ → ℝ × List ℝ
  | r, [] => (r, [])
  | r, x :: xs =>
    let y := x + A * r
    let t := filt_real A y xs
    (t.1, y :: t.2)

/-- The per-step error bound of `step_f64_error` / `step_f32_error`, for state `y` (the previous
output) and input `x`, with unit roundoff `u` and underflow error `η`. It must stay exactly the
right-hand side of those theorems: `filt_f64_withinStepErr` and `filt_f32_withinStepErr` check
that it does. -/
def stepErr (A u η y x : ℝ) : ℝ :=
  |x + A * y| * u + (|A * y| * u + η) * (1 + u) + η

/-- `WithinStepErr A u η y xs f ys`: starting from state `y` (the previous output), the
computed outputs `ys` and final state `f` come from inputs `xs`, each step within `stepErr` of
the exact step taken from the previous computed output. -/
def WithinStepErr (A u η : ℝ) : ℝ → List ℝ → ℝ → List ℝ → Prop
  | y, [], f, [] => f = y
  | y, x :: xs, f, y' :: ys =>
    |y' - (x + A * y)| ≤ stepErr A u η y x ∧ WithinStepErr A u η y' xs f ys
  | _, _, _, _ => False

/-- One step keeps both bounds: if the computed state `y` is within `E` of the exact state `r`,
`|r| ≤ B`, the input is at most `M` in size, and the step's rounding is within `stepErr`, then the
new computed state `y'` is within `E` of the new exact state, which is at most `B` in size. -/
theorem block_step (A u η M B E x y r y' : ℝ) (hu : 0 ≤ u) (hB : M + |A| * B ≤ B)
    (hE : u * M + η * (2 + u) + |A| * u * (2 + u) * (B + E) + |A| * E ≤ E)
    (hx : |x| ≤ M) (hyr : |y - r| ≤ E) (hr : |r| ≤ B)
    (hstep : |y' - (x + A * y)| ≤ stepErr A u η y x) :
    |y' - (x + A * r)| ≤ E ∧ |x + A * r| ≤ B := by
  have hA := abs_nonneg A
  have hy : |y| ≤ B + E := by
    calc |y| = |(y - r) + r| := by ring_nf
      _ ≤ |y - r| + |r| := abs_add_le _ _
      _ ≤ B + E := by linarith
  -- One step's rounding error, bounded using |x| ≤ M and |y| ≤ B + E.
  have hs : stepErr A u η y x ≤ u * M + η * (2 + u) + |A| * u * (2 + u) * (B + E) := by
    unfold stepErr
    have h1 : |x + A * y| ≤ M + |A| * (B + E) := by
      calc |x + A * y| ≤ |x| + |A * y| := abs_add_le _ _
        _ = |x| + |A| * |y| := by rw [abs_mul]
        _ ≤ M + |A| * (B + E) := add_le_add hx (mul_le_mul_of_nonneg_left hy hA)
    have h2 : |A * y| ≤ |A| * (B + E) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy hA
    have k1 := mul_le_mul_of_nonneg_right h1 hu
    have k2 := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ u * (1 + u))
    nlinarith [k1, k2]
  constructor
  · -- The new error: this step's rounding plus the old error, shrunk by |A|.
    have e : y' - (x + A * r) = (y' - (x + A * y)) + A * (y - r) := by ring
    rw [e]
    calc |(y' - (x + A * y)) + A * (y - r)|
        ≤ |y' - (x + A * y)| + |A * (y - r)| := abs_add_le _ _
      _ = |y' - (x + A * y)| + |A| * |y - r| := by rw [abs_mul]
      _ ≤ (u * M + η * (2 + u) + |A| * u * (2 + u) * (B + E)) + |A| * E :=
        add_le_add (hstep.trans hs) (mul_le_mul_of_nonneg_left hyr hA)
      _ ≤ E := hE
  · -- The exact filter stays within B (stability).
    calc |x + A * r| ≤ |x| + |A * r| := abs_add_le _ _
      _ = |x| + |A| * |r| := by rw [abs_mul]
      _ ≤ M + |A| * B := add_le_add hx (mul_le_mul_of_nonneg_left hr hA)
      _ ≤ B := hB

/-- The induction behind `block_error_real` (its auxiliary lemma), with the bounds `B` (on the
exact filter) and `E` (on the error) as parameters satisfying the two inequalities that make
them invariant. -/
theorem block_error_core (A u η M B E : ℝ) (hu : 0 ≤ u) (hB : M + |A| * B ≤ B)
    (hE : u * M + η * (2 + u) + |A| * u * (2 + u) * (B + E) + |A| * E ≤ E) :
    ∀ (xs : List ℝ) (y r f : ℝ) (ys : List ℝ),
      (∀ x ∈ xs, |x| ≤ M) → |y - r| ≤ E → |r| ≤ B → WithinStepErr A u η y xs f ys →
      List.Forall₂ (fun c e => |c - e| ≤ E) ys (filt_real A r xs).2 ∧
        |f - (filt_real A r xs).1| ≤ E := by
  intro xs
  induction xs with
  | nil =>
    intro y r f ys _ hyr _ hw
    cases ys with
    | nil =>
      simp only [WithinStepErr] at hw
      subst hw
      exact ⟨List.Forall₂.nil, hyr⟩
    | cons => simp [WithinStepErr] at hw
  | cons x xs ih =>
    intro y r f ys hM hyr hr hw
    cases ys with
    | nil => simp [WithinStepErr] at hw
    | cons y' ys =>
      simp only [WithinStepErr] at hw
      obtain ⟨hstep, hrest⟩ := hw
      obtain ⟨herr, hr'⟩ :=
        block_step A u η M B E x y r y' hu hB hE (hM x (by simp)) hyr hr hstep
      obtain ⟨h1, h2⟩ :=
        ih y' (x + A * r) f ys (fun z hz => hM z (List.mem_cons_of_mem _ hz)) herr hr' hrest
      exact ⟨List.Forall₂.cons herr h1, h2⟩

/-- `B` of `block_error_real` (and of `filt_f64_block_error`, `process_f64_block_error` and the
f32 versions): when `|A| < 1`, a bound on the exact filter's outputs from state `S` with inputs at
most `M` in size. -/
noncomputable def outBound (A M S : ℝ) : ℝ := |S| + M / (1 - |A|)

/-- `E` of `block_error_real` (and of `filt_f64_block_error`, `process_f64_block_error` and the
f32 versions): the whole-block error bound. -/
noncomputable def errBound (A u η M S : ℝ) : ℝ :=
  (u * M + η * (2 + u) + |A| * u * (2 + u) * outBound A M S) / (1 - |A| - |A| * u * (2 + u))

/-- `B = outBound` and `E = errBound` satisfy what `block_step` needs: `E ≥ 0`, `|S| ≤ B`, and
the two inequalities. -/
theorem block_constants (A u η M S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hstab : |A| + |A| * u * (2 + u) < 1) :
    let B := outBound A M S
    let E := errBound A u η M S
    0 ≤ E ∧ |S| ≤ B ∧ M + |A| * B ≤ B ∧
      u * M + η * (2 + u) + |A| * u * (2 + u) * (B + E) + |A| * E ≤ E := by
  intro B E
  have hBdef : B = |S| + M / (1 - |A|) := rfl
  have hEdef : E = (u * M + η * (2 + u) + |A| * u * (2 + u) * B) /
      (1 - |A| - |A| * u * (2 + u)) := rfl
  have hA := abs_nonneg A
  have hκ : 0 ≤ |A| * u * (2 + u) := by positivity
  have hα : 0 < 1 - |A| := by linarith
  have hden : 0 < 1 - |A| - |A| * u * (2 + u) := by linarith
  have hB0 : 0 ≤ M / (1 - |A|) := div_nonneg hM0 hα.le
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hE0 : 0 ≤ E := by rw [hEdef]; exact div_nonneg (by positivity) hden.le
  have hB : M + |A| * B ≤ B := by
    have : M = (1 - |A|) * (M / (1 - |A|)) := by field_simp
    rw [hBdef]
    nlinarith [abs_nonneg S]
  have hEeq : E * (1 - |A| - |A| * u * (2 + u)) =
      u * M + η * (2 + u) + |A| * u * (2 + u) * B := by
    rw [hEdef]; exact div_mul_cancel₀ _ hden.ne'
  have hE : u * M + η * (2 + u) + |A| * u * (2 + u) * (B + E) + |A| * E ≤ E := by
    nlinarith [hEeq]
  exact ⟨hE0, by rw [hBdef]; linarith, hB, hE⟩

/-- **Whole-block error, on real numbers.** Suppose the inputs are bounded by `M`, the filter
starts from state `S`, and each computed step is within the per-step rounding error of the exact
step (`WithinStepErr`). If `|A| + |A|·u·(2 + u) < 1` (stability, with room for rounding), then
every computed output, and the final state, is within

`E = (u·M + η·(2 + u) + |A|·u·(2 + u)·B) / (1 - |A| - |A|·u·(2 + u))`

of the exact real-number filter's, however long the block, where `B = |S| + M / (1 - |A|)`
bounds the exact filter's outputs. (`B` and `E` are `outBound` and `errBound`.) -/
theorem block_error_real (A u η M S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hstab : |A| + |A| * u * (2 + u) < 1) (xs : List ℝ) (f : ℝ) (ys : List ℝ)
    (hM : ∀ x ∈ xs, |x| ≤ M) (hw : WithinStepErr A u η S xs f ys) :
    let E := errBound A u η M S
    List.Forall₂ (fun c e => |c - e| ≤ E) ys (filt_real A S xs).2 ∧
      |f - (filt_real A S xs).1| ≤ E := by
  intro E
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants A u η M S hu hη hM0 hstab
  have h0 : |S - S| ≤ E := by rw [sub_self, abs_zero]; exact hE0
  exact block_error_core A u η M (outBound A M S) E hu hB hE xs S S f ys hM h0 hSB hw

/-! ## The bounds for inputs at most 1 and a start from 0 -/

/-- **`B`, `E` and `E / B` grow with `|A|`.** For inputs at most `M = 1` in size and a starting
state `S = 0`, if `|A| ≤ a` and `a + a·u·(2 + u) < 1`, then `B = outBound A 1 0` is at most
`1 / (1 - a)`, `E = errBound A u η 1 0` is at most its value at `|A| = a`, written out, and so is
`E / B`. -/
theorem outBound_errBound_le_of_abs_le (A a u η : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hAa : |A| ≤ a) (hstab : a + a * u * (2 + u) < 1) :
    outBound A 1 0 ≤ 1 / (1 - a) ∧
      errBound A u η 1 0 ≤ (u + η * (2 + u) + a * u * (2 + u) / (1 - a)) /
        (1 - a - a * u * (2 + u)) ∧
      errBound A u η 1 0 / outBound A 1 0 ≤
        ((u + η * (2 + u)) * (1 - a) + a * u * (2 + u)) / (1 - a - a * u * (2 + u)) := by
  have hα := abs_nonneg A
  have ha : 0 ≤ a := hα.trans hAa
  have hκ : 0 ≤ u * (2 + u) := by positivity
  have hak : 0 ≤ a * u * (2 + u) := by positivity
  have hαk : |A| * u * (2 + u) ≤ a * u * (2 + u) := by gcongr
  have hta : 0 < 1 - a := by linarith
  have ht : 0 < 1 - |A| := by linarith
  have hDa : 0 < 1 - a - a * u * (2 + u) := by linarith
  have hD : 1 - a - a * u * (2 + u) ≤ 1 - |A| - |A| * u * (2 + u) := by linarith
  have hB : outBound A 1 0 = 1 / (1 - |A|) := by unfold outBound; simp
  have hBle : outBound A 1 0 ≤ 1 / (1 - a) := by
    rw [hB]; exact one_div_le_one_div_of_le hta (by linarith)
  refine ⟨hBle, ?_, ?_⟩
  · unfold errBound
    rw [hB]
    have hN : u * 1 + η * (2 + u) + |A| * u * (2 + u) * (1 / (1 - |A|)) ≤
        u + η * (2 + u) + a * u * (2 + u) / (1 - a) := by
      rw [mul_one_div, mul_one]
      have : |A| * u * (2 + u) / (1 - |A|) ≤ a * u * (2 + u) / (1 - a) :=
        div_le_div₀ hak hαk hta (by linarith)
      linarith
    exact div_le_div₀ (by positivity) hN hDa hD
  · have hE : errBound A u η 1 0 / outBound A 1 0 =
        ((u + η * (2 + u)) * (1 - |A|) + |A| * u * (2 + u)) /
          (1 - |A| - |A| * u * (2 + u)) := by
      unfold errBound
      rw [hB]
      field_simp
    rw [hE, div_le_div_iff₀ (by linarith) hDa]
    have key := mul_nonneg (sub_nonneg.2 hAa)
      (by positivity : 0 ≤ u * (2 + u) * (1 + (u + η * (2 + u))))
    nlinarith [key]

/-- **How `E` grows as `|A|` approaches 1.** For inputs at most `M = 1` in size and a starting
state `S = 0`, when `1/2 ≤ |A| ≤ 1 - δ`, where `7·u·(2 + u) ≤ δ`, `0 < u ≤ 1/100`, `0 ≤ η`
and `η·(2 + u) ≤ u / 100`: `u / (1 - |A|)² ≤ E ≤ 3·u / (1 - |A|)²`, with
`E = errBound A u η 1 0`. -/
theorem errBound_between_of_abs_le (A u η δ : ℝ) (hu0 : 0 < u) (hu : u ≤ 1 / 100)
    (hη : 0 ≤ η) (hc : η * (2 + u) ≤ u / 100) (hδ : 7 * (u * (2 + u)) ≤ δ)
    (hA1 : 1 / 2 ≤ |A|) (hA2 : |A| ≤ 1 - δ) :
    u / (1 - |A|) ^ 2 ≤ errBound A u η 1 0 ∧ errBound A u η 1 0 ≤ 3 * u / (1 - |A|) ^ 2 := by
  set α := |A| with hαdef
  set t := 1 - α with htdef
  set κ := u * (2 + u) with hκdef
  set c := η * (2 + u) with hcdef
  have hκ0 : 2 * u ≤ κ := by rw [hκdef]; nlinarith
  have hκ1 : κ ≤ 201 / 100 * u := by rw [hκdef]; nlinarith
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have ht : 0 < t := by linarith
  have ht2 : t ≤ 1 / 2 := by linarith
  have hακ : α * κ ≤ t / 7 := by nlinarith
  have hακ1 : u ≤ α * κ := by nlinarith
  have hD : 0 < t - α * κ := by linarith
  have hE : errBound A u η 1 0 = ((u + c) * t + α * κ) / (t * (t - α * κ)) := by
    unfold errBound outBound
    rw [← hαdef, abs_zero, zero_add, ← htdef]
    have : 1 - α - α * u * (2 + u) = t - α * κ := by rw [htdef, hκdef]; ring
    rw [this, hcdef, hκdef]
    field_simp
  rw [hE]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : u * t ≤ α * κ * t := mul_le_mul_of_nonneg_right hακ1 ht.le
    have k2 : 0 ≤ (u + c) * t ^ 2 := by positivity
    have k3 : 0 ≤ u * (α * κ) := by positivity
    have e : u * (t * (t - α * κ)) = t * (u * t - u * (α * κ)) := by ring
    have e2 : ((u + c) * t + α * κ) * t ^ 2 = t * ((u + c) * t ^ 2 + α * κ * t) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left (by linarith) ht.le
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have k1 : (u + c) * t ^ 2 ≤ (101 / 100 * u) * (t / 2) := by
      have : t ^ 2 ≤ t / 2 := by nlinarith
      exact mul_le_mul (by linarith) this (by positivity) (by positivity)
    have k2 : α * κ * t ≤ 201 / 100 * u * t := by
      have : α * κ ≤ 201 / 100 * u := by nlinarith
      exact mul_le_mul_of_nonneg_right this ht.le
    have k3 : u * (α * κ) ≤ u * (t / 7) := mul_le_mul_of_nonneg_left hακ hu0.le
    have e : ((u + c) * t + α * κ) * t ^ 2 = t * ((u + c) * t ^ 2 + α * κ * t) := by ring
    have e2 : 3 * u * (t * (t - α * κ)) = t * (3 * u * t - 3 * (u * (α * κ))) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left (by nlinarith) ht.le

/-- **A decibel bound from a power bound.** If `0 < x ≤ r` and `r ^ m · 10 ^ n ≤ 1` (`m > 0`),
then `20·log₁₀ x ≤ -(20·n / m)`. With `x = E / B` this states `E` relative to `B` in decibels;
the power bound is a statement about rational numbers that `norm_num` checks. -/
theorem twenty_logb_le_of_pow_le (x r : ℝ) (m n : ℕ) (hx : 0 < x) (hxr : x ≤ r) (hm : 0 < m)
    (hr : r ^ m * 10 ^ n ≤ 1) : 20 * Real.logb 10 x ≤ -(20 * n / m) := by
  have hr0 : 0 < r := hx.trans_le hxr
  have h1 : Real.logb 10 x ≤ Real.logb 10 r := Real.logb_le_logb_of_le (by norm_num) hx hxr
  have hpow : r ^ m ≤ ((10 : ℝ) ^ n)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    exact hr
  have h2 : (m : ℝ) * Real.logb 10 r ≤ -n := by
    rw [← Real.logb_pow]
    calc Real.logb 10 (r ^ m) ≤ Real.logb 10 ((10 : ℝ) ^ n)⁻¹ :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hpow
      _ = -n := by rw [Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : Real.logb 10 r ≤ -n / m := by
    rw [le_div_iff₀ hm']; linarith
  have : -(20 * (n : ℝ) / m) = 20 * (-n / m) := by ring
  rw [this]
  linarith

/-- **The four bounds of one row of the table in `proofs/README.md`.** For inputs at most `M = 1`
in size and a starting state `S = 0`, with `0 < u`, `0 ≤ η ≤ ηb`, `|A| ≤ a` and
`a + a·u·(2 + u) < 1`: if `Bb` and `Eb` are at least the values of `B = outBound A 1 0` and
`E = errBound A u η 1 0` at `|A| = a` and `η = ηb` (written out), `k / 10 ^ j` is at least the
value there of `E / B`, and `k ^ m · 10 ^ n ≤ 10 ^ (j·m)` in natural numbers with `m > 0`, then
`B ≤ Bb`, `E ≤ Eb`, `E / B ≤ k / 10 ^ j` and `20·log₁₀(E / B) ≤ -(20·n / m)`. -/
theorem block_constants_le_of_abs_le (A a u η ηb Bb Eb : ℝ) (k j m n : ℕ) (hu : 0 < u)
    (hη : 0 ≤ η) (hηb : η ≤ ηb) (hAa : |A| ≤ a) (hstab : a + a * u * (2 + u) < 1)
    (hm : 0 < m) (hB : 1 / (1 - a) ≤ Bb)
    (hE : (u + ηb * (2 + u) + a * u * (2 + u) / (1 - a)) / (1 - a - a * u * (2 + u)) ≤ Eb)
    (hr : ((u + ηb * (2 + u)) * (1 - a) + a * u * (2 + u)) / (1 - a - a * u * (2 + u)) ≤
      k / 10 ^ j)
    (hpow : k ^ m * 10 ^ n ≤ 10 ^ (j * m)) :
    outBound A 1 0 ≤ Bb ∧ errBound A u η 1 0 ≤ Eb ∧
      errBound A u η 1 0 / outBound A 1 0 ≤ k / 10 ^ j ∧
      20 * Real.logb 10 (errBound A u η 1 0 / outBound A 1 0) ≤ -(20 * n / m) := by
  obtain ⟨h1, h2, h3⟩ := outBound_errBound_le_of_abs_le A a u η hu.le hη hAa hstab
  have hα := abs_nonneg A
  have ha : 0 ≤ a := hα.trans hAa
  have hden : 0 < 1 - a - a * u * (2 + u) := by linarith
  have hak : 0 ≤ a * u * (2 + u) := by have := hu.le; positivity
  have hta : 0 < 1 - a := by linarith
  -- The values at `|A| = a` grow with `η`, so those at `η = ηb` bound them.
  have hηu : η * (2 + u) ≤ ηb * (2 + u) := mul_le_mul_of_nonneg_right hηb (by linarith)
  have hE' : (u + η * (2 + u) + a * u * (2 + u) / (1 - a)) / (1 - a - a * u * (2 + u)) ≤ Eb :=
    (div_le_div_of_nonneg_right (by linarith) hden.le).trans hE
  have hr' : ((u + η * (2 + u)) * (1 - a) + a * u * (2 + u)) / (1 - a - a * u * (2 + u)) ≤
      k / 10 ^ j := by
    refine (div_le_div_of_nonneg_right ?_ hden.le).trans hr
    nlinarith [mul_le_mul_of_nonneg_right hηu hta.le]
  have hstabA : |A| + |A| * u * (2 + u) < 1 := by
    have : |A| * u * (2 + u) ≤ a * u * (2 + u) := by gcongr
    linarith
  obtain ⟨-, hSB, -, -⟩ := block_constants A u η 1 0 hu.le hη zero_le_one hstabA
  have hpos : 0 < errBound A u η 1 0 / outBound A 1 0 := by
    have hk : 0 ≤ |A| * u * (2 + u) := by positivity
    have hdenA : 0 < 1 - |A| - |A| * u * (2 + u) := by linarith
    have hE1 : 0 < errBound A u η 1 0 := by
      unfold errBound
      have : 0 ≤ |A| * u * (2 + u) * outBound A 1 0 := by
        have := (abs_nonneg (0 : ℝ)).trans hSB
        positivity
      exact div_pos (by nlinarith) hdenA
    have hB1 : 0 < outBound A 1 0 := by
      unfold outBound
      rw [abs_zero, zero_add]
      exact div_pos one_pos (by linarith)
    exact div_pos hE1 hB1
  have hpow' : ((k : ℝ) / 10 ^ j) ^ m * 10 ^ n ≤ 1 := by
    rw [div_pow, ← pow_mul, div_mul_eq_mul_div, div_le_one (by positivity)]
    exact_mod_cast hpow
  exact ⟨h1.trans hB, h2.trans hE', h3.trans hr',
    twenty_logb_le_of_pow_le _ _ m n hpos (h3.trans hr') hm hpow'⟩

end conjure_dsp_lib.one_pole

end
