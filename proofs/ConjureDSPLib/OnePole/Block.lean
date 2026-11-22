module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# The one-pole filter over a whole block: the real-number argument

Each floating-point step of the filter `y = x + a * y_prev` is close to the exact step (the
per-step bounds in `BridgeF64.lean` and `BridgeF32.lean`, not imported here). This file shows, on real numbers only,
that with a stable coefficient (`|A| < 1`, with a little room to spare) those per-step errors do
not pile up: over a block of any length, every computed output stays within one fixed distance
`E` of the exact real-number filter's output.

It uses real numbers only, so it serves both precisions: `BlockF64.lean` and `BlockF32.lean`
apply it to the Rust functions.
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
`|r| ≤ B`, the input is at most `M`, and the step's rounding is within `stepErr`, then the new
computed state `y'` is within `E` of the new exact state, which is at most `B`. -/
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

/-- `B` of `block_error_real`: a bound on the exact filter's outputs from state `S` with inputs
at most `M`. -/
noncomputable def outBound (A M S : ℝ) : ℝ := |S| + M / (1 - |A|)

/-- `E` of `block_error_real`: the whole-block error bound. -/
noncomputable def errBound (A u η M S : ℝ) : ℝ :=
  (u * M + η * (2 + u) + |A| * u * (2 + u) * outBound A M S) / (1 - |A| - |A| * u * (2 + u))

/-- The constants of `block_error_real` work: `E ≥ 0`, `|S| ≤ B`, and the two inequalities that
`block_step` needs. -/
theorem block_constants (A u η M S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hstab : |A| + |A| * u * (2 + u) < 1) :
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    0 ≤ E ∧ |S| ≤ B ∧ M + |A| * B ≤ B ∧
      u * M + η * (2 + u) + |A| * u * (2 + u) * (B + E) + |A| * E ≤ E := by
  intro B E
  have hA := abs_nonneg A
  have hκ : 0 ≤ |A| * u * (2 + u) := by positivity
  have hα : 0 < 1 - |A| := by linarith
  have hden : 0 < 1 - |A| - |A| * u * (2 + u) := by linarith
  have hB0 : 0 ≤ M / (1 - |A|) := div_nonneg hM0 hα.le
  have hBnn : 0 ≤ B := by positivity
  have hE0 : 0 ≤ E := div_nonneg (by positivity) hden.le
  have hB : M + |A| * B ≤ B := by
    have : M = (1 - |A|) * (M / (1 - |A|)) := by field_simp
    nlinarith [abs_nonneg S]
  have hEeq : E * (1 - |A| - |A| * u * (2 + u)) =
      u * M + η * (2 + u) + |A| * u * (2 + u) * B := div_mul_cancel₀ _ hden.ne'
  have hE : u * M + η * (2 + u) + |A| * u * (2 + u) * (B + E) + |A| * E ≤ E := by
    nlinarith [hEeq]
  exact ⟨hE0, by simp only [B]; linarith, hB, hE⟩

/-- **Whole-block error, on real numbers.** Suppose the inputs are bounded by `M`, the filter
starts from state `S`, and each computed step is within the per-step rounding error of the exact
step (`WithinStepErr`). If `|A| + |A|·u·(2 + u) < 1` (stability, with room for rounding), then
every computed output, and the final state, is within

`E = (u·M + η·(2 + u) + |A|·u·(2 + u)·B) / (1 - |A| - |A|·u·(2 + u))`

of the exact real-number filter's, however long the block, where `B = |S| + M / (1 - |A|)`
bounds the exact filter's outputs. -/
theorem block_error_real (A u η M S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hstab : |A| + |A| * u * (2 + u) < 1) (xs : List ℝ) (f : ℝ) (ys : List ℝ)
    (hM : ∀ x ∈ xs, |x| ≤ M) (hw : WithinStepErr A u η S xs f ys) :
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    List.Forall₂ (fun c e => |c - e| ≤ E) ys (filt_real A S xs).2 ∧
      |f - (filt_real A S xs).1| ≤ E := by
  intro B E
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants A u η M S hu hη hM0 hstab
  exact block_error_core A u η M B E hu hB hE xs S S f ys hM (by simpa using hE0) hSB hw

end conjure_dsp_lib.one_pole

end
