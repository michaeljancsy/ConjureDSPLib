module

public import ConjureDSPLib.Smoother.Exact
public import ConjureDSPLib.FloatFacts

/-!
# The smoother over a whole block: the real-number argument

Each floating-point step of the smoother `y = s + c * (x - s)` rounds three times: the
difference `x - s`, the product `c * (x - s)` and the sum (the per-step bounds in `BridgeF64.lean`
and `BridgeF32.lean`, not imported here). The coefficient `c = 1 - a` is rounded once per block,
before the first sample, so it is the same in every step; this file compares the computed
smoother with the exact smoother `filt_real A` whose coefficient is that stored `c`, that is with
`A = 1 - c` (`BridgeF64.lean` and `BridgeF32.lean` bound how far that `A` is from `a`).

This file shows, on real numbers only, that with a stable `A` (`|A| < 1`, with a little room to
spare) the per-step errors do not pile up: over a block of any length, every computed output stays
within one fixed distance `E` of the exact smoother's output. For a steady input `X` it follows
that the computed state is within `|A|^n·|S - X| + E` of `X` after `n` samples.

It uses real numbers only, so it serves both precisions: `BlockF64.lean` and `BlockF32.lean`
apply it to the Rust functions. The last part bounds `E` for inputs at most 1 in size, a start
from 0 and `0 ≤ A ≤ a`, and gives the tool for stating `E` in decibels.
-/

@[expose] public section

namespace conjure_dsp_lib.smoother

/-- The bound on the rounding error of the difference `x - y` (`y` the state, `x` the input):
`u·|x - y| + η`. -/
def diffErr (u η y x : ℝ) : ℝ := u * |x - y| + η

/-- The bound on the error of the rounded product `c * (x - y)` against the exact
`(1 - A)·(x - y)`, counting the difference's rounding: `|1 - A|` times the difference's error,
plus the product's own rounding, `u·|1 - A|·|computed difference| + η`. -/
def prodErr (A u η y x : ℝ) : ℝ :=
  u * |1 - A| * (|x - y| + diffErr u η y x) + η + |1 - A| * diffErr u η y x

/-- The per-step error bound of `step_f64_error` / `step_f32_error`, for state `y` (the previous
output) and input `x`, with coefficient `1 - A`, unit roundoff `u` and underflow error `η`: the
sum's rounding, `u·|computed sum| + η`, plus the product's error `prodErr`. It must stay exactly
the right-hand side of those theorems: `filt_f64_withinStepErr` and `filt_f32_withinStepErr`
check that it does. -/
def stepErr (A u η y x : ℝ) : ℝ :=
  u * (|y + (1 - A) * (x - y)| + prodErr A u η y x) + η + prodErr A u η y x

/-- `WithinStepErr A u η y xs f ys`: starting from state `y` (the previous output), the
computed outputs `ys` and final state `f` come from inputs `xs`, each step within `stepErr` of
the exact step taken from the previous computed output. -/
def WithinStepErr (A u η : ℝ) : ℝ → List ℝ → ℝ → List ℝ → Prop
  | y, [], f, [] => f = y
  | y, x :: xs, f, y' :: ys =>
    |y' - (y + (1 - A) * (x - y))| ≤ stepErr A u η y x ∧ WithinStepErr A u η y' xs f ys
  | _, _, _, _ => False

/-- A bound on `stepErr` when the input is at most `M` and the state at most `W` in size. -/
def stepBound (A u η M W : ℝ) : ℝ :=
  u * (|A| * W + |1 - A| * M) +
    (1 + u) * (|1 - A| * u * (2 + u) * (M + W) + |1 - A| * (1 + u) * η + η) + η

/-- How fast `stepBound` grows with the state bound `W`: `stepBound A u η M (W + E)` is
`stepBound A u η M W + errGrowth A u · E`. -/
def errGrowth (A u : ℝ) : ℝ := u * |A| + (1 + u) * |1 - A| * u * (2 + u)

theorem stepBound_add (A u η M W E : ℝ) :
    stepBound A u η M (W + E) = stepBound A u η M W + errGrowth A u * E := by
  unfold stepBound errGrowth; ring

/-- One step's rounding error is at most `stepBound` when the input is at most `M` and the state
at most `W` in size. -/
theorem stepErr_le (A u η M W x y : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hx : |x| ≤ M)
    (hy : |y| ≤ W) : stepErr A u η y x ≤ stepBound A u η M W := by
  have hκ := abs_nonneg (1 - A)
  have hg : |x - y| ≤ M + W := (abs_sub x y).trans (add_le_add hx hy)
  have hd : diffErr u η y x ≤ u * (M + W) + η := by
    unfold diffErr; gcongr
  have hd0 : 0 ≤ diffErr u η y x := by unfold diffErr; positivity
  have hp : prodErr A u η y x ≤
      |1 - A| * u * (2 + u) * (M + W) + |1 - A| * (1 + u) * η + η := by
    unfold prodErr
    calc u * |1 - A| * (|x - y| + diffErr u η y x) + η + |1 - A| * diffErr u η y x
        ≤ u * |1 - A| * ((M + W) + (u * (M + W) + η)) + η + |1 - A| * (u * (M + W) + η) := by
          gcongr
      _ = _ := by ring
  have hl : |y + (1 - A) * (x - y)| ≤ |A| * W + |1 - A| * M := by
    have e : y + (1 - A) * (x - y) = A * y + (1 - A) * x := by ring
    rw [e]
    calc |A * y + (1 - A) * x| ≤ |A * y| + |(1 - A) * x| := abs_add_le _ _
      _ = |A| * |y| + |1 - A| * |x| := by rw [abs_mul, abs_mul]
      _ ≤ |A| * W + |1 - A| * M := by gcongr
  unfold stepErr stepBound
  calc u * (|y + (1 - A) * (x - y)| + prodErr A u η y x) + η + prodErr A u η y x
      = u * |y + (1 - A) * (x - y)| + (1 + u) * prodErr A u η y x + η := by ring
    _ ≤ u * (|A| * W + |1 - A| * M) +
        (1 + u) * (|1 - A| * u * (2 + u) * (M + W) + |1 - A| * (1 + u) * η + η) + η := by
      gcongr

/-- One step keeps both bounds: if the computed state `y` is within `E` of the exact state `r`,
`|r| ≤ B`, the input is at most `M` in size, and the step's rounding is within `stepErr`, then the
new computed state `y'` is within `E` of the new exact state, which is at most `B` in size. -/
theorem block_step (A u η M B E x y r y' : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hB : |1 - A| * M + |A| * B ≤ B) (hE : stepBound A u η M (B + E) + |A| * E ≤ E)
    (hx : |x| ≤ M) (hyr : |y - r| ≤ E) (hr : |r| ≤ B)
    (hstep : |y' - (y + (1 - A) * (x - y))| ≤ stepErr A u η y x) :
    |y' - (r + (1 - A) * (x - r))| ≤ E ∧ |r + (1 - A) * (x - r)| ≤ B := by
  have hA := abs_nonneg A
  have hy : |y| ≤ B + E := by
    calc |y| = |(y - r) + r| := by ring_nf
      _ ≤ |y - r| + |r| := abs_add_le _ _
      _ ≤ B + E := by linarith
  have hs := stepErr_le A u η M (B + E) x y hu hη hx hy
  constructor
  · -- The new error: this step's rounding plus the old error, shrunk by |A|.
    have e : y' - (r + (1 - A) * (x - r)) = (y' - (y + (1 - A) * (x - y))) + A * (y - r) := by
      ring
    rw [e]
    calc |(y' - (y + (1 - A) * (x - y))) + A * (y - r)|
        ≤ |y' - (y + (1 - A) * (x - y))| + |A * (y - r)| := abs_add_le _ _
      _ = |y' - (y + (1 - A) * (x - y))| + |A| * |y - r| := by rw [abs_mul]
      _ ≤ stepBound A u η M (B + E) + |A| * E :=
        add_le_add (hstep.trans hs) (mul_le_mul_of_nonneg_left hyr hA)
      _ ≤ E := hE
  · -- The exact smoother stays within B (stability).
    have e : r + (1 - A) * (x - r) = A * r + (1 - A) * x := by ring
    rw [e]
    calc |A * r + (1 - A) * x| ≤ |A * r| + |(1 - A) * x| := abs_add_le _ _
      _ = |A| * |r| + |1 - A| * |x| := by rw [abs_mul, abs_mul]
      _ ≤ |A| * B + |1 - A| * M := by gcongr
      _ ≤ B := by linarith

/-- The induction behind `block_error_real`, with the bounds `B` (on the exact smoother) and `E`
(on the error) as parameters satisfying the two inequalities that make them invariant. -/
theorem block_error_core (A u η M B E : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hB : |1 - A| * M + |A| * B ≤ B) (hE : stepBound A u η M (B + E) + |A| * E ≤ E) :
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
        block_step A u η M B E x y r y' hu hη hB hE (hM x (by simp)) hyr hr hstep
      obtain ⟨h1, h2⟩ := ih y' (r + (1 - A) * (x - r)) f ys
        (fun z hz => hM z (List.mem_cons_of_mem _ hz)) herr hr' hrest
      exact ⟨List.Forall₂.cons herr h1, h2⟩

/-- `B` of `block_error_real` (and of `process_f64_block_error` and the f32 version): when
`|A| < 1`, a bound on the exact smoother's outputs from state `S` with inputs at most `M` in size.
When `0 ≤ A < 1` it is `|S| + M`. -/
noncomputable def outBound (A M S : ℝ) : ℝ := |S| + |1 - A| * M / (1 - |A|)

/-- `E` of `block_error_real` (and of `process_f64_block_error` and the f32 version): the
whole-block error bound. -/
noncomputable def errBound (A u η M S : ℝ) : ℝ :=
  stepBound A u η M (outBound A M S) / (1 - |A| - errGrowth A u)

/-- `B = outBound` and `E = errBound` satisfy what `block_step` needs: `E ≥ 0`, `|S| ≤ B`, and
the two inequalities. -/
theorem block_constants (A u η M S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hstab : |A| + errGrowth A u < 1) :
    let B := outBound A M S
    let E := errBound A u η M S
    0 ≤ E ∧ |S| ≤ B ∧ |1 - A| * M + |A| * B ≤ B ∧ stepBound A u η M (B + E) + |A| * E ≤ E := by
  intro B E
  have hBdef : B = |S| + |1 - A| * M / (1 - |A|) := rfl
  have hEdef : E = stepBound A u η M B / (1 - |A| - errGrowth A u) := rfl
  have hA := abs_nonneg A
  have hκ := abs_nonneg (1 - A)
  have hg : 0 ≤ errGrowth A u := by unfold errGrowth; positivity
  have hα : 0 < 1 - |A| := by linarith
  have hden : 0 < 1 - |A| - errGrowth A u := by linarith
  have hB0 : 0 ≤ |1 - A| * M / (1 - |A|) := div_nonneg (by positivity) hα.le
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hSB : 0 ≤ stepBound A u η M B := by unfold stepBound; positivity
  have hE0 : 0 ≤ E := by rw [hEdef]; exact div_nonneg hSB hden.le
  have hB : |1 - A| * M + |A| * B ≤ B := by
    have : |1 - A| * M = (1 - |A|) * (|1 - A| * M / (1 - |A|)) := by field_simp
    rw [hBdef]
    nlinarith [abs_nonneg S]
  have hEeq : E * (1 - |A| - errGrowth A u) = stepBound A u η M B := by
    rw [hEdef]; exact div_mul_cancel₀ _ hden.ne'
  have hE : stepBound A u η M (B + E) + |A| * E ≤ E := by
    rw [stepBound_add]; nlinarith [hEeq]
  exact ⟨hE0, by rw [hBdef]; linarith, hB, hE⟩

/-- **Whole-block error, on real numbers.** Suppose the inputs are bounded by `M`, the smoother
starts from state `S`, and each computed step is within the per-step rounding error of the exact
step with coefficient `1 - A` (`WithinStepErr`). If `|A| + errGrowth A u < 1` (stability, with
room for rounding), then every computed output, and the final state, is within
`E = errBound A u η M S` of the exact smoother `filt_real A` from `S`, however long the block. -/
theorem block_error_real (A u η M S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hstab : |A| + errGrowth A u < 1) (xs : List ℝ) (f : ℝ) (ys : List ℝ)
    (hM : ∀ x ∈ xs, |x| ≤ M) (hw : WithinStepErr A u η S xs f ys) :
    let E := errBound A u η M S
    List.Forall₂ (fun c e => |c - e| ≤ E) ys (filt_real A S xs).2 ∧
      |f - (filt_real A S xs).1| ≤ E := by
  intro E
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants A u η M S hu hη hM0 hstab
  have h0 : |S - S| ≤ E := by rw [sub_self, abs_zero]; exact hE0
  exact block_error_core A u η M (outBound A M S) E hu hη hB hE xs S S f ys hM h0 hSB hw

/-- **Settling on a steady input, on real numbers.** Under the conditions of `block_error_real`,
with the input `X` held for `n` samples and `|X| ≤ M`: the computed final state is within
`|A|^n·|S - X| + E` of `X`, where `E = errBound A u η M S`. The first term is the exact
smoother's remaining distance (`filt_real_replicate`); the second is the rounding. -/
theorem settle_real (A u η M X S : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (hXM : |X| ≤ M)
    (hstab : |A| + errGrowth A u < 1) (n : ℕ) (f : ℝ) (ys : List ℝ)
    (hw : WithinStepErr A u η S (List.replicate n X) f ys) :
    |f - X| ≤ |A| ^ n * |S - X| + errBound A u η M S := by
  have h := (block_error_real A u η M S hu hη ((abs_nonneg X).trans hXM) hstab _ f ys
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hXM) hw).2
  rw [filt_real_replicate] at h
  have e : f - X = (f - (X + A ^ n * (S - X))) + A ^ n * (S - X) := by ring
  rw [e]
  calc |(f - (X + A ^ n * (S - X))) + A ^ n * (S - X)|
      ≤ |f - (X + A ^ n * (S - X))| + |A ^ n * (S - X)| := abs_add_le _ _
    _ = |f - (X + A ^ n * (S - X))| + |A| ^ n * |S - X| := by rw [abs_mul, abs_pow]
    _ ≤ errBound A u η M S + |A| ^ n * |S - X| := by linarith
    _ = _ := by ring

/-! ## The bound for inputs at most 1, a start from 0 and `0 ≤ A ≤ a` -/

/-- **`E` grows with `A` on `0 ≤ A ≤ a`.** For inputs at most `M = 1` in size, a starting state
`S = 0`, `0 ≤ u ≤ 1/4`, `0 ≤ η`, `0 ≤ A ≤ a` and `a + errGrowth a u < 1`: the stability condition
holds at `A`, `B = outBound A 1 0` is exactly 1, and `E = errBound A u η 1 0` is at most its value
at `A = a`, written out. -/
theorem errBound_le_of_le (A a u η : ℝ) (hu : 0 ≤ u) (hu4 : u ≤ 1 / 4) (hη : 0 ≤ η)
    (hA0 : 0 ≤ A) (hAa : A ≤ a) (hstab : a + errGrowth a u < 1) :
    |A| + errGrowth A u < 1 ∧ outBound A 1 0 = 1 ∧
      errBound A u η 1 0 ≤ (u + (1 + u) * ((1 - a) * (2 * u * (2 + u) + (1 + u) * η) + η) + η) /
        (1 - a - u * a - (1 + u) * (1 - a) * u * (2 + u)) := by
  have hg : 0 ≤ errGrowth a u := by unfold errGrowth; positivity
  have ha1 : a < 1 := by have := hA0.trans hAa; linarith
  have hA1 : A < 1 := lt_of_le_of_lt hAa ha1
  have hAabs : |A| = A := abs_of_nonneg hA0
  have hA1abs : |1 - A| = 1 - A := abs_of_nonneg (by linarith)
  have haabs : |a| = a := abs_of_nonneg (hA0.trans hAa)
  have ha1abs : |1 - a| = 1 - a := abs_of_nonneg (by linarith)
  have hk : u * (2 + u) ≤ 9 / 16 := by nlinarith
  have hk0 : 0 ≤ u * (2 + u) := by positivity
  have hga : errGrowth a u = u * a + (1 + u) * (1 - a) * u * (2 + u) := by
    unfold errGrowth; rw [haabs, ha1abs]
  have hgA : errGrowth A u = u * A + (1 + u) * (1 - A) * u * (2 + u) := by
    unfold errGrowth; rw [hAabs, hA1abs]
  have hmono : 0 ≤ (a - A) * ((1 + u) * (1 - u * (2 + u))) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hstabA : |A| + errGrowth A u < 1 := by
    rw [hAabs, hgA]; rw [hga] at hstab; nlinarith [hmono]
  have hB : outBound A 1 0 = 1 := by
    unfold outBound
    rw [abs_zero, zero_add, hAabs, hA1abs, mul_one, div_self (by linarith)]
  refine ⟨hstabA, hB, ?_⟩
  unfold errBound
  rw [hB, hAabs, hgA]
  have hDa : 0 < 1 - a - u * a - (1 + u) * (1 - a) * u * (2 + u) := by
    rw [hga] at hstab; linarith
  have hDA : 0 < 1 - A - (u * A + (1 + u) * (1 - A) * u * (2 + u)) := by
    rw [hAabs, hgA] at hstabA; linarith
  rw [div_le_div_iff₀ hDA hDa]
  unfold stepBound
  rw [hAabs, hA1abs]
  -- Both sides are affine in `A`; their difference is `(a - A)` times a nonnegative number.
  have hP : 0 ≤ u + (1 + u) * η + η := by positivity
  have hQ : 0 ≤ (1 + u) * (2 * u * (2 + u) + (1 + u) * η) := by positivity
  have e : (u + (1 + u) * ((1 - a) * (2 * u * (2 + u) + (1 + u) * η) + η) + η) *
        (1 - A - (u * A + (1 + u) * (1 - A) * u * (2 + u))) -
      (u * (A * 1 + (1 - A) * 1) + (1 + u) * ((1 - A) * u * (2 + u) * (1 + 1) +
          (1 - A) * (1 + u) * η + η) + η) * (1 - a - u * a - (1 + u) * (1 - a) * u * (2 + u)) =
      (a - A) * ((u + (1 + u) * η + η) * ((1 + u) * (1 - u * (2 + u))) +
        (1 + u) * (2 * u * (2 + u) + (1 + u) * η) * u) := by
    ring
  have h0 : 0 ≤ (a - A) * ((u + (1 + u) * η + η) * ((1 + u) * (1 - u * (2 + u))) +
      (1 + u) * (2 * u * (2 + u) + (1 + u) * η) * u) :=
    mul_nonneg (by linarith) (add_nonneg (mul_nonneg hP (by nlinarith)) (by positivity))
  linarith [e, h0]

/-- **The bounds of one row of the smoother table in `proofs/README.md`.** For inputs at most
`M = 1` in size and a starting state `S = 0`, with `0 < u ≤ 1/4`, `0 ≤ η ≤ ηb`, `0 ≤ A ≤ a` and
`a + errGrowth a u < 1`: if `k / 10 ^ j` is at least the value of `E = errBound A u η 1 0` at
`A = a` and `η = ηb` (written out), and `k ^ m · 10 ^ n ≤ 10 ^ (j·m)` in natural numbers with
`m > 0`, then the stability condition holds, `B = outBound A 1 0 = 1`, `E ≤ k / 10 ^ j` and
`20·log₁₀ E ≤ -(20·n / m)`. -/
theorem table_row_le_of_le (A a u η ηb : ℝ) (k j m n : ℕ) (hu : 0 < u) (hu4 : u ≤ 1 / 4)
    (hη : 0 ≤ η) (hηb : η ≤ ηb) (hA0 : 0 ≤ A) (hAa : A ≤ a) (hstab : a + errGrowth a u < 1)
    (hm : 0 < m)
    (hE : (u + (1 + u) * ((1 - a) * (2 * u * (2 + u) + (1 + u) * ηb) + ηb) + ηb) /
        (1 - a - u * a - (1 + u) * (1 - a) * u * (2 + u)) ≤ k / 10 ^ j)
    (hpow : k ^ m * 10 ^ n ≤ 10 ^ (j * m)) :
    |A| + errGrowth A u < 1 ∧ outBound A 1 0 = 1 ∧ errBound A u η 1 0 ≤ k / 10 ^ j ∧
      20 * Real.logb 10 (errBound A u η 1 0) ≤ -(20 * n / m) := by
  obtain ⟨hstabA, hB, h⟩ := errBound_le_of_le A a u η hu.le hu4 hη hA0 hAa hstab
  have hg : 0 ≤ errGrowth a u := by unfold errGrowth; have := hu.le; positivity
  have ha1 : a < 1 := by have := hA0.trans hAa; linarith
  have ha0 : 0 ≤ a := hA0.trans hAa
  have hk : u * (2 + u) ≤ 9 / 16 := by nlinarith
  have hden : 0 < 1 - a - u * a - (1 + u) * (1 - a) * u * (2 + u) := by
    have hga : errGrowth a u = u * a + (1 + u) * (1 - a) * u * (2 + u) := by
      unfold errGrowth; rw [abs_of_nonneg ha0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - a)]
    linarith
  -- The value at `A = a` grows with `η`, so the one at `η = ηb` bounds it.
  have hE' : errBound A u η 1 0 ≤ k / 10 ^ j := by
    refine h.trans ((div_le_div_of_nonneg_right ?_ hden.le).trans hE)
    have h1a : 0 ≤ 1 - a := by linarith
    have : (1 - a) * ((1 + u) * η) ≤ (1 - a) * ((1 + u) * ηb) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hηb (by linarith)) h1a
    nlinarith
  have hpos : 0 < errBound A u η 1 0 := by
    unfold errBound
    rw [hB]
    have hdenA : 0 < 1 - |A| - errGrowth A u := by linarith
    refine div_pos ?_ hdenA
    unfold stepBound
    have := abs_nonneg A
    have := abs_nonneg (1 - A)
    have : 0 ≤ u * (|A| * 1 + |1 - A| * 1) := by have := hu.le; positivity
    have : 0 ≤ (1 + u) * (|1 - A| * u * (2 + u) * (1 + 1) + |1 - A| * (1 + u) * η + η) := by
      have := hu.le; positivity
    -- `u·(|A| + |1 - A|) ≥ u·|A + (1 - A)| = u > 0`.
    have : u * 1 ≤ u * (|A| * 1 + |1 - A| * 1) := by
      have h1 : (1 : ℝ) ≤ |A| + |1 - A| := by
        calc (1 : ℝ) = |A + (1 - A)| := by ring_nf; simp
          _ ≤ |A| + |1 - A| := abs_add_le _ _
      nlinarith
    linarith
  have hpow' : ((k : ℝ) / 10 ^ j) ^ m * 10 ^ n ≤ 1 := by
    rw [div_pow, ← pow_mul, div_mul_eq_mul_div, div_le_one (by positivity)]
    exact_mod_cast hpow
  exact ⟨hstabA, hB, hE', twenty_logb_le_of_pow_le _ _ m n hpos hE' hm hpow'⟩

end conjure_dsp_lib.smoother

end
