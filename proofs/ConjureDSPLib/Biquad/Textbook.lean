module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# The biquad's transposed direct form II is the textbook recurrence

On real numbers (exact arithmetic), the two-state transposed-direct-form-II filter that
`src/biquad.rs` computes gives exactly the outputs of the textbook recurrence

`y[n] = b0·x[n] + b1·x[n-1] + b2·x[n-2] - a1·y[n-1] - a2·y[n-2]`.

From a zero state it matches the recurrence with zero history (`tdf2_real_eq_df1_real_zero`);
in general, a state corresponds to a history through `stateOfHistory` (`tdf2_real_eq_df1_real`).
In floating point the two forms round differently; the Rust code computes the transposed form.
-/

@[expose] public section

namespace conjure_dsp_lib.biquad

/-- The transposed-direct-form-II filter in exact arithmetic, from state `(s1, s2)`: returns the
final state and the outputs. Same steps as the Rust `step_f64` / `step_f32`. -/
def tdf2_real (b0 b1 b2 a1 a2 : ℝ) : ℝ × ℝ → List ℝ → (ℝ × ℝ) × List ℝ
  | s, [] => (s, [])
  | (s1, s2), x :: xs =>
    let y := b0 * x + s1
    let r := tdf2_real b0 b1 b2 a1 a2 (b1 * x - a1 * y + s2, b2 * x - a2 * y) xs
    (r.1, y :: r.2)

/-- The textbook (direct form I) recurrence in exact arithmetic, from the history
`(x[n-1], x[n-2], y[n-1], y[n-2])`: returns the outputs. -/
def df1_real (b0 b1 b2 a1 a2 : ℝ) : ℝ × ℝ × ℝ × ℝ → List ℝ → List ℝ
  | _, [] => []
  | (x1, x2, y1, y2), x :: xs =>
    let y := b0 * x + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2
    y :: df1_real b0 b1 b2 a1 a2 (x, x1, y, y1) xs

/-- The transposed-form state that carries the same information as a textbook history. -/
def stateOfHistory (b1 b2 a1 a2 : ℝ) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ
  | (x1, x2, y1, y2) => (b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2, b2 * x1 - a2 * y1)

/-- From the state matching a history, the transposed form gives exactly the textbook outputs. -/
theorem tdf2_real_eq_df1_real (b0 b1 b2 a1 a2 : ℝ) :
    ∀ (xs : List ℝ) (h : ℝ × ℝ × ℝ × ℝ),
      (tdf2_real b0 b1 b2 a1 a2 (stateOfHistory b1 b2 a1 a2 h) xs).2 =
        df1_real b0 b1 b2 a1 a2 h xs := by
  intro xs
  induction xs with
  | nil => intro h; obtain ⟨x1, x2, y1, y2⟩ := h; rfl
  | cons x xs ih =>
    intro h
    obtain ⟨x1, x2, y1, y2⟩ := h
    have hy : b0 * x + (b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2) =
        b0 * x + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2 := by ring
    simp only [stateOfHistory, tdf2_real, df1_real, hy]
    congr 1
    rw [← ih (x, x1, b0 * x + b1 * x1 + b2 * x2 - a1 * y1 - a2 * y2, y1)]
    simp only [stateOfHistory]
    congr 3
    ring

/-- From a zero state, the transposed form gives exactly the textbook outputs with zero history:
the impulse response, step response and every other output agree. -/
theorem tdf2_real_eq_df1_real_zero (b0 b1 b2 a1 a2 : ℝ) (xs : List ℝ) :
    (tdf2_real b0 b1 b2 a1 a2 (0, 0) xs).2 = df1_real b0 b1 b2 a1 a2 (0, 0, 0, 0) xs := by
  have h := tdf2_real_eq_df1_real b0 b1 b2 a1 a2 xs (0, 0, 0, 0)
  simp only [stateOfHistory, mul_zero, sub_zero, add_zero] at h
  exact h

end conjure_dsp_lib.biquad

end
