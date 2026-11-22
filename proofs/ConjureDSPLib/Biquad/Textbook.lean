module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# The biquad's transposed direct form II is the textbook recurrence

On real numbers (exact arithmetic), the two-state transposed-direct-form-II filter that
`src/biquad.rs` computes gives exactly the outputs of the textbook recurrence

`y[n] = b0·x[n] + b1·x[n-1] + b2·x[n-2] - a1·y[n-1] - a2·y[n-2]`.

From a zero state it matches the recurrence with zero history (`filt_real_eq_df1_real_zero`);
in general, a state corresponds to a history through `stateOfHistory` (`filt_real_eq_df1_real`).
In floating point the two forms round differently; the Rust code computes the transposed form.
-/

@[expose] public section

namespace conjure_dsp_lib.biquad

/-- Biquad coefficients as real numbers, normalized so that `a0 = 1`. -/
structure CoeffsReal where
  /-- Feed-forward coefficient of `x[n]`. -/
  b0 : ℝ
  /-- Feed-forward coefficient of `x[n-1]`. -/
  b1 : ℝ
  /-- Feed-forward coefficient of `x[n-2]`. -/
  b2 : ℝ
  /-- Feedback coefficient of `y[n-1]` (subtracted). -/
  a1 : ℝ
  /-- Feedback coefficient of `y[n-2]` (subtracted). -/
  a2 : ℝ

/-- The transposed-direct-form-II filter in exact arithmetic, from state `(s1, s2)`: returns the
final state and the outputs. It is the real-number counterpart of `filt_f64` / `filt_f32` (the
same steps); the biquad error-bound proof will relate the two. -/
def filt_real (c : CoeffsReal) : ℝ × ℝ → List ℝ → (ℝ × ℝ) × List ℝ
  | s, [] => (s, [])
  | (s1, s2), x :: xs =>
    let y := c.b0 * x + s1
    let r := filt_real c (c.b1 * x - c.a1 * y + s2, c.b2 * x - c.a2 * y) xs
    (r.1, y :: r.2)

/-- The textbook (direct form I) recurrence in exact arithmetic, from the history
`(x[n-1], x[n-2], y[n-1], y[n-2])`: returns the outputs. -/
def df1_real (c : CoeffsReal) : ℝ × ℝ × ℝ × ℝ → List ℝ → List ℝ
  | _, [] => []
  | (x1, x2, y1, y2), x :: xs =>
    let y := c.b0 * x + c.b1 * x1 + c.b2 * x2 - c.a1 * y1 - c.a2 * y2
    y :: df1_real c (x, x1, y, y1) xs

/-- The transposed-form state that carries the same information as a textbook history. -/
def stateOfHistory (c : CoeffsReal) : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ
  | (x1, x2, y1, y2) =>
    (c.b1 * x1 + c.b2 * x2 - c.a1 * y1 - c.a2 * y2, c.b2 * x1 - c.a2 * y1)

/-- From the state matching a history, the transposed form gives exactly the textbook outputs. -/
theorem filt_real_eq_df1_real (c : CoeffsReal) (xs : List ℝ) (h : ℝ × ℝ × ℝ × ℝ) :
    (filt_real c (stateOfHistory c h) xs).2 = df1_real c h xs := by
  induction xs generalizing h with
  | nil => obtain ⟨x1, x2, y1, y2⟩ := h; rfl
  | cons x xs ih =>
    obtain ⟨x1, x2, y1, y2⟩ := h
    have hy : c.b0 * x + (c.b1 * x1 + c.b2 * x2 - c.a1 * y1 - c.a2 * y2) =
        c.b0 * x + c.b1 * x1 + c.b2 * x2 - c.a1 * y1 - c.a2 * y2 := by ring
    simp only [stateOfHistory, filt_real, df1_real, hy]
    congr 1
    rw [← ih (x, x1, c.b0 * x + c.b1 * x1 + c.b2 * x2 - c.a1 * y1 - c.a2 * y2, y1)]
    simp only [stateOfHistory]
    congr 3
    ring

/-- From a zero state, the transposed form gives exactly the textbook outputs with zero history:
the impulse response, step response and every other output agree. -/
theorem filt_real_eq_df1_real_zero (c : CoeffsReal) (xs : List ℝ) :
    (filt_real c (0, 0) xs).2 = df1_real c (0, 0, 0, 0) xs := by
  have h := filt_real_eq_df1_real c xs (0, 0, 0, 0)
  simp only [stateOfHistory, mul_zero, sub_zero, add_zero] at h
  exact h

end conjure_dsp_lib.biquad

end
