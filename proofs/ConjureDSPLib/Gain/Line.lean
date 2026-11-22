module

public import ConjureDSPLib.FloatFacts

/-!
# The gain ramp in real numbers

Facts about real numbers shared by both precisions' ramp proofs (`BridgeF64.lean`,
`BridgeF32.lean`): the straight line `S + (E - S)·i/n` the ramp follows, the error of one gain
and of the step built from four roundings, and the direction of a ramp built from FloatLib's
`roundAt` in any format.
-/

@[expose] public section

open FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.gain

/-- The straight line `S + (E - S)·i/n` that the error bounds below measure against is `S` at
`i = 0`. -/
theorem ramp_line_zero (S E : ℝ) (n : ℕ) : S + (E - S) * ((0 : ℕ) : ℝ) / n = S := by simp

/-- The straight line is `E - (E - S)/n` at the last sample, `i = n - 1`. -/
theorem ramp_line_last (S E : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    S + (E - S) * ((n - 1 : ℕ) : ℝ) / n = E - (E - S) / n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  rw [Nat.cast_sub hn]
  field_simp
  ring

/-- The straight line reaches `E` at `i = n`, one sample after the block. -/
theorem ramp_line_end (S E : ℝ) (n : ℕ) (hn : 1 ≤ n) : S + (E - S) * (n : ℝ) / n = E := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  field_simp
  ring

/-- **The size of a rounded value.** If `y` is within `u·|x| + η` of `x`, with `u ≤ 1/16`, then
`|y| ≤ (17/16)·|x| + η`. -/
theorem abs_rounded_le (u η x y : ℝ) (hu : u ≤ 1 / 16)
    (h : |y - x| ≤ u * |x| + η) : |y| ≤ 17 / 16 * |x| + η := by
  have h' := abs_sub_abs_le_abs_sub y x
  have : u * |x| ≤ 1 / 16 * |x| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  linarith

/-- The size of the rounded quotient `s` times `i`, for `0 ≤ i ≤ N`, when `s` is within
`u·|d/N| + η` of `d/N`. -/
theorem ramp_abs_si_le (u η d s N i : ℝ) (hu : u ≤ 1 / 16) (hη : 0 ≤ η)
    (hN : 1 ≤ N) (hi0 : 0 ≤ i) (hiN : i ≤ N)
    (e2 : |s - d / N| ≤ u * |d / N| + η) : |s * i| ≤ 17 / 16 * |d| + N * η := by
  have hN0 : 0 < N := by linarith
  have hdN : |d / N| = |d| / N := by rw [abs_div, abs_of_pos hN0]
  have hs : |s| ≤ 17 / 16 * (|d| / N) + η := by
    have h := abs_sub_abs_le_abs_sub s (d / N)
    have : u * (|d| / N) ≤ 1 / 16 * (|d| / N) :=
      mul_le_mul_of_nonneg_right hu (by positivity)
    rw [hdN] at e2 h
    linarith
  rw [abs_mul, abs_of_nonneg hi0]
  calc |s| * i ≤ (17 / 16 * (|d| / N) + η) * i := mul_le_mul_of_nonneg_right hs hi0
    _ = 17 / 16 * |d| * (i / N) + η * i := by field_simp
    _ ≤ 17 / 16 * |d| * 1 + η * N := by
        gcongr
        · exact (div_le_one hN0).mpr hiN
    _ = 17 / 16 * |d| + N * η := by ring

/-- **The error of one gain, in real numbers.** If `d`, `s`, `p` and `g` are the rounded
difference, quotient, product and sum, each within `u·|exact| + η` of the exact operation on the
rounded operands, then `g` is within `u·|S| + 5u·|D| + (2N + 4)·η` of `S + D·i/N`. -/
theorem ramp_error_real (u η S D d s p g N i : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 16)
    (hη : 0 ≤ η) (hN : 1 ≤ N) (hi0 : 0 ≤ i) (hiN : i ≤ N)
    (e1 : |d - D| ≤ u * |D| + η)
    (e2 : |s - d / N| ≤ u * |d / N| + η)
    (e3 : |p - s * i| ≤ u * |s * i| + η)
    (e4 : |g - (S + p)| ≤ u * |S + p| + η) :
    |g - (S + D * i / N)| ≤ u * |S| + 5 * u * |D| + (2 * N + 4) * η := by
  have hN0 : 0 < N := by linarith
  have hd := abs_rounded_le u η D d hu e1
  have hq := ramp_abs_si_le u η d s N i hu hη hN hi0 hiN e2
  have hp := abs_rounded_le u η (s * i) p hu e3
  -- The four pieces of the error.
  have t1 : |g - (S + p)| ≤ u * |S| + u * |p| + η := by
    have : u * |S + p| ≤ u * (|S| + |p|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) hu0
    linarith
  have t3 : |s * i - d * i / N| ≤ u * |d| + N * η := by
    have he : s * i - d * i / N = (s - d / N) * i := by field_simp
    rw [he, abs_mul, abs_of_nonneg hi0]
    have hdN : |d / N| = |d| / N := by rw [abs_div, abs_of_pos hN0]
    rw [hdN] at e2
    calc |s - d / N| * i ≤ (u * (|d| / N) + η) * i := mul_le_mul_of_nonneg_right e2 hi0
      _ = u * |d| * (i / N) + η * i := by field_simp
      _ ≤ u * |d| * 1 + η * N := by
          gcongr
          · exact (div_le_one hN0).mpr hiN
      _ = u * |d| + N * η := by ring
  have t4 : |d * i / N - D * i / N| ≤ u * |D| + η := by
    have he : d * i / N - D * i / N = (d - D) * (i / N) := by ring
    rw [he, abs_mul, abs_of_nonneg (div_nonneg hi0 hN0.le)]
    calc |d - D| * (i / N) ≤ |d - D| * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hN0).mpr hiN) (abs_nonneg _)
      _ ≤ u * |D| + η := by linarith
  have hsplit : g - (S + D * i / N) =
      (g - (S + p)) + (p - s * i) + (s * i - d * i / N) + (d * i / N - D * i / N) := by ring
  have htri : |g - (S + D * i / N)| ≤
      |g - (S + p)| + |p - s * i| + |s * i - d * i / N| + |d * i / N - D * i / N| := by
    rw [hsplit]
    have h1 := abs_add_le ((g - (S + p)) + (p - s * i) + (s * i - d * i / N))
      (d * i / N - D * i / N)
    have h2 := abs_add_le ((g - (S + p)) + (p - s * i)) (s * i - d * i / N)
    have h3 := abs_add_le (g - (S + p)) (p - s * i)
    linarith
  -- The sizes, multiplied by `u`.
  have a1 : u * |p| ≤ 17 / 16 * (u * |s * i|) + u * η := by
    have := mul_le_mul_of_nonneg_left hp hu0; linarith
  have a2 : u * |s * i| ≤ 17 / 16 * (u * |d|) + u * (N * η) := by
    have := mul_le_mul_of_nonneg_left hq hu0; linarith
  have a3 : u * |d| ≤ 17 / 16 * (u * |D|) + u * η := by
    have := mul_le_mul_of_nonneg_left hd hu0; linarith
  have b1 : u * η ≤ 1 / 16 * η := mul_le_mul_of_nonneg_right hu hη
  have b2 : u * (N * η) ≤ 1 / 16 * (N * η) := mul_le_mul_of_nonneg_right hu (by positivity)
  have b3 : 0 ≤ u * |D| := by positivity
  have b4 : 0 ≤ N * η := by positivity
  linarith

/-- **The error of the step, in real numbers.** If `d` is within `u·|D| + η` of `D` and `s`
within `u·|d/N| + η` of `d/N`, then `s` is within `3u·|D| + 3η` of `D/N`. -/
theorem ramp_step_error_real (u η D d s N : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 16)
    (hη : 0 ≤ η) (hN : 1 ≤ N)
    (e1 : |d - D| ≤ u * |D| + η)
    (e2 : |s - d / N| ≤ u * |d / N| + η) :
    |s - D / N| ≤ 3 * u * |D| + 3 * η := by
  have hN0 : 0 < N := by linarith
  have hd := abs_rounded_le u η D d hu e1
  have hdN : |d / N| = |d| / N := by rw [abs_div, abs_of_pos hN0]
  have hsplit : s - D / N = (s - d / N) + (d - D) / N := by field_simp; ring
  have h1 : |d| / N ≤ |d| := div_le_self (abs_nonneg _) hN
  have h2 : |(d - D) / N| ≤ |d - D| := by
    rw [abs_div, abs_of_pos hN0]; exact div_le_self (abs_nonneg _) hN
  have h3 : u * (|d| / N) ≤ u * |d| := mul_le_mul_of_nonneg_left h1 hu0
  have a3 : u * |d| ≤ 17 / 16 * (u * |D|) + u * η := by
    have := mul_le_mul_of_nonneg_left hd hu0; linarith
  have b1 : u * η ≤ 1 / 16 * η := mul_le_mul_of_nonneg_right hu hη
  have b3 : 0 ≤ u * |D| := by positivity
  rw [hdN] at e2
  rw [hsplit]
  have := abs_add_le (s - d / N) ((d - D) / N)
  linarith

/-- **The last gain, in real numbers.** If `g` is within `A` of the straight line at
`i = N - 1` and `s` within `B` of `(E - S)/N`, then `g` is within `A + B` of `E - s`. -/
theorem ramp_last_error_real (S E g s N A B : ℝ) (hN : N ≠ 0)
    (h1 : |g - (S + (E - S) * (N - 1) / N)| ≤ A) (h2 : |s - (E - S) / N| ≤ B) :
    |g - (E - s)| ≤ A + B := by
  have he : g - (E - s) = (g - (S + (E - S) * (N - 1) / N)) + (s - (E - S) / N) := by
    field_simp; ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **One step inside the block, in real numbers.** If `g1` and `g0` are within `A1` and `A0`
of the straight line at `i + 1` and `i`, and `s` within `B` of `(E - S)/N`, then `g1 - g0` is
within `A1 + A0 + B` of `s`. -/
theorem ramp_succ_sub_real (S E g0 g1 s N i A0 A1 B : ℝ) (hN : N ≠ 0)
    (h1 : |g1 - (S + (E - S) * (i + 1) / N)| ≤ A1) (h0 : |g0 - (S + (E - S) * i / N)| ≤ A0)
    (h2 : |s - (E - S) / N| ≤ B) : |g1 - g0 - s| ≤ A1 + A0 + B := by
  have he : g1 - g0 - s = (g1 - (S + (E - S) * (i + 1) / N)) - (g0 - (S + (E - S) * i / N)) -
      (s - (E - S) / N) := by field_simp; ring
  rw [he]
  have ha := abs_sub (g1 - (S + (E - S) * (i + 1) / N) - (g0 - (S + (E - S) * i / N)))
    (s - (E - S) / N)
  have hb := abs_sub (g1 - (S + (E - S) * (i + 1) / N)) (g0 - (S + (E - S) * i / N))
  linarith

/-- **The direction of the rounded ramp, in any format.** With `s` the rounded quotient of the
rounded `E - S` by the rounded `N ≥ 0`, and `x ≤ y`: the rounded gain
`roundAt (S + roundAt (s · roundAt x))` is at most the same at `y` when `S ≤ E`, and at least it
when `E ≤ S`. -/
theorem ramp_mono_roundAt (fmt : FloatFormat) (S E s N x y : ℝ) (hN : 0 ≤ N) (hxy : x ≤ y)
    (hs : s = Model.roundAt fmt (Model.roundAt fmt (E - S) / Model.roundAt fmt N)) :
    (S ≤ E → Model.roundAt fmt (S + Model.roundAt fmt (s * Model.roundAt fmt x)) ≤
        Model.roundAt fmt (S + Model.roundAt fmt (s * Model.roundAt fmt y))) ∧
      (E ≤ S → Model.roundAt fmt (S + Model.roundAt fmt (s * Model.roundAt fmt y)) ≤
        Model.roundAt fmt (S + Model.roundAt fmt (s * Model.roundAt fmt x))) := by
  have hn0 : 0 ≤ Model.roundAt fmt N := Model.roundAt_nonneg fmt hN
  have hxy' : Model.roundAt fmt x ≤ Model.roundAt fmt y := Model.roundAt_mono fmt hxy
  constructor
  · intro hSE
    have hs0 : 0 ≤ s := by
      rw [hs]
      exact Model.roundAt_nonneg fmt
        (div_nonneg (Model.roundAt_nonneg fmt (by linarith)) hn0)
    have h1 := Model.roundAt_mono fmt (mul_le_mul_of_nonneg_left hxy' hs0)
    apply Model.roundAt_mono fmt
    linarith
  · intro hES
    have hs0 : s ≤ 0 := by
      rw [hs]
      exact Model.roundAt_nonpos fmt (div_nonpos_of_nonpos_of_nonneg
        (Model.roundAt_nonpos fmt (by linarith)) hn0)
    have h1 := Model.roundAt_mono fmt (mul_le_mul_of_nonpos_left hxy' hs0)
    apply Model.roundAt_mono fmt
    linarith

end conjure_dsp_lib.gain
