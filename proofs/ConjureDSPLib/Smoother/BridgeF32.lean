module

public import ConjureDSPLib.Smoother.SpecF32
public import ConjureDSPLib.Smoother.Block
public import ConjureDSPLib.FloatFacts
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz

/-!
# The smoother in f32: from one step to real numbers

`process_f32` computes `c = 1 - a` once, then each step `s + c * (x - s)` (`process_f32_spec` in
`SpecF32.lean`). This file relates both to exact real arithmetic:

1. `coeff_f32_error`: the stored `c` is within `u·|1 - a| + η` of `1 - a` (`a` standing for its
   value), and `coeff_f32_exact`: when the value of `a` is between 1/2 and 2, `c` is exactly
   `1 - a` (Sterbenz's lemma).
2. `step_f32_error`: one step, with three roundings (the difference, the product and the sum), is
   within `stepErr` of the exact step `s + c·(x - s)` with the stored `c`.
-/

@[expose] public section

open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.smoother

/-- The binary32 number 1 is finite. -/
theorem one_isFinite_f32 : (1 : Float32).isFinite = true := by decide

/-- The binary32 number 1 has the value 1. -/
theorem real_f32_one : real_f32 1 = 1 := by
  unfold real_f32
  have : (ofFloat32 (1 : Float32) : Binary32) = 1 := by decide
  rw [this, toReal_one]

/-- When `a` is finite and `|1 - v| ≤ 2`, where `v` is the value of `a` (for example when
`|v| ≤ 1`), `1 - a` is finite. -/
theorem isFinite_one_sub_f32 (a : Float32) (ha : a.isFinite = true) (h : |1 - real_f32 a| ≤ 2) :
    (1 - a).isFinite = true := by
  refine isFinite_sub_f32 1 a one_isFinite_f32 ha ?_
  rw [real_f32_one, maxFinite_f32_eq]
  have : (2 : ℝ) ≤ (2 ^ 24 - 1) * 2 ^ 104 := by
    have : (1 : ℝ) ≤ 2 ^ 104 := one_le_pow₀ (by norm_num)
    calc (2 : ℝ) ≤ (2 ^ 24 - 1) * 1 := by norm_num
      _ ≤ (2 ^ 24 - 1) * 2 ^ 104 := mul_le_mul_of_nonneg_left this (by norm_num)
  exact h.trans this

/-- When `a` is finite and its value is at most 1 in size, `1 - a` is finite. -/
theorem isFinite_one_sub_f32_of_abs_le_one (a : Float32) (ha : a.isFinite = true)
    (ha1 : |real_f32 a| ≤ 1) : (1 - a).isFinite = true := by
  refine isFinite_one_sub_f32 a ha ?_
  have := abs_le.mp ha1
  rw [abs_le]; constructor <;> linarith

/-- **The stored coefficient, f32.** When `a` and `1 - a` are finite, the value of `1 - a` in
binary32 is within `u·|1 - v| + η` of `1 - v`, where `v` is the value of `a`. -/
theorem coeff_f32_error (a : Float32) (ha : a.isFinite = true) (hc : (1 - a).isFinite = true) :
    |real_f32 (1 - a) - (1 - real_f32 a)| ≤
      unitRoundoff_f32 * |1 - real_f32 a| + underflowErr_f32 := by
  have h := abs_real_sub_sub_le_f32 1 a one_isFinite_f32 ha hc
  rwa [real_f32_one] at h

/-- **The stored coefficient is exact for `1/2 ≤ A ≤ 2`, f32.** When `a` is finite and its value
`v` satisfies `1/2 ≤ v ≤ 2` (for example a slow smoother's `a` near 1), `1 - a` is computed with
no rounding error: its value is exactly `1 - v` (Sterbenz's lemma). -/
theorem coeff_f32_exact (a : Float32) (ha : a.isFinite = true) (h1 : 1 / 2 ≤ real_f32 a)
    (h2 : real_f32 a ≤ 2) : real_f32 (1 - a) = 1 - real_f32 a := by
  have hc : (1 - a).isFinite = true :=
    isFinite_one_sub_f32 a ha (by rw [abs_le]; constructor <;> linarith)
  have h := isFinite_ofFloat32 _ hc
  have hgen : ∀ v : Float32, v.isFinite = true →
      Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix
        (Model.fexpOf FloatFormat.binary32) (real_f32 v) :=
    fun v hv => Model.toReal_genericFormat_of_isFinite _ (isFinite_ofFloat32 v hv)
  have e : real_f32 (1 - a) =
      Model.roundAt FloatFormat.binary32 (real_f32 1 - real_f32 a) := by
    unfold real_f32
    rw [ofFloat32_sub_of_isFinite 1 a one_isFinite_f32 ha] at h ⊢
    exact toReal_sub_eq_roundAt h
  rw [e, Model.roundAt_sub_eq_of_sterbenz FloatFormat.binary32 (hgen 1 one_isFinite_f32)
    (hgen a ha) (by rw [real_f32_one]; linarith) (by rw [real_f32_one]; linarith), real_f32_one]

/-- **One step of the f32 smoother.** When `c`, `s`, `x`, the rounded difference `x - s`, the
rounded product `c * (x - s)` and the result are all finite (no overflow), one step
`s + c * (x - s)` (three roundings: the difference, the product, the sum) differs from the exact
step `S + C·(X - S)` by at most `stepErr (1 - C) u η S X`, where `C`, `S`, `X` are the values of
`c`, `s`, `x`, and `u = 2⁻²⁴`, `η` binary32's rounding constants. -/
theorem step_f32_error (c s x : Float32)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hx : x.isFinite = true)
    (hd : (x - s).isFinite = true) (hp : (c * (x - s)).isFinite = true)
    (hr : (s + c * (x - s)).isFinite = true) :
    |real_f32 (s + c * (x - s)) - (real_f32 s + real_f32 c * (real_f32 x - real_f32 s))| ≤
      stepErr (1 - real_f32 c) unitRoundoff_f32 underflowErr_f32 (real_f32 s) (real_f32 x) := by
  have h1 := abs_real_sub_sub_le_f32 x s hx hs hd
  have h2 := abs_real_mul_sub_le_f32 c (x - s) hc hd hp
  have h3 := abs_real_add_sub_le_f32 s (c * (x - s)) hs hp hr
  unfold stepErr prodErr diffErr
  rw [sub_sub_cancel]
  set C := real_f32 c
  set S := real_f32 s
  set X := real_f32 x
  set D := real_f32 (x - s)
  set P := real_f32 (c * (x - s))
  set Y := real_f32 (s + c * (x - s))
  set u := unitRoundoff_f32
  set η := underflowErr_f32
  have hu : 0 ≤ u := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ η := (Model.underflowErrorAt_pos _).le
  have hD : |D| ≤ |X - S| + (u * |X - S| + η) := by
    calc |D| = |(X - S) + (D - (X - S))| := by ring_nf
      _ ≤ |X - S| + |D - (X - S)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hPe : |P - C * (X - S)| ≤
      u * |C| * (|X - S| + (u * |X - S| + η)) + η + |C| * (u * |X - S| + η) := by
    have e : P - C * (X - S) = (P - C * D) + C * (D - (X - S)) := by ring
    rw [e]
    calc |(P - C * D) + C * (D - (X - S))| ≤ |P - C * D| + |C * (D - (X - S))| :=
          abs_add_le _ _
      _ = |P - C * D| + |C| * |D - (X - S)| := by rw [abs_mul C]
      _ ≤ (u * (|C| * |D|) + η) + |C| * (u * |X - S| + η) := by
          rw [abs_mul C D] at h2
          gcongr
      _ ≤ (u * (|C| * (|X - S| + (u * |X - S| + η))) + η) + |C| * (u * |X - S| + η) := by
          gcongr
      _ = _ := by ring
  have hSP : |S + P| ≤ |S + C * (X - S)| +
      (u * |C| * (|X - S| + (u * |X - S| + η)) + η + |C| * (u * |X - S| + η)) := by
    calc |S + P| = |(S + C * (X - S)) + (P - C * (X - S))| := by ring_nf
      _ ≤ |S + C * (X - S)| + |P - C * (X - S)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have e : Y - (S + C * (X - S)) = (Y - (S + P)) + (P - C * (X - S)) := by ring
  rw [e]
  calc |(Y - (S + P)) + (P - C * (X - S))| ≤ |Y - (S + P)| + |P - C * (X - S)| :=
        abs_add_le _ _
    _ ≤ (u * |S + P| + η) + |P - C * (X - S)| := by linarith
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left hSP hu
      linarith

end conjure_dsp_lib.smoother

end
