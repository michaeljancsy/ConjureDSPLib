module

public import ConjureDSPLib.Delay.SpecF64
public import ConjureDSPLib.Delay.Interp
public import ConjureDSPLib.Delay.Cast
public import ConjureDSPLib.Gain.BridgeF64
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Sterbenz

/-!
# The interpolated delay read in f64

About `read_interp_f64` from `src/delay.rs`, as Aeneas translated it. Write `L` for the buffer's
length and `p` for the position. This file proves:

1. `read_interp_f64_short_buffer`, `read_interp_f64_ok`: with `L < 5` it returns `0`; it never
   fails, for every buffer, position and delay.
2. `read_interp_f64_spec`: for `L ≥ 5`, with `(n, t) = interpPoint_f64 L delay` (the sample index
   and the fraction, as the code computes them, `2 ≤ n ≤ L - 3` by `interpPoint_f64_fst_le`), the
   result is exactly `lagrange4_f64 t xm1 x0 x1 x2`, where `xm1`, `x0`, `x1`, `x2` are the buffer's
   elements at `(p + L - k) mod L` for `k = n - 1, n, n + 1, n + 2`: the samples `read_f64` returns
   at those delays (`read_f64_spec`).
3. `read_interp_f64_frac`: for a finite `delay` of value `D`, `5 ≤ L ≤ 2^53`, the fraction `t` is
   finite with value between 0 and 1: `n = 2`, `t = 0` when `D < 2`; `n = ⌊D⌋` and `t = D - n`
   exactly when `2 ≤ D < L - 2`; and `n = L - 3`, `t = 1` when `D ≥ L - 2`.
4. `read_interp_f64_whole`, `read_interp_f64_whole_eq_read`: at a whole-number delay
   `2 ≤ D ≤ L - 2`, with `L ≤ 2^53` and every sample in the buffer finite, the result has the same
   value as the sample at delay `D`, the one `read_f64` returns.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange
open conjure_dsp_lib.gain (castNat_f64 usize_toFloat_eq_castNat_f64)

namespace conjure_dsp_lib.delay

/-- The sample index `n` and the fraction `t` that `read_interp_f64` uses, for a buffer of length
`L`: with `whole` the translated `delay as usize`, `(2, 0)` if `whole < 2`, `(L - 3, 1)` if
`whole > L - 3`, and `(whole, delay - castNat_f64 whole)` otherwise. -/
def interpPoint_f64 (L : ℕ) (delay : Float) : ℕ × Float :=
  let whole := (Float.toUScalar .Usize delay).val
  if whole < 2 then (2, 0) else if L - 3 < whole then (L - 3, 1)
  else (whole, delay - castNat_f64 whole)

/-- The four-point Lagrange formula, as the code computes it in binary64: weights
`-(t·(t - 1)·(t - 2))/6`, `(t + 1)·(t - 1)·(t - 2)·0.5`, `-((t + 1)·t·(t - 2))·0.5` and
`(t + 1)·t·(t - 1)/6`, each product left to right, then
`((wm1·xm1 + w0·x0) + w1·x1) + w2·x2`. -/
def lagrange4_f64 (t xm1 x0 x1 x2 : Float) : Float :=
  -(t * (t - 1) * (t - 2)) / 6 * xm1 + (t + 1) * (t - 1) * (t - 2) * 0.5 * x0 +
    -((t + 1) * t * (t - 2)) * 0.5 * x1 + (t + 1) * t * (t - 1) / 6 * x2

/-- The branch of `read_interp_f64` that computes `(n, t)` never fails and gives
`interpPoint_f64`. -/
theorem interpPoint_f64_spec (buffer : Slice Float) (delay : Float) (hL : 5 ≤ buffer.length) :
    (if Float.toUScalar .Usize delay < 2#usize then ok (2#usize, (Float.ofBits 0))
      else do
        let i ← Slice.len buffer - 3#usize
        if Float.toUScalar .Usize delay > i then ok (i, (Float.ofBits 4607182418800017408))
        else ok (Float.toUScalar .Usize delay,
          Float.sub delay (UScalar.toFloat (Float.toUScalar .Usize delay)))) ⦃ nt =>
      nt.1.val = (interpPoint_f64 buffer.length delay).1 ∧
        nt.2 = (interpPoint_f64 buffer.length delay).2 ⦄ := by
  have hlv : (Slice.len buffer).val = buffer.length := Slice.len_val buffer
  unfold interpPoint_f64
  split
  · rename_i h
    have : (Float.toUScalar .Usize delay).val < 2 := by scalar_tac
    simp only [this, ite_true, WP.spec_ok]
    exact ⟨rfl, rfl⟩
  · rename_i h
    have h2 : ¬ (Float.toUScalar .Usize delay).val < 2 := by scalar_tac
    simp only [h2, ite_false]
    step*
    · have h3 : buffer.length - 3 < (Float.toUScalar .Usize delay).val := by scalar_tac
      simp only [h3, ite_true]
      exact ⟨by scalar_tac, rfl⟩
    · have h3 : ¬ buffer.length - 3 < (Float.toUScalar .Usize delay).val := by scalar_tac
      simp only [h3, ite_false, usize_toFloat_eq_castNat_f64]
      and_intros <;> trivial

/-- `2 ≤ n ≤ L - 3`, for `L ≥ 5`. -/
theorem interpPoint_f64_fst_le (L : ℕ) (delay : Float) (hL : 5 ≤ L) :
    2 ≤ (interpPoint_f64 L delay).1 ∧ (interpPoint_f64 L delay).1 ≤ L - 3 := by
  unfold interpPoint_f64
  dsimp only
  split_ifs <;> simp <;> omega

/-- **What it reads and computes.** For `L = buffer.length ≥ 5`, with
`(n, t) = interpPoint_f64 L delay`: `read_interp_f64` never fails, and returns exactly
`lagrange4_f64 t xm1 x0 x1 x2`, where `xm1`, `x0`, `x1` and `x2` are the buffer's elements at
`(position + L - k) mod L` for `k = n - 1`, `n`, `n + 1` and `n + 2` (the samples `read_f64`
returns at those delays, `read_f64_spec`). -/
theorem read_interp_f64_spec (buffer : Slice Float) (position : Std.Usize) (delay : Float)
    (hL : 5 ≤ buffer.length) :
    read_interp_f64 buffer position delay ⦃ y =>
      ∃ xm1 x0 x1 x2,
        buffer.val[(position.val + buffer.length - ((interpPoint_f64 buffer.length delay).1 - 1)) %
          buffer.length]? = some xm1 ∧
        buffer.val[(position.val + buffer.length - (interpPoint_f64 buffer.length delay).1) %
          buffer.length]? = some x0 ∧
        buffer.val[(position.val + buffer.length - ((interpPoint_f64 buffer.length delay).1 + 1)) %
          buffer.length]? = some x1 ∧
        buffer.val[(position.val + buffer.length - ((interpPoint_f64 buffer.length delay).1 + 2)) %
          buffer.length]? = some x2 ∧
        y = lagrange4_f64 (interpPoint_f64 buffer.length delay).2 xm1 x0 x1 x2 ⦄ := by
  have hlv : (Slice.len buffer).val = buffer.length := Slice.len_val buffer
  obtain ⟨hn2, hnL⟩ := interpPoint_f64_fst_le buffer.length delay hL
  unfold read_interp_f64
  have hne : ¬ (Slice.len buffer < 5#usize) := by scalar_tac
  simp only [hne, ite_false, lift, bind_ok]
  apply WP.spec_bind (interpPoint_f64_spec buffer delay hL)
  intro nt hnt
  obtain ⟨n, t⟩ := nt
  obtain ⟨hn, ht⟩ := hnt
  simp only at hn ht
  set N := (interpPoint_f64 buffer.length delay).1 with hN
  have hL0 : 0 < buffer.length := by omega
  step*
  apply WP.spec_bind (tap_index_spec buffer.len w k buffer.length position.val hlv hL0 w_post
    (by omega))
  rintro r ⟨hr, hrL⟩
  step*
  apply WP.spec_bind (wrap_index_spec buffer.len i buffer.length (position.val + buffer.length - k.val)
    hlv hL0 (by omega))
  rintro r1 ⟨hr1, hr1L⟩
  step*
  apply WP.spec_bind (wrap_index_spec buffer.len i1 buffer.length
    (position.val + buffer.length - k.val + 1) hlv hL0 (by omega))
  rintro r2 ⟨hr2, hr2L⟩
  step*
  apply WP.spec_bind (wrap_index_spec buffer.len i2 buffer.length
    (position.val + buffer.length - k.val + 1 + 1) hlv hL0 (by omega))
  rintro r3 ⟨hr3, hr3L⟩
  step*
  have hk : k.val = N + 2 := by omega
  have getv : ∀ (j : ℕ) (hj : j < buffer.length), buffer.val[j]? = some buffer.val[j] :=
    fun j hj => List.getElem?_eq_getElem hj
  refine ⟨xm1, x0, x1, x2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show position.val + buffer.length - (N - 1) =
      position.val + buffer.length - k.val + 1 + 1 + 1 by omega, ← hr3, xm1_post]
    exact getv _ hr3L
  · rw [show position.val + buffer.length - N =
      position.val + buffer.length - k.val + 1 + 1 by omega, ← hr2, x0_post]
    exact getv _ hr2L
  · rw [show position.val + buffer.length - (N + 1) =
      position.val + buffer.length - k.val + 1 by omega, ← hr1, x1_post]
    exact getv _ hr1L
  · rw [show position.val + buffer.length - (N + 2) =
      position.val + buffer.length - k.val by omega, ← hr, x2_post]
    exact getv _ hrL
  · rw [← ht]
    rfl

/-- With fewer than 5 samples in the buffer, `read_interp_f64` never fails and returns `0`. -/
theorem read_interp_f64_short_buffer (buffer : Slice Float) (position : Std.Usize)
    (delay : Float) (hL : buffer.length < 5) : read_interp_f64 buffer position delay = ok 0 := by
  have h : Slice.len buffer < 5#usize := by scalar_tac
  simp only [read_interp_f64, h, ite_true]
  rfl

/-- `read_interp_f64` never fails, for every buffer, position and delay. -/
theorem read_interp_f64_ok (buffer : Slice Float) (position : Std.Usize) (delay : Float) :
    ∃ y, read_interp_f64 buffer position delay = ok y := by
  rcases Nat.lt_or_ge buffer.length 5 with h | h
  · exact ⟨_, read_interp_f64_short_buffer buffer position delay h⟩
  · obtain ⟨y, hy, -⟩ := exists_ok_of_spec (read_interp_f64_spec buffer position delay h)
    exact ⟨y, hy⟩

/-- The value of a binary64 number from its unpacked form, for the constants below. -/
theorem real_f64_zero : real_f64 0 = 0 := by
  rw [real_f64_eq_unpack, show (0 : Float).toModel.unpack = .zero .positive by rfl,
    Model.unpackedToReal_zero]

theorem real_f64_one' : real_f64 1 = 1 := by
  rw [real_f64_eq_unpack,
    show (1 : Float).toModel.unpack = .finite .positive 4503599627370496 (-52) (by decide) by rfl,
    Model.unpackedToReal_finite, Formats.Flocq.bpow_binaryRadix]
  norm_num

/-- **The fraction.** For a finite `delay` of value `D` and `5 ≤ L ≤ 2^53` (and `L` at most the
number of `usize` values, as every buffer length is), with `(n, t) = interpPoint_f64 L delay`:
`t` is finite and its value is between 0 and 1. When `D < 2`, `n = 2` and `t` has value 0; when
`2 ≤ D < L - 2`, `n = ⌊D⌋` and `t` has value exactly `D - n`, the fractional part of `D`; when
`D ≥ L - 2`, `n = L - 3` and `t` has value 1. -/
theorem read_interp_f64_frac (L : ℕ) (delay : Float) (hL : 5 ≤ L) (hL53 : L ≤ 2 ^ 53)
    (hLs : L ≤ USize.size) (hfin : delay.isFinite = true) :
    (interpPoint_f64 L delay).2.isFinite = true ∧
      0 ≤ real_f64 (interpPoint_f64 L delay).2 ∧ real_f64 (interpPoint_f64 L delay).2 ≤ 1 ∧
      (real_f64 delay < 2 →
        (interpPoint_f64 L delay).1 = 2 ∧ real_f64 (interpPoint_f64 L delay).2 = 0) ∧
      (2 ≤ real_f64 delay → real_f64 delay < (L : ℝ) - 2 →
        (interpPoint_f64 L delay).1 = ⌊real_f64 delay⌋₊ ∧
          real_f64 (interpPoint_f64 L delay).2 = real_f64 delay - ⌊real_f64 delay⌋₊) ∧
      ((L : ℝ) - 2 ≤ real_f64 delay →
        (interpPoint_f64 L delay).1 = L - 3 ∧ real_f64 (interpPoint_f64 L delay).2 = 1) := by
  have hw := toUScalar_usize_val_f64 delay hfin
  set D := real_f64 delay with hD
  set W := ⌊D⌋₊ with hW
  have hzero : (0 : Float).isFinite = true := by decide
  have hone : (1 : Float).isFinite = true := by decide
  have hL2 : ((L - 2 : ℕ) : ℝ) = (L : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  -- The three cases, by the value of `D`.
  have low : D < 2 → interpPoint_f64 L delay = (2, 0) := by
    intro h
    have : W < 2 := by
      rcases lt_or_ge D 0 with h0 | h0
      · rw [hW, Nat.floor_eq_zero.mpr (by linarith)]; omega
      · exact (Nat.floor_lt h0).mpr (by exact_mod_cast h)
    unfold interpPoint_f64
    simp only [hw, show min W (USize.size - 1) < 2 by omega, ite_true]
  have high : (L : ℝ) - 2 ≤ D → interpPoint_f64 L delay = (L - 3, 1) := by
    intro h
    have : L - 2 ≤ W := Nat.le_floor (by rw [hL2]; exact h)
    unfold interpPoint_f64
    simp only [hw, show ¬ min W (USize.size - 1) < 2 by omega,
      show L - 3 < min W (USize.size - 1) by omega, ite_true, ite_false]
  have mid : 2 ≤ D → D < (L : ℝ) - 2 →
      interpPoint_f64 L delay = (W, delay - castNat_f64 W) ∧ 2 ≤ W ∧ W ≤ L - 3 := by
    intro h1 h2
    have hW2 : 2 ≤ W := Nat.le_floor (by exact_mod_cast h1)
    have hWL : W < L - 2 := (Nat.floor_lt (by linarith)).mpr (by rw [hL2]; exact h2)
    refine ⟨?_, hW2, by omega⟩
    unfold interpPoint_f64
    simp only [hw, show min W (USize.size - 1) = W by omega, show ¬ W < 2 by omega,
      show ¬ L - 3 < W by omega, ite_false]
  -- In the middle case the subtraction is exact (Sterbenz's lemma).
  have midval : 2 ≤ D → D < (L : ℝ) - 2 →
      (delay - castNat_f64 W).isFinite = true ∧ real_f64 (delay - castNat_f64 W) = D - W := by
    intro h1 h2
    obtain ⟨-, hW2, hWL⟩ := mid h1 h2
    have hWle : W ≤ 2 ^ 53 := by omega
    have hcf := gain.isFinite_castNat_f64 W (hWle.trans (by norm_num))
    have hcr := gain.real_castNat_f64 W hWle
    have hfl : (W : ℝ) ≤ D := Nat.floor_le (by linarith)
    have hlt : D < W + 1 := Nat.lt_floor_add_one D
    have hW2r : (2 : ℝ) ≤ W := by exact_mod_cast hW2
    have hsf : (delay - castNat_f64 W).isFinite = true := by
      apply isFinite_sub_f64 _ _ hfin hcf
      rw [hcr, ← hD, abs_of_nonneg (by linarith)]
      have hm := maxFinite_f64_ge
      have h1020 : (1 : ℝ) ≤ 2 ^ 1020 := one_le_pow₀ (by norm_num)
      have hlt1 : D - W ≤ 1 := by linarith
      generalize (2 : ℝ) ^ 1020 = B at hm h1020
      linarith
    refine ⟨hsf, ?_⟩
    have h := isFinite_ofFloat _ hsf
    have hgen : ∀ v : Float, v.isFinite = true →
        Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix
          (Model.fexpOf FloatFormat.binary64) (real_f64 v) :=
      fun v hv => Model.toReal_genericFormat_of_isFinite _ (isFinite_ofFloat v hv)
    have e : real_f64 (delay - castNat_f64 W) =
        Model.roundAt FloatFormat.binary64 (real_f64 delay - real_f64 (castNat_f64 W)) := by
      unfold real_f64
      rw [ofFloat_sub_of_isFinite delay _ hfin hcf] at h ⊢
      exact toReal_sub_eq_roundAt h
    rw [e, Model.roundAt_sub_eq_of_sterbenz FloatFormat.binary64 (hgen delay hfin) (hgen _ hcf)
      (by rw [hcr]; linarith) (by rw [hcr]; linarith), hcr]
  refine ⟨?_, ?_, ?_, fun h => by rw [low h]; exact ⟨rfl, real_f64_zero⟩, fun h1 h2 => ?_,
    fun h => by rw [high h]; exact ⟨rfl, real_f64_one'⟩⟩
  · rcases lt_or_ge D 2 with h1 | h1
    · rw [low h1]; exact hzero
    rcases lt_or_ge D ((L : ℝ) - 2) with h2 | h2
    · rw [(mid h1 h2).1]; exact (midval h1 h2).1
    · rw [high h2]; exact hone
  · rcases lt_or_ge D 2 with h1 | h1
    · rw [low h1, real_f64_zero]
    rcases lt_or_ge D ((L : ℝ) - 2) with h2 | h2
    · rw [(mid h1 h2).1, (midval h1 h2).2]; simp only [sub_nonneg]; exact Nat.floor_le (by linarith)
    · rw [high h2, real_f64_one']; norm_num
  · rcases lt_or_ge D 2 with h1 | h1
    · rw [low h1, real_f64_zero]; norm_num
    rcases lt_or_ge D ((L : ℝ) - 2) with h2 | h2
    · rw [(mid h1 h2).1, (midval h1 h2).2]
      have := Nat.lt_floor_add_one D
      linarith
    · rw [high h2, real_f64_one']
  · rw [(mid h1 h2).1]
    exact ⟨rfl, (midval h1 h2).2⟩

/-! ### At a whole-number delay -/

/-- A finite binary64 value times a finite zero is a finite zero. -/
theorem real_mul_of_real_eq_zero_f64 (w x : Float) (hw : w.isFinite = true)
    (hx : x.isFinite = true) (h0 : real_f64 w = 0) :
    (w * x).isFinite = true ∧ real_f64 (w * x) = 0 := by
  have hf : (w * x).isFinite = true := by
    apply isFinite_mul_f64 _ _ hw hx
    rw [h0, zero_mul, abs_zero]
    exact (abs_nonneg _).trans (abs_real_le_maxFinite_f64 x hx)
  refine ⟨hf, ?_⟩
  rw [real_mul_f64 _ _ hw hx hf, h0, zero_mul]
  exact Model.roundAt_zero _

/-- A finite binary64 value times a finite one keeps its value. -/
theorem real_mul_of_real_eq_one_f64 (w x : Float) (hw : w.isFinite = true)
    (hx : x.isFinite = true) (h1 : real_f64 w = 1) :
    (w * x).isFinite = true ∧ real_f64 (w * x) = real_f64 x := by
  have hf : (w * x).isFinite = true := by
    apply isFinite_mul_f64 _ _ hw hx
    rw [h1, one_mul]
    exact abs_real_le_maxFinite_f64 x hx
  refine ⟨hf, ?_⟩
  rw [real_mul_f64 _ _ hw hx hf, h1, one_mul]
  exact Model.roundAt_toReal_eq _ (isFinite_ofFloat x hx)

/-- Adding a finite zero to a finite binary64 value, on either side, keeps its value. -/
theorem real_add_of_real_eq_zero_f64 (a b : Float) (ha : a.isFinite = true)
    (hb : b.isFinite = true) (h : real_f64 a = 0 ∨ real_f64 b = 0) :
    (a + b).isFinite = true ∧ real_f64 (a + b) = real_f64 a + real_f64 b := by
  have hs : ∃ c : Float, c.isFinite = true ∧ real_f64 c = real_f64 a + real_f64 b := by
    rcases h with h | h
    · exact ⟨b, hb, by rw [h, zero_add]⟩
    · exact ⟨a, ha, by rw [h, add_zero]⟩
  obtain ⟨c, hc, hcv⟩ := hs
  have hf : (a + b).isFinite = true := by
    apply isFinite_add_f64 _ _ ha hb
    rw [← hcv]; exact abs_real_le_maxFinite_f64 c hc
  refine ⟨hf, ?_⟩
  rw [real_add_f64 _ _ ha hb hf, ← hcv]
  exact Model.roundAt_toReal_eq _ (isFinite_ofFloat c hc)

/-- The value of a binary64 zero (either sign) is 0, and it is finite. -/
theorem zero_facts_f64 (w : Float) (s : Float.Model.UnpackedFloat.Sign)
    (h : w.toModel.unpack = .zero s) : w.isFinite = true ∧ real_f64 w = 0 := by
  refine ⟨?_, by rw [real_f64_eq_unpack, h, Model.unpackedToReal_zero]⟩
  simp only [Float.isFinite, Float.Model.isFinite, h, Float.Model.UnpackedFloat.isFinite]

/-- The binary64 number whose unpacked form is that of 1 is finite with value 1. -/
theorem one_facts_f64 (w : Float)
    (h : w.toModel.unpack = .finite .positive 4503599627370496 (-52) (by decide)) :
    w.isFinite = true ∧ real_f64 w = 1 := by
  refine ⟨?_, ?_⟩
  · simp only [Float.isFinite, Float.Model.isFinite, h, Float.Model.UnpackedFloat.isFinite]
  · rw [real_f64_eq_unpack, h, Model.unpackedToReal_finite, Formats.Flocq.bpow_binaryRadix]
    norm_num

/-- The weighted sum with weights of values `(0, 1, 0, 0)` (or `(0, 0, 1, 0)`) has the value of
`x0` (or `x1`), when every weight and sample is finite. -/
theorem combine_f64 (wm1 w0 w1 w2 xm1 x0 x1 x2 : Float) (hwm1 : wm1.isFinite = true)
    (hw0 : w0.isFinite = true) (hw1 : w1.isFinite = true) (hw2 : w2.isFinite = true)
    (hm1 : xm1.isFinite = true) (h0 : x0.isFinite = true) (h1 : x1.isFinite = true)
    (h2 : x2.isFinite = true) (rm1 : real_f64 wm1 = 0) (r2 : real_f64 w2 = 0)
    (hsel : (real_f64 w0 = 1 ∧ real_f64 w1 = 0) ∨ (real_f64 w0 = 0 ∧ real_f64 w1 = 1)) :
    (wm1 * xm1 + w0 * x0 + w1 * x1 + w2 * x2).isFinite = true ∧
      real_f64 (wm1 * xm1 + w0 * x0 + w1 * x1 + w2 * x2) =
        if real_f64 w0 = 1 then real_f64 x0 else real_f64 x1 := by
  obtain ⟨fm1, vm1⟩ := real_mul_of_real_eq_zero_f64 wm1 xm1 hwm1 hm1 rm1
  obtain ⟨f2, v2⟩ := real_mul_of_real_eq_zero_f64 w2 x2 hw2 h2 r2
  rcases hsel with ⟨r0, r1⟩ | ⟨r0, r1⟩
  · obtain ⟨f0, v0⟩ := real_mul_of_real_eq_one_f64 w0 x0 hw0 h0 r0
    obtain ⟨f1, v1⟩ := real_mul_of_real_eq_zero_f64 w1 x1 hw1 h1 r1
    obtain ⟨fa, va⟩ := real_add_of_real_eq_zero_f64 _ _ fm1 f0 (Or.inl vm1)
    obtain ⟨fb, vb⟩ := real_add_of_real_eq_zero_f64 _ _ fa f1 (Or.inr v1)
    obtain ⟨fc, vc⟩ := real_add_of_real_eq_zero_f64 _ _ fb f2 (Or.inr v2)
    refine ⟨fc, ?_⟩
    rw [vc, vb, va, vm1, v0, v1, v2, r0]
    simp
  · obtain ⟨f0, v0⟩ := real_mul_of_real_eq_zero_f64 w0 x0 hw0 h0 r0
    obtain ⟨f1, v1⟩ := real_mul_of_real_eq_one_f64 w1 x1 hw1 h1 r1
    obtain ⟨fa, va⟩ := real_add_of_real_eq_zero_f64 _ _ fm1 f0 (Or.inl vm1)
    obtain ⟨fb, vb⟩ := real_add_of_real_eq_zero_f64 _ _ fa f1 (Or.inl (by rw [va, vm1, v0]; ring))
    obtain ⟨fc, vc⟩ := real_add_of_real_eq_zero_f64 _ _ fb f2 (Or.inr v2)
    refine ⟨fc, ?_⟩
    rw [vc, vb, va, vm1, v0, v1, v2, r0]
    simp

set_option maxRecDepth 100000 in
/-- **At a fraction of 0.** When `t` is a zero (of either sign) and the four samples are finite,
`lagrange4_f64 t xm1 x0 x1 x2` is finite and has the value of `x0`. -/
theorem lagrange4_f64_zero (t xm1 x0 x1 x2 : Float) (s : Float.Model.UnpackedFloat.Sign)
    (ht : t.toModel.unpack = .zero s) (hm1 : xm1.isFinite = true) (h0 : x0.isFinite = true)
    (h1 : x1.isFinite = true) (h2 : x2.isFinite = true) :
    (lagrange4_f64 t xm1 x0 x1 x2).isFinite = true ∧
      real_f64 (lagrange4_f64 t xm1 x0 x1 x2) = real_f64 x0 := by
  have htz : t = Float.ofModel (Float.Model.pack (.zero s)) :=
    (ofModel_pack_eq_of_unpack_f64 t _ ht.symm).symm
  unfold lagrange4_f64
  -- `t` is `+0` or `-0`; each weight is a zero except `w0`, which unpacks as 1.
  have hw : (∃ s', (-(t * (t - 1) * (t - 2)) / 6).toModel.unpack = .zero s') ∧
      ((t + 1) * (t - 1) * (t - 2) * 0.5).toModel.unpack =
        .finite .positive 4503599627370496 (-52) (by decide) ∧
      (∃ s', (-((t + 1) * t * (t - 2)) * 0.5).toModel.unpack = .zero s') ∧
      (∃ s', ((t + 1) * t * (t - 1) / 6).toModel.unpack = .zero s') := by
    cases s
    · rw [show t = -(0 : Float) from htz.trans rfl]
      exact ⟨⟨_, rfl⟩, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
    · rw [show t = (0 : Float) from htz.trans rfl]
      exact ⟨⟨_, rfl⟩, rfl, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨⟨sm1, hsm1⟩, hw0, ⟨s1, hs1⟩, ⟨s2, hs2⟩⟩ := hw
  obtain ⟨fm1, rm1⟩ := zero_facts_f64 _ _ hsm1
  obtain ⟨f0', r0⟩ := one_facts_f64 _ hw0
  obtain ⟨f1', r1⟩ := zero_facts_f64 _ _ hs1
  obtain ⟨f2', r2⟩ := zero_facts_f64 _ _ hs2
  have h := combine_f64 _ _ _ _ xm1 x0 x1 x2 fm1 f0' f1' f2' hm1 h0 h1 h2 rm1 r2
    (Or.inl ⟨r0, r1⟩)
  rw [r0, ite_eq_left_iff.mpr (fun h => absurd rfl h)] at h
  exact h

set_option maxRecDepth 100000 in
/-- **At a fraction of 1.** When `t` is the binary64 number 1 and the four samples are finite,
`lagrange4_f64 t xm1 x0 x1 x2` is finite and has the value of `x1`. -/
theorem lagrange4_f64_one (xm1 x0 x1 x2 : Float) (hm1 : xm1.isFinite = true)
    (h0 : x0.isFinite = true) (h1 : x1.isFinite = true) (h2 : x2.isFinite = true) :
    (lagrange4_f64 1 xm1 x0 x1 x2).isFinite = true ∧
      real_f64 (lagrange4_f64 1 xm1 x0 x1 x2) = real_f64 x1 := by
  unfold lagrange4_f64
  obtain ⟨sm1, hsm1⟩ : ∃ s', (-((1 : Float) * (1 - 1) * (1 - 2)) / 6).toModel.unpack = .zero s' :=
    ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s', (((1 : Float) + 1) * (1 - 1) * (1 - 2) * 0.5).toModel.unpack =
    .zero s' := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s', (((1 : Float) + 1) * 1 * (1 - 1) / 6).toModel.unpack = .zero s' :=
    ⟨_, rfl⟩
  have hw1 : (-(((1 : Float) + 1) * 1 * (1 - 2)) * 0.5).toModel.unpack =
      .finite .positive 4503599627370496 (-52) (by decide) := rfl
  obtain ⟨fm1, rm1⟩ := zero_facts_f64 _ _ hsm1
  obtain ⟨f0', r0⟩ := zero_facts_f64 _ _ hs0
  obtain ⟨f1', r1⟩ := one_facts_f64 _ hw1
  obtain ⟨f2', r2⟩ := zero_facts_f64 _ _ hs2
  have h := combine_f64 _ _ _ _ xm1 x0 x1 x2 fm1 f0' f1' f2' hm1 h0 h1 h2 rm1 r2
    (Or.inr ⟨r0, r1⟩)
  rw [r0, ite_eq_right (by norm_num)] at h
  exact h

/-- **At a whole-number delay.** For `5 ≤ L ≤ 2^53`, a finite `delay` whose value is a whole
number `D` with `2 ≤ D ≤ L - 2`, and every sample in the buffer finite: `read_interp_f64` never
fails, and returns a finite value equal to the value of the buffer's element at
`(position + L - D) mod L`, the sample at delay `D`. -/
theorem read_interp_f64_whole (buffer : Slice Float) (position : Std.Usize) (delay : Float)
    (D : ℕ) (hL : 5 ≤ buffer.length) (hL53 : buffer.length ≤ 2 ^ 53)
    (hfin : delay.isFinite = true) (hD : real_f64 delay = D) (hD2 : 2 ≤ D)
    (hDL : D ≤ buffer.length - 2) (hbuf : ∀ x ∈ buffer.val, x.isFinite = true) :
    read_interp_f64 buffer position delay ⦃ y => y.isFinite = true ∧
      ∃ x, buffer.val[(position.val + buffer.length - D) % buffer.length]? = some x ∧
        real_f64 y = real_f64 x ⦄ := by
  have hLs : buffer.length ≤ USize.size := by
    have := buffer.property
    have h2 : Std.Usize.max < USize.size := by
      rw [Std.Usize.max, USize.size_eq_two_pow]; scalar_tac
    simp only [Slice.length]; omega
  obtain ⟨-, -, -, -, hmid, hhigh⟩ :=
    read_interp_f64_frac buffer.length delay hL hL53 hLs hfin
  apply WP.spec_mono (read_interp_f64_spec buffer position delay hL)
  rintro y ⟨xm1, x0, x1, x2, em1, e0, e1, e2, hy⟩
  have fin : ∀ {j : ℕ} {x : Float}, buffer.val[j]? = some x → x.isFinite = true :=
    fun hj => hbuf _ (List.mem_of_getElem? hj)
  rw [hD] at hmid hhigh
  have hDr : (2 : ℝ) ≤ D := by exact_mod_cast hD2
  rcases Nat.lt_or_ge D (buffer.length - 2) with hlt | hge
  · -- A delay below `L - 2`: `n = D` and `t` has value 0.
    have hlt' : (D : ℝ) < (buffer.length : ℝ) - 2 := by
      have : ((buffer.length - 2 : ℕ) : ℝ) = (buffer.length : ℝ) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [← this]; exact_mod_cast hlt
    obtain ⟨hn, ht⟩ := hmid hDr hlt'
    rw [Nat.floor_natCast] at hn ht
    rw [sub_self] at ht
    have htf := (read_interp_f64_frac buffer.length delay hL hL53 hLs hfin).1
    obtain ⟨s, hs⟩ : ∃ s, (interpPoint_f64 buffer.length delay).2.toModel.unpack = .zero s := by
      have hfm : (interpPoint_f64 buffer.length delay).2.toModel.unpack.isFinite = true := by
        simpa only [Float.isFinite, Float.Model.isFinite] using htf
      rw [real_f64_eq_unpack] at ht
      cases hu : (interpPoint_f64 buffer.length delay).2.toModel.unpack with
      | zero s => exact ⟨s, rfl⟩
      | notANumber => simp [hu, Float.Model.UnpackedFloat.isFinite] at hfm
      | infinity s => simp [hu, Float.Model.UnpackedFloat.isFinite] at hfm
      | finite s m e hm =>
        exfalso
        rw [hu, Model.unpackedToReal_finite, Formats.Flocq.bpow_binaryRadix] at ht
        have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
        have hpos : (0 : ℝ) < m * 2 ^ e := mul_pos hm0 (zpow_pos (by norm_num) e)
        cases s <;> simp only [Model.modelSignBit, ite_true, ite_false, Bool.false_eq_true,
          one_mul, neg_mul] at ht <;> linarith
    rw [hn] at e0
    obtain ⟨hf, hv⟩ := lagrange4_f64_zero _ xm1 x0 x1 x2 s hs (fin em1) (fin e0) (fin e1) (fin e2)
    rw [hy]
    exact ⟨hf, x0, e0, hv⟩
  · -- The delay `L - 2`: `n = L - 3` and `t` is 1.
    have hD' : D = buffer.length - 2 := by omega
    have hge' : (buffer.length : ℝ) - 2 ≤ D := by
      rw [hD', Nat.cast_sub (by omega)]; norm_num
    obtain ⟨hn, -⟩ := hhigh hge'
    have ht1 : (interpPoint_f64 buffer.length delay).2 = 1 := by
      have := Nat.floor_natCast (R := ℝ) D
      unfold interpPoint_f64
      have hw := toUScalar_usize_val_f64 delay hfin
      rw [hD, Nat.floor_natCast] at hw
      simp only [hw, show ¬ min D (USize.size - 1) < 2 by omega,
        show buffer.length - 3 < min D (USize.size - 1) by omega, ite_true, ite_false]
    rw [hn, show buffer.length - 3 + 1 = D by omega] at e1
    rw [ht1] at hy
    obtain ⟨hf, hv⟩ := lagrange4_f64_one xm1 x0 x1 x2 (fin em1) (fin e0) (fin e1) (fin e2)
    rw [hy]
    exact ⟨hf, x1, e1, hv⟩

/-- **The same as `read_f64`.** Under the conditions of `read_interp_f64_whole`, for any
`usize` delay `d` with value `D`: `read_interp_f64` at `delay` and `read_f64` at `d` both never
fail, and return values that are equal as real numbers. -/
theorem read_interp_f64_whole_eq_read (buffer : Slice Float) (position : Std.Usize)
    (delay : Float) (d : Std.Usize) (hL : 5 ≤ buffer.length) (hL53 : buffer.length ≤ 2 ^ 53)
    (hfin : delay.isFinite = true) (hD : real_f64 delay = d.val) (hD2 : 2 ≤ d.val)
    (hDL : d.val ≤ buffer.length - 2) (hbuf : ∀ x ∈ buffer.val, x.isFinite = true) :
    ∃ y x, read_interp_f64 buffer position delay = ok y ∧ read_f64 buffer position d = ok x ∧
      real_f64 y = real_f64 x := by
  obtain ⟨y, hy, -, x, hx, hyx⟩ := exists_ok_of_spec
    (read_interp_f64_whole buffer position delay d.val hL hL53 hfin hD hD2 hDL hbuf)
  obtain ⟨x', hx', hxx⟩ := exists_ok_of_spec (read_f64_spec buffer position d (by omega))
  have hmin : min d.val (buffer.length - 1) = d.val := by omega
  rw [hmin, hx] at hxx
  cases hxx
  exact ⟨y, _, hy, hx', hyx⟩

end conjure_dsp_lib.delay

end
