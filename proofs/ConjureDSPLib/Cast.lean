module

public import ConjureDSPLib.FloatFacts
public import ConjureDSPLib.Code.Funs
public import Mathlib.Algebra.Order.Floor.Semifield
public import FloatLib.Floats.Formats.IEEE754.Native.Model.Representation

/-!
# Rust's `as usize` on floats

Aeneas translates `x as usize`, for a float `x`, to `Float.toUScalar .Usize x` (and
`Float32.toUScalar .Usize x`), which is Lean's own conversion: round toward zero, NaN to 0, and
saturate at the largest `usize`. This file proves, for every finite `x`, that the result is the
integer part of the value of `x`, `⌊x⌋₊` (0 for a negative `x`), capped at the largest `usize`
(`toUScalar_usize_val_f64`, `toUScalar_usize_val_f32`).
-/

@[expose] public section

open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange
open Float.Model.UnpackedFloat

namespace conjure_dsp_lib

/-- Shifting an extended mantissa right by `k` bits divides its mantissa by `2^k`. -/
theorem mantissa_shiftRight (em : ExtendedMantissa) (k : ℕ) :
    (em >>> k).mantissa = em.mantissa / 2 ^ k := by
  induction k with
  | zero =>
    show (Nat.repeat ExtendedMantissa.shiftRightOne 0 em).mantissa = _
    simp [Nat.repeat]
  | succ k ih =>
    show (Nat.repeat ExtendedMantissa.shiftRightOne (k + 1) em).mantissa = _
    rw [Nat.repeat]
    show (ExtendedMantissa.shiftRightOne (em >>> k)).mantissa = _
    rw [ExtendedMantissa.shiftRightOne, ih, Nat.div_div_eq_div_mul, pow_succ]

/-- Lean's rounding of a positive `m·2^e` toward zero is `m·2^max(e, 0) / 2^max(-e, 0)`. -/
theorem roundToInt_positive (m : ℕ) (e : ℤ) :
    roundToInt .positive m e = ((m * 2 ^ e.toNat / 2 ^ (-e).toNat : ℕ) : ℤ) := by
  unfold roundToInt
  simp only [decreaseExponent, shiftToExponent, ExtendedMantissa.ofMantissaAndAccuracy]
  rw [mantissa_shiftRight]
  simp [Sign.apply, Nat.shiftLeft_eq]
  rw [show (max e 0 - e).toNat = (-e).toNat by omega]

/-- Lean's rounding of a negative `-(m·2^e)` toward zero is at most 0. -/
theorem roundToInt_negative_toNat (m : ℕ) (e : ℤ) : (roundToInt .negative m e).toNat = 0 := by
  unfold roundToInt
  simp [Sign.apply]

/-- The integer part of `m·2^e`, for a natural `m`, is `m·2^max(e, 0) / 2^max(-e, 0)`. -/
theorem floor_mul_zpow (m : ℕ) (e : ℤ) :
    ⌊(m : ℝ) * 2 ^ e⌋₊ = m * 2 ^ e.toNat / 2 ^ (-e).toNat := by
  rcases le_or_gt 0 e with he | he
  · have h1 : (-e).toNat = 0 := by omega
    have h2 : (2 : ℝ) ^ e = ((2 ^ e.toNat : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Int.toNat_of_nonneg he]
    rw [h1, pow_zero, Nat.div_one, h2, ← Nat.cast_mul, Nat.floor_natCast]
  · have h1 : e.toNat = 0 := by omega
    have h3 : (((-e).toNat : ℕ) : ℤ) = -e := Int.toNat_of_nonneg (by omega)
    have h2 : (2 : ℝ) ^ e = 1 / ((2 ^ (-e).toNat : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, one_div, ← zpow_natCast, h3, zpow_neg, inv_inv]
    rw [h1, pow_zero, mul_one, h2, mul_one_div, Nat.floor_div_eq_div]

/-- Lean's conversion to `usize` of an unpacked finite float is the integer part of its value,
capped at the largest `usize`. -/
theorem toUSize_toNat_of_isFinite (x : Float.Model.UnpackedFloat) (hfin : x.isFinite = true) :
    x.toUSize.toNat = min ⌊Model.unpackedToReal x⌋₊ (USize.size - 1) := by
  unfold Float.Model.UnpackedFloat.toUSize
  have hc : ∀ n : ℕ, (USize.ofNatClamp n).toNat = min n (USize.size - 1) := fun n => by
    show (BitVec.ofNatClamp System.Platform.numBits n).toNat = _
    rw [BitVec.toNat_ofNatClamp, USize.size_eq_two_pow]
  cases x with
  | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hfin
  | infinity s => simp [Float.Model.UnpackedFloat.isFinite] at hfin
  | zero s =>
    -- `toInt` of a zero is 0 by definition (unfolding `toInt` with `simp` would add its equation
    -- lemmas, which mention NaN, to this module).
    show (USize.ofNatClamp (0 : ℤ).toNat).toNat = _
    rw [hc, Int.toNat_zero, Model.unpackedToReal_zero, Nat.floor_zero]
  | finite s m e hm =>
    rw [Model.unpackedToReal_finite, Formats.Flocq.bpow_binaryRadix, hc]
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    have hp : (0 : ℝ) < 2 ^ e := zpow_pos (by norm_num) e
    cases s with
    | negative =>
      simp only [Model.modelSignBit, ite_true]
      show min (roundToInt .negative m e).toNat _ = _
      rw [roundToInt_negative_toNat, Nat.floor_eq_zero.mpr (by nlinarith [mul_pos hmr hp])]
    | positive =>
      simp only [Model.modelSignBit, Bool.false_eq_true, ite_false, one_mul]
      show min (roundToInt .positive m e).toNat _ = _
      rw [roundToInt_positive, Int.toNat_natCast, floor_mul_zpow]

/-- The value of a binary64 number is the value of Lean's unpacked form of it. -/
theorem real_f64_eq_unpack (d : Float) :
    real_f64 d = Model.unpackedToReal d.toModel.unpack := by
  unfold real_f64
  rw [show toReal (ofFloat d : Binary64) = Model.toReal (toModel (ofFloat d : Binary64)) from rfl]
  rw [Model.toReal_eq_unpackedToReal_toModel (by decide), toModel_ofFloat]
  rfl

/-- The value of a binary32 number is the value of Lean's unpacked form of it. -/
theorem real_f32_eq_unpack (d : Float32) :
    real_f32 d = Model.unpackedToReal d.toModel.unpack := by
  unfold real_f32
  rw [show toReal (ofFloat32 d : Binary32) = Model.toReal (toModel (ofFloat32 d : Binary32))
    from rfl]
  rw [Model.toReal_eq_unpackedToReal_toModel (by decide), toModel_ofFloat32]
  rfl

open Aeneas Aeneas.Std in
/-- **`d as usize` for a finite `f64`.** For every finite `d`, the translated `d as usize` is the
integer part `⌊D⌋₊` of the value `D` of `d` (0 when `D < 1`, negative `D` included), capped at
the largest `usize`. -/
theorem toUScalar_usize_val_f64 (d : Float) (hd : d.isFinite = true) :
    (Float.toUScalar .Usize d).val = min ⌊real_f64 d⌋₊ (USize.size - 1) := by
  rw [real_f64_eq_unpack]
  exact toUSize_toNat_of_isFinite _ (by simpa only [Float.isFinite, Float.Model.isFinite] using hd)

open Aeneas Aeneas.Std in
/-- **`d as usize` for a finite `f32`.** The same as `toUScalar_usize_val_f64`. -/
theorem toUScalar_usize_val_f32 (d : Float32) (hd : d.isFinite = true) :
    (Float32.toUScalar .Usize d).val = min ⌊real_f32 d⌋₊ (USize.size - 1) := by
  rw [real_f32_eq_unpack]
  exact toUSize_toNat_of_isFinite _
    (by simpa only [Float32.isFinite, Float32.Model.isFinite] using hd)

end conjure_dsp_lib

end
