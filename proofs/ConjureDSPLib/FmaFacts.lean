module

public import ConjureDSPLib.FloatFacts
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.AddSub
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.MulDiv
public import FloatLib.Floats.Formats.IEEE754.Native.Model.Representation

/-!
# Lean's fused multiply-add and FloatLib's rounding

Rust's `f64::mul_add` and `f32::mul_add` are translated by Aeneas to Lean's `Float.fma` and
`Float32.fma`, which compute `x * y + z` exactly and round once (Lean core's logical model,
`Float.Model.UnpackedFloat.fma`). FloatLib proves the same kind of link for Lean's `+`, `-`, `*`
and `/`, but not for `fma`. This file adds it:

* `real_fma_f64`, `real_fma_f32`: for finite operands and a finite result, the real value of
  `x.fma y z` is FloatLib's nearest-even rounding `roundAt` of the exact `x·y + z`. This is the
  rounding FloatLib's own `fma` is proved to compute (`Model.toReal_fma_eq_roundAt`).
* `abs_real_fma_sub_le_f64`, `abs_real_fma_sub_le_f32`: so one fused multiply-add is within
  `u·|x·y + z| + η` of the exact value, the same per-operation bound as one `+`, `-`, `*` or `/`.
* `isFinite_fma_f64`, `isFinite_fma_f32`: the result is finite when the exact `x·y + z` is at most
  the largest finite value in size.

The proof follows FloatLib's for addition (`Arithmetic/LeanModel/AddSub.lean`): when the three
operands are finite and nonzero, Lean's `fma` is Lean's `add` of the exact product, an unpacked
value with mantissa `m₁·m₂` and exponent `e₁ + e₂`, and the addend. FloatLib's lemma for that case
is private, so its proof is repeated here (`roundDyadic_addDyadic_eq_ofModel_add`).
-/

@[expose] public section

open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib

namespace FmaModel

open Float.Model.UnpackedFloat
open FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Lean's `round` of `|m|` with the sign of `m` is Lean's `normalize` of `m`. (FloatLib's private
`round_natAbs_eq_normalize`, with the same proof.) -/
theorem round_natAbs_eq_normalize (spec : Float.Model.Format) (mantissa exponent : Int) :
    Float.Model.UnpackedFloat.round spec (modelSign (mantissa < 0))
        mantissa.natAbs exponent =
      Float.Model.UnpackedFloat.normalize spec mantissa exponent .positive := by
  unfold Float.Model.UnpackedFloat.normalize
  split <;> rename_i hcompare
  · have hnegative := Int.compare_eq_lt.mp hcompare
    have habs : mantissa.natAbs = (-mantissa).toNat := by omega
    simp [modelSign, hnegative, habs]
  · have hzero := Int.compare_eq_eq.mp hcompare
    subst mantissa
    simp [modelSign]
  · have hpositive := Int.compare_eq_gt.mp hcompare
    have habs : mantissa.natAbs = mantissa.toNat := by omega
    simp [modelSign, not_lt.mpr hpositive.le, habs]

/-- Rounding FloatLib's exact sum of two aligned dyadics is packing Lean's `normalize` of the
signed sum of their mantissas. (FloatLib's private `round_addFields_eq_normalize`, with the same
proof.) -/
theorem round_addFields_eq_normalize
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Bool) (mantissa₁ mantissa₂ : Nat) (exponent : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂) :
    roundDyadic fmt
        (FloatLib.Numerics.Dyadic.addFields
          sign₁ mantissa₁ exponent sign₂ mantissa₂ exponent) =
      ofModel fmt
        (Float.Model.UnpackedFloat.normalize (FloatFormat.toModel fmt)
          ((modelSign sign₁).apply mantissa₁ + (modelSign sign₂).apply mantissa₂)
          exponent .positive) := by
  unfold FloatLib.Numerics.Dyadic.addFields
  simp only [beq_iff_eq, hmantissa₁.ne', hmantissa₂.ne', ite_false,
    le_refl, ite_true, sub_self, Int.toNat_zero]
  cases sign₁ <;> cases sign₂ <;>
    simp only [Bool.false_eq_true, eq_self, ite_false, ite_true,
      modelSign_false, modelSign_true, Sign.apply]
  all_goals
    split_ifs with hzero
    · simp only [roundDyadic, hfmt, ite_true, ieeeRoundDyadic,
        Bool.false_and, Bool.true_and, modelSign_false, modelSign_true,
        round_exact_zero]
      simp_all [Float.Model.UnpackedFloat.normalize]
      all_goals omega
    · simp only [roundDyadic, hfmt, ite_true, ieeeRoundDyadic]
      rw [← round_natAbs_eq_normalize]
      rfl

/-- For any two finite nonzero unpacked values (not only those unpacked from format words),
Lean's unpacked addition, packed, is FloatLib's rounding of the exact dyadic sum. (FloatLib's
private `round_addDyadic_eq_ofModel_add_finite`, with the same proof.) -/
theorem roundDyadic_addDyadic_eq_ofModel_add
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign₁ sign₂ : Sign) (mantissa₁ mantissa₂ : Nat) (exponent₁ exponent₂ : Int)
    (hmantissa₁ : 0 < mantissa₁) (hmantissa₂ : 0 < mantissa₂) :
    roundDyadic fmt
        (addDyadic
          ⟨modelSignBit sign₁, mantissa₁, exponent₁⟩
          ⟨modelSignBit sign₂, mantissa₂, exponent₂⟩) =
      ofModel fmt
        (Float.Model.UnpackedFloat.add (FloatFormat.toModel fmt)
          (.finite sign₁ mantissa₁ exponent₁ hmantissa₁)
          (.finite sign₂ mantissa₂ exponent₂ hmantissa₂)) := by
  have hsign (sign : Sign) : modelSign (modelSignBit sign) = sign := by
    cases sign <;> rfl
  by_cases hexponents : exponent₁ ≤ exponent₂
  · rw [addDyadic, FloatLib.Numerics.Dyadic.add_align_right_to_left_exponent
      _ _ _ _ _ _ hmantissa₁.ne' hexponents]
    have hshifted : 0 < mantissa₂ <<< (exponent₂ - exponent₁).toNat :=
      Nat.shiftLeft_pos_iff.mpr hmantissa₂
    simpa only [FloatLib.Numerics.Dyadic.add, Float.Model.UnpackedFloat.add,
      min_eq_left hexponents, Float.Model.UnpackedFloat.decreaseExponent,
      sub_self, Int.toNat_zero, Nat.shiftLeft_eq', Nat.shiftLeft_zero, hsign] using
      round_addFields_eq_normalize fmt hfmt (modelSignBit sign₁) (modelSignBit sign₂)
        mantissa₁ (mantissa₂ <<< (exponent₂ - exponent₁).toNat) exponent₁
        hmantissa₁ hshifted
  · have hlt : exponent₂ < exponent₁ := lt_of_not_ge hexponents
    rw [addDyadic, FloatLib.Numerics.Dyadic.add_align_left_to_right_exponent
      _ _ _ _ _ _ hmantissa₂.ne' hlt]
    have hshifted : 0 < mantissa₁ <<< (exponent₁ - exponent₂).toNat :=
      Nat.shiftLeft_pos_iff.mpr hmantissa₁
    simpa only [FloatLib.Numerics.Dyadic.add, Float.Model.UnpackedFloat.add,
      min_eq_right hlt.le, Float.Model.UnpackedFloat.decreaseExponent,
      sub_self, Int.toNat_zero, Nat.shiftLeft_eq', Nat.shiftLeft_zero, hsign] using
      round_addFields_eq_normalize fmt hfmt (modelSignBit sign₁) (modelSignBit sign₂)
        (mantissa₁ <<< (exponent₁ - exponent₂).toNat) mantissa₂ exponent₂
        hshifted hmantissa₂

/-- The sign bit of a product of signs is the exclusive or of the sign bits. -/
theorem modelSignBit_mul (s₁ s₂ : Sign) :
    modelSignBit (s₁ * s₂) = Bool.xor (modelSignBit s₁) (modelSignBit s₂) := by
  cases s₁ <;> cases s₂ <;> rfl

/-- A finite nonzero value unpacked from a word has the real value of its dyadic. -/
theorem toReal_of_toModel_eq_finite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) {s : Sign} {m : Nat} {e : Int} {hm : 0 < m}
    (hx : toModel x = .finite s m e hm) :
    toReal x = (⟨modelSignBit s, m, e⟩ : FloatLib.Numerics.Dyadic).toReal := by
  rw [toReal_eq_unpackedToReal_toModel hfmt x, hx]
  rfl

/-- A finite value unpacked from a word as a zero has the real value 0. -/
theorem toReal_of_toModel_eq_zero {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) {s : Sign} (hx : toModel x = .zero s) : toReal x = 0 := by
  rw [toReal_eq_unpackedToReal_toModel hfmt x, hx, unpackedToReal_zero]

/-! Lean's `fma` on zero operands, one equation per case the proofs below need. (Unfolding `fma`
with `simp` would add its equation lemmas to this module, and some of those mention NaN.) -/

theorem fma_zero_zero_zero (spec : Float.Model.Format) (s₁ s₂ s₃ : Sign) :
    Float.Model.UnpackedFloat.fma spec (.zero s₁) (.zero s₂) (.zero s₃) =
      if s₁ * s₂ == s₃ then .zero s₃ else .zero .positive := rfl

theorem fma_zero_finite_zero (spec : Float.Model.Format) (s₁ s₂ s₃ : Sign) (m₂ : Nat) (e₂ : Int)
    (h₂ : 0 < m₂) :
    Float.Model.UnpackedFloat.fma spec (.zero s₁) (.finite s₂ m₂ e₂ h₂) (.zero s₃) =
      if s₁ * s₂ == s₃ then .zero s₃ else .zero .positive := rfl

theorem fma_finite_zero_zero (spec : Float.Model.Format) (s₁ s₂ s₃ : Sign) (m₁ : Nat) (e₁ : Int)
    (h₁ : 0 < m₁) :
    Float.Model.UnpackedFloat.fma spec (.finite s₁ m₁ e₁ h₁) (.zero s₂) (.zero s₃) =
      if s₁ * s₂ == s₃ then .zero s₃ else .zero .positive := rfl

theorem fma_zero_zero_finite (spec : Float.Model.Format) (s₁ s₂ s₃ : Sign) (m₃ : Nat) (e₃ : Int)
    (h₃ : 0 < m₃) :
    Float.Model.UnpackedFloat.fma spec (.zero s₁) (.zero s₂) (.finite s₃ m₃ e₃ h₃) =
      .finite s₃ m₃ e₃ h₃ := rfl

theorem fma_zero_finite_finite (spec : Float.Model.Format) (s₁ s₂ s₃ : Sign) (m₂ m₃ : Nat)
    (e₂ e₃ : Int) (h₂ : 0 < m₂) (h₃ : 0 < m₃) :
    Float.Model.UnpackedFloat.fma spec (.zero s₁) (.finite s₂ m₂ e₂ h₂) (.finite s₃ m₃ e₃ h₃) =
      .finite s₃ m₃ e₃ h₃ := rfl

theorem fma_finite_zero_finite (spec : Float.Model.Format) (s₁ s₂ s₃ : Sign) (m₁ m₃ : Nat)
    (e₁ e₃ : Int) (h₁ : 0 < m₁) (h₃ : 0 < m₃) :
    Float.Model.UnpackedFloat.fma spec (.finite s₁ m₁ e₁ h₁) (.zero s₂) (.finite s₃ m₃ e₃ h₃) =
      .finite s₃ m₃ e₃ h₃ := rfl

/-- **Lean's fused multiply-add rounds once.** For a conventional IEEE format, three finite
words, the first two and the third unpacked by Lean's model, and a finite result: the real value
of the packed result of Lean's unpacked `fma` is FloatLib's nearest-even rounding of the exact
`x·y + z`. The addend must be a canonical word (every word imported from a Lean float is). -/
theorem toReal_ofModel_fma_toModel_eq_roundAt {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y z : Model fmt) (hx : isFinite x = true) (hy : isFinite y = true)
    (hz : isFinite z = true) (hzc : IsModelCanonical z)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.fma (FloatFormat.toModel fmt)
            (toModel x) (toModel y) (toModel z))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.fma (FloatFormat.toModel fmt)
            (toModel x) (toModel y) (toModel z))) =
      roundAt fmt (toReal x * toReal y + toReal z) := by
  have hzero := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  have hxm : (toModel x).isFinite = true := by rw [isFinite_toModel hfmt]; exact hx
  have hym : (toModel y).isFinite = true := by rw [isFinite_toModel hfmt]; exact hy
  have hzm : (toModel z).isFinite = true := by rw [isFinite_toModel hfmt]; exact hz
  -- The addend alone: packing its own unpacked form gives it back.
  have hzself : toReal (ofModel fmt (toModel z)) = toReal z := by
    change toReal (canonicalizeModel z) = toReal z
    rw [canonicalizeModel_eq_self z hzc]
  have hzround : roundAt fmt (toReal z) = toReal z := roundAt_toReal_eq z hz
  obtain ⟨ux, hux⟩ : ∃ ux, toModel x = ux := ⟨_, rfl⟩
  obtain ⟨uy, huy⟩ : ∃ uy, toModel y = uy := ⟨_, rfl⟩
  obtain ⟨uz, huz⟩ : ∃ uz, toModel z = uz := ⟨_, rfl⟩
  rw [hux, huy, huz] at hfinite ⊢
  rw [hux] at hxm
  rw [huy] at hym
  rw [huz] at hzm hzself
  cases ux with
  | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hxm
  | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hxm
  | zero s₁ =>
    rw [toReal_of_toModel_eq_zero hfmt x hux, zero_mul, zero_add]
    cases uy with
    | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hym
    | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hym
    | zero s₂ =>
      cases uz with
      | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | zero s₃ =>
        rw [toReal_of_toModel_eq_zero hfmt z huz, roundAt_zero]
        rw [fma_zero_zero_zero]
        split_ifs <;> exact toReal_ofModel_zero fmt hzero _
      | finite s₃ m₃ e₃ h₃ =>
        rw [fma_zero_zero_finite, hzround]; exact hzself
    | finite s₂ m₂ e₂ h₂ =>
      cases uz with
      | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | zero s₃ =>
        rw [toReal_of_toModel_eq_zero hfmt z huz, roundAt_zero]
        rw [fma_zero_finite_zero]
        split_ifs <;> exact toReal_ofModel_zero fmt hzero _
      | finite s₃ m₃ e₃ h₃ =>
        rw [fma_zero_finite_finite, hzround]; exact hzself
  | finite s₁ m₁ e₁ h₁ =>
    cases uy with
    | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hym
    | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hym
    | zero s₂ =>
      rw [toReal_of_toModel_eq_zero hfmt y huy, mul_zero, zero_add]
      cases uz with
      | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | zero s₃ =>
        rw [toReal_of_toModel_eq_zero hfmt z huz, roundAt_zero]
        rw [fma_finite_zero_zero]
        split_ifs <;> exact toReal_ofModel_zero fmt hzero _
      | finite s₃ m₃ e₃ h₃ =>
        rw [fma_finite_zero_finite, hzround]; exact hzself
    | finite s₂ m₂ e₂ h₂ =>
      have hxy : toReal x * toReal y =
          (⟨Bool.xor (modelSignBit s₁) (modelSignBit s₂), m₁ * m₂, e₁ + e₂⟩ :
            FloatLib.Numerics.Dyadic).toReal := by
        rw [toReal_of_toModel_eq_finite hfmt x hux, toReal_of_toModel_eq_finite hfmt y huy]
        exact (Dyadic.toReal_mul _ _).symm
      cases uz with
      | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | zero s₃ =>
        -- `x·y + 0` is Lean's product `x·y`.
        rw [toReal_of_toModel_eq_zero hfmt z huz, add_zero]
        have hmul : Float.Model.UnpackedFloat.fma (FloatFormat.toModel fmt)
            (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) (.zero s₃) =
            Float.Model.UnpackedFloat.mul (FloatFormat.toModel fmt) (toModel x) (toModel y) := by
          rw [hux, huy]; rfl
        rw [hmul] at hfinite ⊢
        exact toReal_ofModel_mul_toModel_eq_roundAt hfmt x y hfinite
      | finite s₃ m₃ e₃ h₃ =>
        -- `x·y + z` is Lean's sum of the exact product and `z`.
        have hpos : 0 < m₁ * m₂ := Nat.mul_pos h₁ h₂
        have hadd : Float.Model.UnpackedFloat.fma (FloatFormat.toModel fmt)
            (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) (.finite s₃ m₃ e₃ h₃) =
            Float.Model.UnpackedFloat.add (FloatFormat.toModel fmt)
              (.finite (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) hpos) (.finite s₃ m₃ e₃ h₃) := rfl
        rw [hadd, ← roundDyadic_addDyadic_eq_ofModel_add fmt hfmt] at hfinite ⊢
        rw [toReal_roundDyadic_eq_roundAt fmt hfmt _ hfinite, Dyadic.toReal_addDyadic,
          hxy, toReal_of_toModel_eq_finite hfmt z huz, modelSignBit_mul]

/-- With finite operands, Lean's `fma` is finite when the exact `x·y + z` is at most the largest
finite value in size. -/
theorem isFinite_ofModel_fma_toModel {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y z : Model fmt) (hx : isFinite x = true) (hy : isFinite y = true)
    (hz : isFinite z = true) (hzc : IsModelCanonical z)
    (hbound : |toReal x * toReal y + toReal z| ≤ toReal (posMaxFinite fmt)) :
    isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.fma (FloatFormat.toModel fmt)
            (toModel x) (toModel y) (toModel z))) = true := by
  have hzero := FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt
  have hxm : (toModel x).isFinite = true := by rw [isFinite_toModel hfmt]; exact hx
  have hym : (toModel y).isFinite = true := by rw [isFinite_toModel hfmt]; exact hy
  have hzm : (toModel z).isFinite = true := by rw [isFinite_toModel hfmt]; exact hz
  have hzself : isFinite (ofModel fmt (toModel z)) = true := by
    change isFinite (canonicalizeModel z) = true
    rw [canonicalizeModel_eq_self z hzc]; exact hz
  have hzeroFin (s : Sign) : isFinite (ofModel fmt (.zero s)) = true := by
    rw [← isFinite_toModel hfmt, toModel_ofModel_zero fmt]; rfl
  obtain ⟨ux, hux⟩ : ∃ ux, toModel x = ux := ⟨_, rfl⟩
  obtain ⟨uy, huy⟩ : ∃ uy, toModel y = uy := ⟨_, rfl⟩
  obtain ⟨uz, huz⟩ : ∃ uz, toModel z = uz := ⟨_, rfl⟩
  rw [hux, huy, huz]
  rw [hux] at hxm
  rw [huy] at hym
  rw [huz] at hzm hzself
  cases ux with
  | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hxm
  | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hxm
  | zero s₁ =>
    cases uy with
    | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hym
    | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hym
    | zero s₂ =>
      cases uz with
      | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | zero s₃ => rw [fma_zero_zero_zero]; split_ifs <;> exact hzeroFin _
      | finite s₃ m₃ e₃ h₃ => rw [fma_zero_zero_finite]; exact hzself
    | finite s₂ m₂ e₂ h₂ =>
      cases uz with
      | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | zero s₃ => rw [fma_zero_finite_zero]; split_ifs <;> exact hzeroFin _
      | finite s₃ m₃ e₃ h₃ => rw [fma_zero_finite_finite]; exact hzself
  | finite s₁ m₁ e₁ h₁ =>
    cases uy with
    | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hym
    | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hym
    | zero s₂ =>
      cases uz with
      | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | zero s₃ => rw [fma_finite_zero_zero]; split_ifs <;> exact hzeroFin _
      | finite s₃ m₃ e₃ h₃ => rw [fma_finite_zero_finite]; exact hzself
    | finite s₂ m₂ e₂ h₂ =>
      cases uz with
      | notANumber => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | infinity _ => simp [Float.Model.UnpackedFloat.isFinite] at hzm
      | zero s₃ =>
        have hmul : Float.Model.UnpackedFloat.fma (FloatFormat.toModel fmt)
            (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) (.zero s₃) =
            Float.Model.UnpackedFloat.mul (FloatFormat.toModel fmt) (toModel x) (toModel y) := by
          rw [hux, huy]; rfl
        rw [hmul, ← mul_eq_ofModel_mul_of_isFinite hfmt x y (by rw [hux]; rfl)
          (by rw [huy]; rfl)]
        refine isFinite_mul_of_abs_mul_le_posMaxFinite x y hfmt hx hy ?_
        rw [toReal_of_toModel_eq_zero hfmt z huz, add_zero] at hbound
        rw [← abs_mul]; exact hbound
      | finite s₃ m₃ e₃ h₃ =>
        have hpos : 0 < m₁ * m₂ := Nat.mul_pos h₁ h₂
        have hadd : Float.Model.UnpackedFloat.fma (FloatFormat.toModel fmt)
            (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂) (.finite s₃ m₃ e₃ h₃) =
            Float.Model.UnpackedFloat.add (FloatFormat.toModel fmt)
              (.finite (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) hpos) (.finite s₃ m₃ e₃ h₃) := rfl
        rw [hadd, ← roundDyadic_addDyadic_eq_ofModel_add fmt hfmt]
        refine isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite fmt hfmt _ ?_
        rw [Dyadic.toReal_addDyadic, modelSignBit_mul,
          Dyadic.toReal_mul ⟨modelSignBit s₁, m₁, e₁⟩ ⟨modelSignBit s₂, m₂, e₂⟩,
          ← toReal_of_toModel_eq_finite hfmt x hux, ← toReal_of_toModel_eq_finite hfmt y huy,
          ← toReal_of_toModel_eq_finite hfmt z huz]
        exact hbound

end FmaModel

open FmaModel

/-- FloatLib's binary64 word of `x.fma y z` is the packed result of Lean's unpacked `fma` of the
operands' words. -/
theorem toModel_ofFloat_fma (x y z : Float) :
    toModel (ofFloat (x.fma y z) : Binary64) =
      Model.ofModel FloatFormat.binary64
        (Float.Model.UnpackedFloat.fma (FloatFormat.toModel FloatFormat.binary64)
          (Model.toModel (toModel (ofFloat x : Binary64)))
          (Model.toModel (toModel (ofFloat y : Binary64)))
          (Model.toModel (toModel (ofFloat z : Binary64)))) := by
  rw [toModel_ofFloat, toModel_ofFloat, toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.fma x.toModel y.toModel z.toModel) = _
  rw [Float.Model.fma, Model.ofFloatModel_pack]
  rfl

/-- FloatLib's binary32 word of `x.fma y z` is the packed result of Lean's unpacked `fma` of the
operands' words. -/
theorem toModel_ofFloat32_fma (x y z : Float32) :
    toModel (ofFloat32 (x.fma y z) : Binary32) =
      Model.ofModel FloatFormat.binary32
        (Float.Model.UnpackedFloat.fma (FloatFormat.toModel FloatFormat.binary32)
          (Model.toModel (toModel (ofFloat32 x : Binary32)))
          (Model.toModel (toModel (ofFloat32 y : Binary32)))
          (Model.toModel (toModel (ofFloat32 z : Binary32)))) := by
  rw [toModel_ofFloat32, toModel_ofFloat32, toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.fma x.toModel y.toModel z.toModel) = _
  rw [Float32.Model.fma, Model.ofFloat32Model_pack]
  rfl

/-- **One rounding (binary64).** The real value of a finite fused multiply-add of finite binary64
numbers is the exact `x·y + z` rounded to nearest, ties to even. -/
theorem real_fma_f64 (x y z : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (hr : (x.fma y z).isFinite = true) :
    real_f64 (x.fma y z) =
      Model.roundAt FloatFormat.binary64 (real_f64 x * real_f64 y + real_f64 z) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64 toReal
  unfold isFinite at h
  rw [toModel_ofFloat_fma] at h ⊢
  exact toReal_ofModel_fma_toModel_eq_roundAt (by decide) _ _ _ (isFinite_ofFloat x hx)
    (isFinite_ofFloat y hy) (isFinite_ofFloat z hz) (Model.isModelCanonical_ofFloatModel _) h

/-- **One rounding (binary32).** The real value of a finite fused multiply-add of finite binary32
numbers is the exact `x·y + z` rounded to nearest, ties to even. -/
theorem real_fma_f32 (x y z : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (hr : (x.fma y z).isFinite = true) :
    real_f32 (x.fma y z) =
      Model.roundAt FloatFormat.binary32 (real_f32 x * real_f32 y + real_f32 z) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32 toReal
  unfold isFinite at h
  rw [toModel_ofFloat32_fma] at h ⊢
  exact toReal_ofModel_fma_toModel_eq_roundAt (by decide) _ _ _ (isFinite_ofFloat32 x hx)
    (isFinite_ofFloat32 y hy) (isFinite_ofFloat32 z hz)
    (Model.isModelCanonical_ofFloat32Model _) h

/-- Lean's binary64 `fma` and FloatLib's software `fma` of the imported operands have the same
real value when both are finite: both are the nearest-even rounding of `x·y + z`. -/
theorem real_fma_eq_floatLib_fma_f64 (x y z : Float) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hz : z.isFinite = true) (hr : (x.fma y z).isFinite = true)
    (hl : Model.isFinite (Model.fma (toModel (ofFloat x : Binary64))
      (toModel (ofFloat y : Binary64)) (toModel (ofFloat z : Binary64))) = true) :
    real_f64 (x.fma y z) =
      Model.toReal (Model.fma (toModel (ofFloat x : Binary64))
        (toModel (ofFloat y : Binary64)) (toModel (ofFloat z : Binary64))) := by
  rw [real_fma_f64 x y z hx hy hz hr, Model.toReal_fma_eq_roundAt _ _ _ (by decide) hl]
  rfl

/-- Lean's binary32 `fma` and FloatLib's software `fma` of the imported operands have the same
real value when both are finite. -/
theorem real_fma_eq_floatLib_fma_f32 (x y z : Float32) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hz : z.isFinite = true) (hr : (x.fma y z).isFinite = true)
    (hl : Model.isFinite (Model.fma (toModel (ofFloat32 x : Binary32))
      (toModel (ofFloat32 y : Binary32)) (toModel (ofFloat32 z : Binary32))) = true) :
    real_f32 (x.fma y z) =
      Model.toReal (Model.fma (toModel (ofFloat32 x : Binary32))
        (toModel (ofFloat32 y : Binary32)) (toModel (ofFloat32 z : Binary32))) := by
  rw [real_fma_f32 x y z hx hy hz hr, Model.toReal_fma_eq_roundAt _ _ _ (by decide) hl]
  rfl

/-- One binary64 fused multiply-add of finite numbers with a finite result is within
`u·|x·y + z| + η` of the exact `x·y + z`: the same bound as one `+`, `-`, `*` or `/`
(`abs_real_add_sub_le_f64` and the others). -/
theorem abs_real_fma_sub_le_f64 (x y z : Float) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hz : z.isFinite = true) (hr : (x.fma y z).isFinite = true) :
    |real_f64 (x.fma y z) - (real_f64 x * real_f64 y + real_f64 z)| ≤
      unitRoundoff_f64 * |real_f64 x * real_f64 y + real_f64 z| + underflowErr_f64 := by
  rw [real_fma_f64 x y z hx hy hz hr]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- One binary32 fused multiply-add of finite numbers with a finite result is within
`u·|x·y + z| + η` of the exact `x·y + z`. -/
theorem abs_real_fma_sub_le_f32 (x y z : Float32) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hz : z.isFinite = true) (hr : (x.fma y z).isFinite = true) :
    |real_f32 (x.fma y z) - (real_f32 x * real_f32 y + real_f32 z)| ≤
      unitRoundoff_f32 * |real_f32 x * real_f32 y + real_f32 z| + underflowErr_f32 := by
  rw [real_fma_f32 x y z hx hy hz hr]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- The fused multiply-add of finite `Float`s is finite when the exact `x·y + z` is at most the
largest finite value in size. -/
theorem isFinite_fma_f64 (x y z : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (h : |real_f64 x * real_f64 y + real_f64 z| ≤ maxFinite_f64) :
    (x.fma y z).isFinite = true := by
  rw [← isFinite_ofFloat_iff]
  unfold isFinite
  rw [toModel_ofFloat_fma]
  exact isFinite_ofModel_fma_toModel (by decide) _ _ _ (isFinite_ofFloat x hx)
    (isFinite_ofFloat y hy) (isFinite_ofFloat z hz) (Model.isModelCanonical_ofFloatModel _) h

/-- The fused multiply-add of finite `Float32`s is finite when the exact `x·y + z` is at most
the largest finite value in size. -/
theorem isFinite_fma_f32 (x y z : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : z.isFinite = true) (h : |real_f32 x * real_f32 y + real_f32 z| ≤ maxFinite_f32) :
    (x.fma y z).isFinite = true := by
  rw [← isFinite_ofFloat32_iff]
  unfold isFinite
  rw [toModel_ofFloat32_fma]
  exact isFinite_ofModel_fma_toModel (by decide) _ _ _ (isFinite_ofFloat32 x hx)
    (isFinite_ofFloat32 y hy) (isFinite_ofFloat32 z hz)
    (Model.isModelCanonical_ofFloat32Model _) h

/-! ## Negation

The fused filters negate a product before adding it (`b1.mul_add(x, -(a1 * y))`, the way clang
contracts `b1*x - a1*y`). Negation is exact. -/

/-- Negating a word and packing Lean's negation of its unpacked form have the same real value and
finiteness. -/
theorem toModel_ofModel_neg_toModel {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (X : Model fmt) :
    Model.toModel (Model.ofModel fmt (Float.Model.UnpackedFloat.neg (Model.toModel X))) =
      Model.toModel (Model.neg X) := by
  rw [← Model.toModel_neg hfmt]
  exact Model.toModel_canonicalizeModel _

/-- FloatLib's binary64 word of `-x` is the packed Lean negation of `x`'s unpacked word. -/
theorem toModel_ofFloat_neg (x : Float) :
    toModel (ofFloat (-x) : Binary64) =
      Model.ofModel FloatFormat.binary64
        (Float.Model.UnpackedFloat.neg (Model.toModel (toModel (ofFloat x : Binary64)))) := by
  rw [toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.neg x.toModel) = _
  rw [Float.Model.neg, Model.ofFloatModel_pack]
  rfl

/-- FloatLib's binary32 word of `-x` is the packed Lean negation of `x`'s unpacked word. -/
theorem toModel_ofFloat32_neg (x : Float32) :
    toModel (ofFloat32 (-x) : Binary32) =
      Model.ofModel FloatFormat.binary32
        (Float.Model.UnpackedFloat.neg (Model.toModel (toModel (ofFloat32 x : Binary32)))) := by
  rw [toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.neg x.toModel) = _
  rw [Float32.Model.neg, Model.ofFloat32Model_pack]
  rfl

/-- Packing Lean's negation of a finite word's unpacked form negates its real value. -/
theorem toReal_ofModel_neg_toModel {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (X : Model fmt) (hX : Model.isFinite X = true) :
    Model.toReal (Model.ofModel fmt (Float.Model.UnpackedFloat.neg (Model.toModel X))) =
      -Model.toReal X := by
  rw [Model.toReal_eq_unpackedToReal_toModel hfmt (Model.ofModel fmt _),
    toModel_ofModel_neg_toModel hfmt, ← Model.toReal_eq_unpackedToReal_toModel hfmt,
    Model.toReal_neg _ hX]

/-- Packing Lean's negation of a finite word's unpacked form gives a finite word. -/
theorem isFinite_ofModel_neg_toModel {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (X : Model fmt) (hX : Model.isFinite X = true) :
    Model.isFinite (Model.ofModel fmt (Float.Model.UnpackedFloat.neg (Model.toModel X))) =
      true := by
  rw [← Model.isFinite_toModel hfmt, toModel_ofModel_neg_toModel hfmt, Model.toModel_neg hfmt]
  rw [← Model.isFinite_toModel hfmt] at hX
  cases hu : Model.toModel X <;>
    simp_all [Float.Model.UnpackedFloat.neg, Float.Model.UnpackedFloat.isFinite]

/-- Negating a finite `Float` negates its real value exactly. -/
theorem real_neg_f64 (x : Float) (hx : x.isFinite = true) : real_f64 (-x) = -real_f64 x := by
  unfold real_f64 toReal
  rw [toModel_ofFloat_neg]
  exact toReal_ofModel_neg_toModel (by decide) _ (isFinite_ofFloat x hx)

/-- Negating a finite `Float32` negates its real value exactly. -/
theorem real_neg_f32 (x : Float32) (hx : x.isFinite = true) : real_f32 (-x) = -real_f32 x := by
  unfold real_f32 toReal
  rw [toModel_ofFloat32_neg]
  exact toReal_ofModel_neg_toModel (by decide) _ (isFinite_ofFloat32 x hx)

/-- The negation of a finite `Float` is finite. -/
theorem isFinite_neg_f64 (x : Float) (hx : x.isFinite = true) : (-x).isFinite = true := by
  rw [← isFinite_ofFloat_iff]
  unfold isFinite
  rw [toModel_ofFloat_neg]
  exact isFinite_ofModel_neg_toModel (by decide) _ (isFinite_ofFloat x hx)

/-- The negation of a finite `Float32` is finite. -/
theorem isFinite_neg_f32 (x : Float32) (hx : x.isFinite = true) : (-x).isFinite = true := by
  rw [← isFinite_ofFloat32_iff]
  unfold isFinite
  rw [toModel_ofFloat32_neg]
  exact isFinite_ofModel_neg_toModel (by decide) _ (isFinite_ofFloat32 x hx)

/-- One binary64 fused multiply-add `x.fma y (-q)`, computing `x·y - q`, of finite numbers with a
finite result is within `u·|x·y - q| + η` of the exact `x·y - q`. -/
theorem abs_real_fma_neg_sub_le_f64 (x y q : Float) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hq : q.isFinite = true) (hr : (x.fma y (-q)).isFinite = true) :
    |real_f64 (x.fma y (-q)) - (real_f64 x * real_f64 y - real_f64 q)| ≤
      unitRoundoff_f64 * |real_f64 x * real_f64 y - real_f64 q| + underflowErr_f64 := by
  have h := abs_real_fma_sub_le_f64 x y (-q) hx hy (isFinite_neg_f64 q hq) hr
  rwa [real_neg_f64 q hq, ← sub_eq_add_neg] at h

/-- One binary32 fused multiply-add `x.fma y (-q)`, computing `x·y - q`, of finite numbers with a
finite result is within `u·|x·y - q| + η` of the exact `x·y - q`. -/
theorem abs_real_fma_neg_sub_le_f32 (x y q : Float32) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hq : q.isFinite = true) (hr : (x.fma y (-q)).isFinite = true) :
    |real_f32 (x.fma y (-q)) - (real_f32 x * real_f32 y - real_f32 q)| ≤
      unitRoundoff_f32 * |real_f32 x * real_f32 y - real_f32 q| + underflowErr_f32 := by
  have h := abs_real_fma_sub_le_f32 x y (-q) hx hy (isFinite_neg_f32 q hq) hr
  rwa [real_neg_f32 q hq, ← sub_eq_add_neg] at h

/-- `x.fma y (-q)` of finite numbers is finite when `|x·y - q|` is at most the largest finite
value. -/
theorem isFinite_fma_neg_f64 (x y q : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hq : q.isFinite = true) (h : |real_f64 x * real_f64 y - real_f64 q| ≤ maxFinite_f64) :
    (x.fma y (-q)).isFinite = true := by
  refine isFinite_fma_f64 x y (-q) hx hy (isFinite_neg_f64 q hq) ?_
  rwa [real_neg_f64 q hq, ← sub_eq_add_neg]

/-- `x.fma y (-q)` of finite numbers is finite when `|x·y - q|` is at most the largest finite
value. -/
theorem isFinite_fma_neg_f32 (x y q : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hq : q.isFinite = true) (h : |real_f32 x * real_f32 y - real_f32 q| ≤ maxFinite_f32) :
    (x.fma y (-q)).isFinite = true := by
  refine isFinite_fma_f32 x y (-q) hx hy (isFinite_neg_f32 q hq) ?_
  rwa [real_neg_f32 q hq, ← sub_eq_add_neg]

end conjure_dsp_lib

end
