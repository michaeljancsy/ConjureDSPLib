module

public import ConjureDSPLib.Gain.SpecF64
public import ConjureDSPLib.Gain.Line
public import ConjureDSPLib.FloatFacts

/-!
# The gain ramp in f64: from the code to real numbers

What `rampGain_f64` (the gain `ramp_f64` multiplies sample `i` by, `SpecF64.lean`) is worth:

1. `rampGain_f64_not_finite`: if `start` or `end` is infinite or NaN, or `end - start`
   overflows, every gain is infinite or NaN, the first included.
2. `rampGain_f64_zero`: when `end - start` is finite and `start` is not `-0`, the first gain is
   exactly `start`, bit for bit (`rampGain_f64_zero_negZero`: a `start` of `-0` may give `+0`).
3. `real_castNat_f64`: `castNat_f64 k` is exactly `k` for `k ≤ 2^53`;
   `real_castNat_f64_eq_roundAt`: for every `k ≤ 2^64` it is `k` rounded to nearest, ties to
   even.
4. `rampGain_f64_error`: with `start` and `end` finite and at most `2^1020` in size and
   `n ≤ 2^53`, each gain is within `u·|S| + 5u·|E - S| + (2n + 4)·η` of the straight
   line `S + (E - S)·i/n` (`u = 2^-53`, `η = 2^-1075`);
   `rampStep_f64_error`, `rampGain_f64_last_error`, `rampGain_f64_succ_sub` and
   `rampGain_f64_next_block` follow from it for the step, the last gain, the steps inside a block
   and the step into the next block.
5. `rampGain_f64_mono`: finite gains never go the wrong way: along the block they do not
   decrease when `start ≤ end`, and do not increase when `end ≤ start`.

The real-number arguments shared with `BridgeF32.lean` are in `Line.lean`; facts about
single float operations are in `FloatFacts.lean`.
-/

@[expose] public section

open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange
open Float.Model (UnpackedFloat Format)

namespace conjure_dsp_lib.gain

/-! ### Infinity and NaN -/

/-- **If an end is not finite, or `end - start` is not finite (it overflowed), every gain is
infinite or NaN**, for every block length `n` and every sample `i`, the first (`i = 0`)
included. -/
theorem rampGain_f64_not_finite (start «end» : Float) (n i : ℕ)
    (h : start.isFinite = false ∨ «end».isFinite = false ∨
      («end» - start).isFinite = false) :
    (rampGain_f64 start «end» n i).isFinite = false := by
  have hd : («end» - start).isFinite = false := by
    rcases h with h | h | h
    · exact isFinite_sub_eq_false_f64 _ _ (Or.inr h)
    · exact isFinite_sub_eq_false_f64 _ _ (Or.inl h)
    · exact h
  have hs := isFinite_div_eq_false_f64 _ (castNat_f64 n) hd
  have hp := isFinite_mul_eq_false_f64 _ (castNat_f64 i) (Or.inl hs)
  exact isFinite_add_eq_false_f64 _ _ (Or.inr hp)

/-- When a gain is finite, so are `start`, `end`, `end - start` and the step: the
contrapositive of `rampGain_f64_not_finite`. -/
theorem isFinite_of_rampGain_f64 (start «end» : Float) (n i : ℕ)
    (h : (rampGain_f64 start «end» n i).isFinite = true) :
    start.isFinite = true ∧ «end».isFinite = true ∧ («end» - start).isFinite = true ∧
      (rampStep_f64 start «end» n).isFinite = true := by
  have key : ∀ b : Bool, b ≠ false → b = true := by decide
  refine ⟨key _ fun hS => ?_, key _ fun hE => ?_, key _ fun hD => ?_, key _ fun hs => ?_⟩
  · rw [rampGain_f64_not_finite _ _ _ _ (Or.inl hS)] at h; exact absurd h (by decide)
  · rw [rampGain_f64_not_finite _ _ _ _ (Or.inr (Or.inl hE))] at h; exact absurd h (by decide)
  · rw [rampGain_f64_not_finite _ _ _ _ (Or.inr (Or.inr hD))] at h; exact absurd h (by decide)
  · rw [rampGain_f64_eq, isFinite_add_eq_false_f64 _ _
      (Or.inr (isFinite_mul_eq_false_f64 _ _ (Or.inl hs)))] at h
    exact absurd h (by decide)

/-! ### The first gain -/

/-- `castNat_f64 0` is `+0`. -/
theorem unpack_castNat_f64_zero : (castNat_f64 0).toModel.unpack = .zero .positive := by
  show (Float.Model.pack (UnpackedFloat.ofNat Format.binary64 0)).unpack = _
  rw [unpack_pack_f64]
  rfl

/-- A finite value times `castNat_f64 0` is a zero (`+0` or `-0`). -/
theorem unpack_mul_castNat_f64_zero (s : Float) (hs : s.isFinite = true) :
    ∃ τ, (s * castNat_f64 0).toModel.unpack = .zero τ := by
  show ∃ τ, (Float.Model.pack (UnpackedFloat.mul Format.binary64 s.toModel.unpack
    (castNat_f64 0).toModel.unpack)).unpack = _
  rw [unpack_pack_f64, unpack_castNat_f64_zero]
  simp only [Float.isFinite, Float.Model.isFinite] at hs
  cases h : s.toModel.unpack <;> simp_all [UnpackedFloat.mul, UnpackedFloat.isFinite]

/-- When the step is finite, the first gain is exactly `start` (as bits, so also its sign),
unless `start` is `-0` (bits `0x8000000000000000`). (A finite step needs `start` to be finite.) -/
theorem rampGain_f64_zero_of_step (start «end» : Float) (n : ℕ)
    (hs : (rampStep_f64 start «end» n).isFinite = true)
    (hz : start.toBits ≠ 0x8000000000000000) : rampGain_f64 start «end» n 0 = start := by
  obtain ⟨τ, hτ⟩ := unpack_mul_castNat_f64_zero _ hs
  exact add_zero_of_ne_negZero_f64 _ _ τ hτ hz

/-- When the step is finite and `start` is `-0` (bits `0x8000000000000000`), the first gain is `+0`
(bits `0`) or `-0`. -/
theorem rampGain_f64_zero_of_step_negZero (start «end» : Float) (n : ℕ)
    (hs : (rampStep_f64 start «end» n).isFinite = true)
    (hz : start.toBits = 0x8000000000000000) :
    (rampGain_f64 start «end» n 0).toBits = 0 ∨
      (rampGain_f64 start «end» n 0).toBits = 0x8000000000000000 := by
  obtain ⟨τ, hτ⟩ := unpack_mul_castNat_f64_zero _ hs
  have hu : start.toModel.unpack = .zero .negative := by
    simp only [Float.toBits] at hz
    simp only [Float.Model.unpack, hz]
    rfl
  have hg : (rampGain_f64 start «end» n 0).toModel.unpack =
      .zero (if UnpackedFloat.Sign.negative = τ then .negative else .positive) := by
    show (Float.Model.pack (UnpackedFloat.add Format.binary64 start.toModel.unpack
      (rampStep_f64 start «end» n * castNat_f64 0).toModel.unpack)).unpack = _
    rw [unpack_pack_f64, hu, hτ]
    cases τ <;> simp [UnpackedFloat.add]
  rw [toBits_of_unpack_eq_zero_f64 _ _ hg]
  cases τ
  · right; decide
  · left; decide

/-! ### Converting the index -/

/-- `castNat_f64 k`, imported into FloatLib, is Lean's integer conversion of `k`. -/
theorem toModel_ofFloat_castNat_f64 (k : ℕ) :
    toModel (ofFloat (castNat_f64 k) : Binary64) =
      Model.ofModel FloatFormat.binary64
        (Float.Model.UnpackedFloat.ofInt FloatFormat.binary64.toModel (k : Int)) := by
  rw [toModel_ofFloat]
  rfl

/-- Converting any `k ≤ 2^64` (every `usize`) gives a finite value. -/
theorem isFinite_castNat_f64 (k : ℕ) (hk : k ≤ 2 ^ 64) : (castNat_f64 k).isFinite = true := by
  rw [← isFinite_ofFloat_iff]
  unfold isFinite
  rw [toModel_ofFloat_castNat_f64, ofModel_ofNat_eq_roundDyadic _ (by decide)]
  apply Model.isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite _ (by decide)
  rw [Model.Dyadic.toReal_ofScaledInt_zero]
  have hk' : (k : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hk
  have hm : (k : ℝ) ≤ maxFinite_f64 := by
    have h1 : (2 : ℝ) ^ 64 ≤ 2 ^ 1020 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h2 := maxFinite_f64_ge
    have h3 : (0 : ℝ) ≤ 2 ^ 1020 := by positivity
    generalize (2 : ℝ) ^ 1020 = B at h1 h2 h3
    linarith
  have : |((k : ℤ) : ℝ)| ≤ maxFinite_f64 := by
    simpa using hm
  exact this

/-- **How `i as f64` rounds:** for every `k ≤ 2^64` (every `usize`), the real value of
`castNat_f64 k` is `k` rounded to the nearest binary64 number, ties to even (FloatLib's
`roundAt`). -/
theorem real_castNat_f64_eq_roundAt (k : ℕ) (hk : k ≤ 2 ^ 64) :
    real_f64 (castNat_f64 k) = Model.roundAt FloatFormat.binary64 (k : ℝ) := by
  have hf := isFinite_ofFloat _ (isFinite_castNat_f64 k hk)
  unfold real_f64
  unfold isFinite at hf
  unfold toReal
  rw [toModel_ofFloat_castNat_f64] at hf ⊢
  rw [ofModel_ofNat_eq_roundDyadic _ (by decide)] at hf ⊢
  have h := Model.toReal_roundDyadic_eq_roundAt FloatFormat.binary64 (by decide) _ hf
  rw [Model.Dyadic.toReal_ofScaledInt_zero] at h
  exact h

/-- **`i as f64` is exact up to `2^53`:** for every `k ≤ 2^53`, the real value of
`castNat_f64 k` is exactly `k`. -/
theorem real_castNat_f64 (k : ℕ) (hk : k ≤ 2 ^ 53) : real_f64 (castNat_f64 k) = k := by
  rw [real_castNat_f64_eq_roundAt k (hk.trans (by norm_num))]
  have := Model.roundAt_intCast_of_abs_le FloatFormat.binary64 (n := (k : ℤ)) (by
    have hk' : (k : ℝ) ≤ 2 ^ 53 := by exact_mod_cast hk
    simpa [FloatFormat.binary64] using hk')
  simpa using this

/-- For `1 ≤ k ≤ 2^64`, `castNat_f64 k` is at least 1. -/
theorem one_le_real_castNat_f64 (k : ℕ) (h1 : 1 ≤ k) (hk : k ≤ 2 ^ 64) :
    1 ≤ real_f64 (castNat_f64 k) := by
  rw [real_castNat_f64_eq_roundAt k hk]
  have h := Model.roundAt_mono FloatFormat.binary64 (show (1 : ℝ) ≤ k by exact_mod_cast h1)
  rwa [Model.roundAt_one] at h

/-- **The step is finite** when `end - start` is (that is, when `start` and `end` are finite and
`end - start` does not overflow), for any block length `1 ≤ n < 2^64` (every nonempty
block). -/
theorem isFinite_rampStep_f64 (start «end» : Float) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64)
    (hD : («end» - start).isFinite = true) : (rampStep_f64 start «end» n).isFinite = true := by
  have hcf := isFinite_castNat_f64 n hn.le
  have hc1 := one_le_real_castNat_f64 n hn1 hn.le
  apply isFinite_div_f64 _ _ hD hcf (ne_of_gt (by linarith))
  rw [abs_div, abs_of_pos (show 0 < real_f64 (castNat_f64 n) by linarith)]
  exact (div_le_self (abs_nonneg _) hc1).trans (abs_real_le_maxFinite_f64 _ hD)

/-- **The first gain is exactly `start`** (as bits) when `end - start` is finite (that is,
`start` and `end` are finite and `end - start` does not overflow), `1 ≤ n < 2^64`, and `start`
is not `-0` (bits `0x8000000000000000`). -/
theorem rampGain_f64_zero (start «end» : Float) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64)
    (hD : («end» - start).isFinite = true) (hz : start.toBits ≠ 0x8000000000000000) :
    rampGain_f64 start «end» n 0 = start :=
  rampGain_f64_zero_of_step _ _ _ (isFinite_rampStep_f64 _ _ _ hn1 hn hD) hz

/-- Under the same conditions, but with `start` equal to `-0`, the first gain is `+0` (bits `0`)
or `-0`. -/
theorem rampGain_f64_zero_negZero (start «end» : Float) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : n < 2 ^ 64)
    (hD : («end» - start).isFinite = true) (hz : start.toBits = 0x8000000000000000) :
    (rampGain_f64 start «end» n 0).toBits = 0 ∨
      (rampGain_f64 start «end» n 0).toBits = 0x8000000000000000 :=
  rampGain_f64_zero_of_step_negZero _ _ _ (isFinite_rampStep_f64 _ _ _ hn1 hn hD) hz

/-! ### Distance from the exact straight line -/

/-- The no-overflow bookkeeping shared by the theorems below: under their conditions,
`end - start` and the step are finite, and each is within one rounding of the exact
operation on its operands. -/
theorem rampStep_f64_facts (start «end» : Float) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 53)
    (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f64 start| ≤ 2 ^ 1020) (hEb : |real_f64 «end»| ≤ 2 ^ 1020) :
    («end» - start).isFinite = true ∧ (rampStep_f64 start «end» n).isFinite = true ∧
      |real_f64 («end» - start) - (real_f64 «end» - real_f64 start)| ≤
        unitRoundoff_f64 * |real_f64 «end» - real_f64 start| + underflowErr_f64 ∧
      |real_f64 (rampStep_f64 start «end» n) - real_f64 («end» - start) / n| ≤
        unitRoundoff_f64 * |real_f64 («end» - start) / n| + underflowErr_f64 := by
  have hmax := maxFinite_f64_ge
  have hB1 : (1 : ℝ) ≤ 2 ^ 1020 := one_le_pow₀ (by norm_num)
  generalize (2 : ℝ) ^ 1020 = B at hmax hB1 hSb hEb
  have hDf : («end» - start).isFinite = true := by
    apply isFinite_sub_f64 _ _ hE hS
    have := abs_sub (real_f64 «end») (real_f64 start); linarith
  have hsf := isFinite_rampStep_f64 start «end» n hn1 (by omega) hDf
  have e2 := abs_real_div_sub_le_f64 _ _ hDf (isFinite_castNat_f64 n (by omega)) hsf
  rw [real_castNat_f64 n hn] at e2
  exact ⟨hDf, hsf, abs_real_sub_sub_le_f64 _ _ hE hS hDf, e2⟩

/-- **Each gain is close to the exact straight line.** When `start` and `end` are finite and at
most `2^1020` in size, `1 ≤ n ≤ 2^53` and `i < n`: the gain of sample `i` is finite, and its
real value is within `u·|S| + 5u·|E - S| + (2n + 4)·η` of `S + (E - S)·i/n`, the exact straight
line through `S` at `i = 0` and `E` at `i = n`. Here `S` and `E` are the real values of `start`
and `end`, `u = 2^-53` the unit roundoff and `η = 2^-1075` the underflow error. -/
theorem rampGain_f64_error (start «end» : Float) (n i : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 53)
    (hi : i < n) (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f64 start| ≤ 2 ^ 1020) (hEb : |real_f64 «end»| ≤ 2 ^ 1020) :
    (rampGain_f64 start «end» n i).isFinite = true ∧
      |real_f64 (rampGain_f64 start «end» n i) -
          (real_f64 start + (real_f64 «end» - real_f64 start) * i / n)| ≤
        unitRoundoff_f64 * |real_f64 start| +
          5 * unitRoundoff_f64 * |real_f64 «end» - real_f64 start| +
          (2 * n + 4) * underflowErr_f64 := by
  obtain ⟨hDf, hsf, e1, e2⟩ := rampStep_f64_facts start «end» n hn1 hn hS hE hSb hEb
  have hu0 : 0 ≤ unitRoundoff_f64 := by rw [unitRoundoff_f64_eq]; positivity
  have hu := unitRoundoff_f64_le
  have hη := underflowErr_f64_nonneg
  have hmax := maxFinite_f64_ge
  have hB1 : (1 : ℝ) ≤ 2 ^ 1020 := one_le_pow₀ (by norm_num)
  generalize (2 : ℝ) ^ 1020 = B at hmax hB1 hSb hEb
  have hni : i ≤ 2 ^ 53 := by omega
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hNη : (n : ℝ) * underflowErr_f64 ≤ 1 := mul_underflowErr_f64_le n (by exact_mod_cast hn)
  have hiN : (i : ℝ) ≤ n := by exact_mod_cast hi.le
  have hη1 : underflowErr_f64 ≤ 1 := by
    have := le_mul_of_one_le_left hη hN1
    linarith
  have hDb : |real_f64 «end» - real_f64 start| ≤ 2 * B := by
    have := abs_sub (real_f64 «end») (real_f64 start); linarith
  have hd := abs_rounded_le _ _ _ _ hu e1
  have hcif := isFinite_castNat_f64 i (hni.trans (by norm_num))
  have hcir := real_castNat_f64 i hni
  have hq := ramp_abs_si_le _ _ _ _ _ _ hu hη hN1 (Nat.cast_nonneg i) hiN e2
  -- The product.
  have hpf : (rampStep_f64 start «end» n * castNat_f64 i).isFinite = true :=
    isFinite_mul_f64 _ _ hsf hcif (by rw [hcir]; linarith)
  have e3 := abs_real_mul_sub_le_f64 _ _ hsf hcif hpf
  rw [hcir] at e3
  have hp := abs_rounded_le _ _ _ _ hu e3
  -- The sum.
  have hgf : (rampGain_f64 start «end» n i).isFinite = true := by
    apply isFinite_add_f64 _ _ hS hpf
    have := abs_add_le (real_f64 start) (real_f64 (rampStep_f64 start «end» n * castNat_f64 i))
    linarith
  have e4 := abs_real_add_sub_le_f64 _ _ hS hpf hgf
  exact ⟨hgf, ramp_error_real _ _ _ _ _ _ _ _ _ _ hu0 hu hη hN1 (Nat.cast_nonneg i) hiN
    e1 e2 e3 e4⟩

/-- **The step is close to `(E - S)/n`.** Under the conditions of `rampGain_f64_error`, the real
value of the step is within `3u·|E - S| + 3η` of `(E - S)/n`. -/
theorem rampStep_f64_error (start «end» : Float) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 53)
    (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f64 start| ≤ 2 ^ 1020) (hEb : |real_f64 «end»| ≤ 2 ^ 1020) :
    |real_f64 (rampStep_f64 start «end» n) - (real_f64 «end» - real_f64 start) / n| ≤
      3 * unitRoundoff_f64 * |real_f64 «end» - real_f64 start| + 3 * underflowErr_f64 := by
  obtain ⟨-, -, e1, e2⟩ := rampStep_f64_facts start «end» n hn1 hn hS hE hSb hEb
  have hu0 : 0 ≤ unitRoundoff_f64 := by rw [unitRoundoff_f64_eq]; positivity
  exact ramp_step_error_real _ _ _ _ _ _ hu0 unitRoundoff_f64_le underflowErr_f64_nonneg
    (by exact_mod_cast hn1) e1 e2

/-- **The last gain is close to `end - step`.** Under the conditions of `rampGain_f64_error`,
the real value of the last gain (`i = n - 1`) is within `u·|S| + 8u·|E - S| + (2n + 7)·η` of
`E - s`, where `s` is the real value of the step. -/
theorem rampGain_f64_last_error (start «end» : Float) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : n ≤ 2 ^ 53)
    (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f64 start| ≤ 2 ^ 1020) (hEb : |real_f64 «end»| ≤ 2 ^ 1020) :
    |real_f64 (rampGain_f64 start «end» n (n - 1)) -
        (real_f64 «end» - real_f64 (rampStep_f64 start «end» n))| ≤
      unitRoundoff_f64 * |real_f64 start| +
        8 * unitRoundoff_f64 * |real_f64 «end» - real_f64 start| +
        (2 * n + 7) * underflowErr_f64 := by
  have h1 := (rampGain_f64_error start «end» n (n - 1) hn1 hn (by omega) hS hE hSb hEb).2
  have h2 := rampStep_f64_error start «end» n hn1 hn hS hE hSb hEb
  have hN : (((n - 1 : ℕ) : ℝ)) = n - 1 := by rw [Nat.cast_sub hn1]; simp
  rw [hN] at h1
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  have := ramp_last_error_real _ _ _ _ _ _ _ hn0 h1 h2
  linarith

/-- **Steps inside a block are close to the step.** Under the conditions of
`rampGain_f64_error`, for `i + 1 < n`, the real gains of samples `i + 1` and `i` differ by `s`
(the real value of the step) to within `2u·|S| + 13u·|E - S| + (4n + 11)·η`. -/
theorem rampGain_f64_succ_sub (start «end» : Float) (n i : ℕ) (hn1 : 1 ≤ n)
    (hn : n ≤ 2 ^ 53)
    (hi : i + 1 < n) (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f64 start| ≤ 2 ^ 1020) (hEb : |real_f64 «end»| ≤ 2 ^ 1020) :
    |real_f64 (rampGain_f64 start «end» n (i + 1)) - real_f64 (rampGain_f64 start «end» n i) -
        real_f64 (rampStep_f64 start «end» n)| ≤
      2 * unitRoundoff_f64 * |real_f64 start| +
        13 * unitRoundoff_f64 * |real_f64 «end» - real_f64 start| +
        (4 * n + 11) * underflowErr_f64 := by
  have h1 := (rampGain_f64_error start «end» n (i + 1) hn1 hn hi hS hE hSb hEb).2
  have h0 := (rampGain_f64_error start «end» n i hn1 hn (by omega) hS hE hSb hEb).2
  have h2 := rampStep_f64_error start «end» n hn1 hn hS hE hSb hEb
  push_cast at h1
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  have := ramp_succ_sub_real _ _ _ _ _ _ _ _ _ _ hn0 h1 h0 h2
  linarith

/-- **From one block to the next.** If a block from `start` to `end` of `n` samples is followed
by a block from `end` to any `end₂` of any length `1 ≤ m < 2^64`, with `end₂ - end` finite
(`end₂` finite and no overflow) and `end` not `-0`: the next block's first gain is exactly `end`,
and it differs from the real value of this block's last gain by `s` (this block's step) to
within `u·|S| + 8u·|E - S| + (2n + 7)·η`, under the conditions of `rampGain_f64_error` on this
block. -/
theorem rampGain_f64_next_block (start «end» end₂ : Float) (n m : ℕ) (hn1 : 1 ≤ n)
    (hn : n ≤ 2 ^ 53) (hm1 : 1 ≤ m) (hm : m < 2 ^ 64)
    (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hD₂ : (end₂ - «end»).isFinite = true) (hz : «end».toBits ≠ 0x8000000000000000)
    (hSb : |real_f64 start| ≤ 2 ^ 1020) (hEb : |real_f64 «end»| ≤ 2 ^ 1020) :
    rampGain_f64 «end» end₂ m 0 = «end» ∧
      |real_f64 (rampGain_f64 «end» end₂ m 0) -
          real_f64 (rampGain_f64 start «end» n (n - 1)) -
          real_f64 (rampStep_f64 start «end» n)| ≤
        unitRoundoff_f64 * |real_f64 start| +
          8 * unitRoundoff_f64 * |real_f64 «end» - real_f64 start| +
          (2 * n + 7) * underflowErr_f64 := by
  have h0 := rampGain_f64_zero «end» end₂ m hm1 hm hD₂ hz
  refine ⟨h0, ?_⟩
  rw [h0]
  have h := rampGain_f64_last_error start «end» n hn1 hn hS hE hSb hEb
  have he : real_f64 «end» - real_f64 (rampGain_f64 start «end» n (n - 1)) -
        real_f64 (rampStep_f64 start «end» n) =
      -(real_f64 (rampGain_f64 start «end» n (n - 1)) -
        (real_f64 «end» - real_f64 (rampStep_f64 start «end» n))) := by ring
  rw [he, abs_neg]
  exact h

/-! ### Direction -/

/-- The real value of a finite gain, as nested roundings. -/
theorem real_rampGain_f64 (start «end» : Float) (n i : ℕ) (hn : n ≤ 2 ^ 64)
    (hi : i ≤ 2 ^ 64)
    (h : (rampGain_f64 start «end» n i).isFinite = true) :
    real_f64 (rampGain_f64 start «end» n i) =
      Model.roundAt FloatFormat.binary64 (real_f64 start +
        Model.roundAt FloatFormat.binary64 (real_f64 (rampStep_f64 start «end» n) *
          Model.roundAt FloatFormat.binary64 i)) ∧
      real_f64 (rampStep_f64 start «end» n) =
        Model.roundAt FloatFormat.binary64 (Model.roundAt FloatFormat.binary64
          (real_f64 «end» - real_f64 start) / Model.roundAt FloatFormat.binary64 n) := by
  obtain ⟨hS, hE, hD, hs⟩ := isFinite_of_rampGain_f64 start «end» n i h
  have hci := isFinite_castNat_f64 i hi
  have hcn := isFinite_castNat_f64 n hn
  have hp : (rampStep_f64 start «end» n * castNat_f64 i).isFinite = true := by
    cases hp : (rampStep_f64 start «end» n * castNat_f64 i).isFinite
    · rw [rampGain_f64_eq, isFinite_add_eq_false_f64 _ _ (Or.inr hp)] at h
      exact absurd h (by decide)
    · rfl
  constructor
  · rw [rampGain_f64_eq, real_add_f64 _ _ hS hp h, real_mul_f64 _ _ hs hci hp,
      real_castNat_f64_eq_roundAt i hi]
  · rw [rampStep_f64, real_div_f64 _ _ hD hcn hs, real_sub_f64 _ _ hE hS hD,
      real_castNat_f64_eq_roundAt n hn]

/-- **The gains never go the wrong way.** For samples `i ≤ j ≤ 2^64` of a block of length
`n ≤ 2^64` whose gains are finite: if `start ≤ end` (as real numbers) then gain `i` is at most
gain `j`, and if `end ≤ start` then gain `j` is at most gain `i`. -/
theorem rampGain_f64_mono (start «end» : Float) (n i j : ℕ) (hn : n ≤ 2 ^ 64)
    (hij : i ≤ j) (hj : j ≤ 2 ^ 64)
    (hi_fin : (rampGain_f64 start «end» n i).isFinite = true)
    (hj_fin : (rampGain_f64 start «end» n j).isFinite = true) :
    (real_f64 start ≤ real_f64 «end» →
        real_f64 (rampGain_f64 start «end» n i) ≤
          real_f64 (rampGain_f64 start «end» n j)) ∧
      (real_f64 «end» ≤ real_f64 start →
        real_f64 (rampGain_f64 start «end» n j) ≤
          real_f64 (rampGain_f64 start «end» n i)) := by
  obtain ⟨hgi, hs⟩ := real_rampGain_f64 start «end» n i hn (hij.trans hj) hi_fin
  obtain ⟨hgj, -⟩ := real_rampGain_f64 start «end» n j hn hj hj_fin
  rw [hgi, hgj]
  exact ramp_mono_roundAt FloatFormat.binary64 _ _ _ _ _ _ (by positivity)
    (by exact_mod_cast hij) hs

end conjure_dsp_lib.gain
