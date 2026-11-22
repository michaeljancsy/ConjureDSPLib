module

public import ConjureDSPLib.Code.Funs
public import ConjureDSPLib.FloatFacts
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral

/-!
# Gain

About `src/gain.rs`, as Aeneas translated it (into `ConjureDSPLib/Code/Funs.lean`):

1. `apply_f64` and `apply_f32` are exactly Lean's `Float.mul` / `Float32.mul`, and never fail.
2. `ramp_f64_spec` / `ramp_f32_spec`: `ramp_f64` and `ramp_f32` never fail, and multiply each
   sample `i` of a block of `n` samples by exactly `start + ((end - start) / n) * i`, computed in
   binary64 / binary32 in that order, with `n` and `i` converted by `castNat_f64` /
   `castNat_f32` (Lean's own `Float.Model.ofNat` / `Float32.Model.ofNat`;
   `usize_toFloat_eq_castNat_f64` and `usize_toFloat32_eq_castNat_f32` show these are the
   translated `as`). See `rampGain_f64`, `rampGain_f32`. These are statements about float
   operations, not about real numbers.
3. `rampGain_f64_not_finite`: if `start` or `end` is infinite or NaN, or `end - start`
   overflows, every gain is infinite or NaN, the first included.
4. `rampGain_f64_zero`: when `end - start` is finite and `start` is not `-0`, the first gain is
   exactly `start`, bit for bit (`rampGain_f64_zero_negZero`: a `start` of `-0` may give `+0`).
5. `real_castNat_f64`: `castNat_f64 k` is exactly `k` for `k ≤ 2^53`;
   `real_castNat_f64_eq_roundAt`: for every `k ≤ 2^64` it is `k` rounded to nearest, ties to
   even.
6. `rampGain_f64_error`: with `start` and `end` finite and at most `2^1020` in size and
   `n ≤ 2^53`, each gain is within `u·|S| + 5u·|E - S| + (2n + 4)·η` of the exact straight
   line `S + (E - S)·i/n`; `rampGain_f64_last_error`, `rampGain_f64_succ_sub` and
   `rampGain_f64_next_block` follow from it for the last gain, the steps inside a block and the
   step into the next block.
7. `rampGain_f64_mono`: finite gains never go the wrong way: along the block they do not
   decrease when `start ≤ end`, and do not increase when `end ≤ start`.

Each has an `_f32` twin (`n ≤ 2^24`, sizes at most `2^124`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.gain

/-- The Rust `apply_f64` is `gain * x` on Lean's binary64 `Float`, and cannot fail. -/
theorem apply_f64_eq (gain x : Float) : apply_f64 gain x = ok (gain * x) := rfl

/-- The Rust `apply_f32` is `gain * x` on Lean's binary32 `Float32`, and cannot fail. -/
theorem apply_f32_eq (gain x : Float32) : apply_f32 gain x = ok (gain * x) := rfl

/-! ## The ramp in f64 -/

/-- A natural number converted to a binary64 value by Lean's own conversion `Float.Model.ofNat`
(whose definition in Lean core's float model rounds to nearest, ties to even; not proved here).
`usize_toFloat_eq_castNat_f64` shows it is the translated Rust `i as f64`. -/
def castNat_f64 (n : ℕ) : Float := Float.ofModel (Float.Model.ofNat n)

/-- The translation of Rust's `i as f64` for a `usize` is `castNat_f64` of its value. -/
theorem usize_toFloat_eq_castNat_f64 (i : Std.Usize) : UScalar.toFloat i = castNat_f64 i.val := by
  simp only [UScalar.toFloat, USize.toFloat, castNat_f64, Float.Model.ofUSize,
    Float.Model.ofNat, Float.Model.UnpackedFloat.ofUSize, USize.toNat_ofBitVec]
  rfl

/-- The gain of sample `i` in a block of `n` samples: `start + ((end - start) / n) * i` in
binary64, in the Rust code's order, with `n` and `i` converted by `castNat_f64`. -/
def rampGain_f64 (start «end» : Float) (n i : ℕ) : Float :=
  start + ((«end» - start) / castNat_f64 n) * castNat_f64 i

/-- The ramp on a list of samples: sample `i` multiplied by `rampGain_f64` for the list's length.
(An empty list gives an empty list.) -/
def rampList_f64 (start «end» : Float) (xs : List Float) : List Float :=
  xs.mapIdx (fun i x => x * rampGain_f64 start «end» xs.length i)

/-- When `i ≤ buf.length`, the loop started at position `i` never fails, leaves the first `i`
samples as they are, and multiplies every later sample `k` by `start + step * castNat_f64 k`. -/
theorem ramp_f64_loop_spec (start step : Float) (buf : Slice Float) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    ramp_f64_loop start buf step i ⦃ fun r =>
      r.val = buf.val.mapIdx (fun k x =>
        if k < i.val then x else x * (start + step * castNat_f64 k)) ⦄ := by
  unfold ramp_f64_loop
  -- Invariant on the loop state `(b, j)`: the buffer keeps its length, the samples from `i` up
  -- to `j` are done, and the others are as they were at the start of the loop.
  apply loop.spec_decr_nat (fun x => x.1.length - x.2.val)
    (fun x => x.1.length = buf.length ∧ i.val ≤ x.2.val ∧ x.2.val ≤ x.1.length ∧
      x.1.val = buf.val.mapIdx (fun k x' =>
        if k < i.val ∨ x.2.val ≤ k then x' else x' * (start + step * castNat_f64 k)))
  · rintro ⟨b, j⟩ ⟨hlen, hij, hj, hb⟩
    simp only at hlen hij hj hb
    simp only [ramp_f64_loop.body, lift, usize_toFloat_eq_castNat_f64]
    step*
    · -- Still looping: sample `j` is now done.
      subst s_post fl1_post
      have hjl : j.val < b.length := by scalar_tac
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [i2_post]; omega
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]
        apply List.ext_getElem
        · simp [hb]
        · intro k hk1 hk2
          by_cases hkj : j.val = k
          · subst hkj
            have h1 : ¬ (j.val < i.val ∨ j.val + 1 ≤ j.val) := by omega
            have h2 : j.val < i.val ∨ j.val ≤ j.val := by omega
            simp only [List.getElem_set_self, List.getElem_mapIdx, hb, h1, h2, ite_true,
              ite_false]
            rfl
          · have h1 : (k < i.val ∨ j.val ≤ k) ↔ (k < i.val ∨ j.val + 1 ≤ k) := by omega
            rw [List.getElem_set_ne hkj]
            simp only [hb, List.getElem_mapIdx, h1]
      · simp only [Slice.set_length, i2_post]; omega
    · -- Finished: every sample from `i` on is done.
      have hjl : j.val = b.length := by scalar_tac
      rw [hb]
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [List.getElem_mapIdx]
        have : ¬ (j.val ≤ k) := by simp [Slice.length] at hk1 hk2 hjl hlen; omega
        simp [this]
  · refine ⟨rfl, le_refl _, hi, ?_⟩
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      simp only [List.getElem_mapIdx]
      grind

/-- **The Rust `ramp_f64` never fails, and its output is exactly `rampList_f64`:** each sample
`i` of the block multiplied by `rampGain_f64 start end n i`, where `n` is the block's length,
in binary64. An empty block is returned unchanged. -/
theorem ramp_f64_spec (start «end» : Float) (buf : Slice Float) :
    ramp_f64 start «end» buf ⦃ fun r => r.val = rampList_f64 start «end» buf.val ⦄ := by
  unfold ramp_f64
  dsimp only
  split
  · rename_i h
    have h0 : buf.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      have := congrArg UScalar.val h
      simpa using this
    simp [h0, rampList_f64]
  · simp only [lift, usize_toFloat_eq_castNat_f64, bind_ok]
    apply WP.spec_mono (ramp_f64_loop_spec start _ buf 0#usize (by simp))
    intro r hr
    rw [hr]
    simp [rampList_f64, rampGain_f64]
    rfl

/-! ## The ramp in f32 -/

/-- A natural number converted to a binary32 value by Lean's own conversion `Float32.Model.ofNat`
(whose definition in Lean core's float model rounds to nearest, ties to even; not proved here).
`usize_toFloat32_eq_castNat_f32` shows it is the translated Rust `i as f32`. -/
def castNat_f32 (n : ℕ) : Float32 := Float32.ofModel (Float32.Model.ofNat n)

/-- The translation of Rust's `i as f32` for a `usize` is `castNat_f32` of its value. -/
theorem usize_toFloat32_eq_castNat_f32 (i : Std.Usize) :
    UScalar.toFloat32 i = castNat_f32 i.val := by
  simp only [UScalar.toFloat32, USize.toFloat32, castNat_f32, Float32.Model.ofUSize,
    Float32.Model.ofNat, Float.Model.UnpackedFloat.ofUSize, USize.toNat_ofBitVec]
  rfl

/-- The gain of sample `i` in a block of `n` samples: `start + ((end - start) / n) * i` in
binary32, in the Rust code's order, with `n` and `i` converted by `castNat_f32`. -/
def rampGain_f32 (start «end» : Float32) (n i : ℕ) : Float32 :=
  start + ((«end» - start) / castNat_f32 n) * castNat_f32 i

/-- The ramp on a list of samples: sample `i` multiplied by `rampGain_f32` for the list's length.
(An empty list gives an empty list.) -/
def rampList_f32 (start «end» : Float32) (xs : List Float32) : List Float32 :=
  xs.mapIdx (fun i x => x * rampGain_f32 start «end» xs.length i)

/-- When `i ≤ buf.length`, the loop started at position `i` never fails, leaves the first `i`
samples as they are, and multiplies every later sample `k` by `start + step * castNat_f32 k`. -/
theorem ramp_f32_loop_spec (start step : Float32) (buf : Slice Float32) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    ramp_f32_loop start buf step i ⦃ fun r =>
      r.val = buf.val.mapIdx (fun k x =>
        if k < i.val then x else x * (start + step * castNat_f32 k)) ⦄ := by
  unfold ramp_f32_loop
  -- Invariant on the loop state `(b, j)`: the buffer keeps its length, the samples from `i` up
  -- to `j` are done, and the others are as they were at the start of the loop.
  apply loop.spec_decr_nat (fun x => x.1.length - x.2.val)
    (fun x => x.1.length = buf.length ∧ i.val ≤ x.2.val ∧ x.2.val ≤ x.1.length ∧
      x.1.val = buf.val.mapIdx (fun k x' =>
        if k < i.val ∨ x.2.val ≤ k then x' else x' * (start + step * castNat_f32 k)))
  · rintro ⟨b, j⟩ ⟨hlen, hij, hj, hb⟩
    simp only at hlen hij hj hb
    simp only [ramp_f32_loop.body, lift, usize_toFloat32_eq_castNat_f32]
    step*
    · -- Still looping: sample `j` is now done.
      subst s_post fl1_post
      have hjl : j.val < b.length := by scalar_tac
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [i2_post]; omega
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]
        apply List.ext_getElem
        · simp [hb]
        · intro k hk1 hk2
          by_cases hkj : j.val = k
          · subst hkj
            have h1 : ¬ (j.val < i.val ∨ j.val + 1 ≤ j.val) := by omega
            have h2 : j.val < i.val ∨ j.val ≤ j.val := by omega
            simp only [List.getElem_set_self, List.getElem_mapIdx, hb, h1, h2, ite_true,
              ite_false]
            rfl
          · have h1 : (k < i.val ∨ j.val ≤ k) ↔ (k < i.val ∨ j.val + 1 ≤ k) := by omega
            rw [List.getElem_set_ne hkj]
            simp only [hb, List.getElem_mapIdx, h1]
      · simp only [Slice.set_length, i2_post]; omega
    · -- Finished: every sample from `i` on is done.
      have hjl : j.val = b.length := by scalar_tac
      rw [hb]
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [List.getElem_mapIdx]
        have : ¬ (j.val ≤ k) := by simp [Slice.length] at hk1 hk2 hjl hlen; omega
        simp [this]
  · refine ⟨rfl, le_refl _, hi, ?_⟩
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      simp only [List.getElem_mapIdx]
      grind

/-- **The Rust `ramp_f32` never fails, and its output is exactly `rampList_f32`:** each sample
`i` of the block multiplied by `rampGain_f32 start end n i`, where `n` is the block's length,
in binary32. An empty block is returned unchanged. -/
theorem ramp_f32_spec (start «end» : Float32) (buf : Slice Float32) :
    ramp_f32 start «end» buf ⦃ fun r => r.val = rampList_f32 start «end» buf.val ⦄ := by
  unfold ramp_f32
  dsimp only
  split
  · rename_i h
    have h0 : buf.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      have := congrArg UScalar.val h
      simpa using this
    simp [h0, rampList_f32]
  · simp only [lift, usize_toFloat32_eq_castNat_f32, bind_ok]
    apply WP.spec_mono (ramp_f32_loop_spec start _ buf 0#usize (by simp))
    intro r hr
    rw [hr]
    simp [rampList_f32, rampGain_f32]
    rfl

section RampValues

open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange
open Float.Model (UnpackedFloat Format)

open FloatLib.Numerics in
/-- Lean's conversion of a natural number is FloatLib's nearest-even rounding of it (FloatLib's
`Model.ofModel_ofInt_eq_roundDyadic`, restated for naturals). -/
theorem ofModel_ofNat_eq_roundDyadic (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (n : ℕ) :
    Model.ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel (n : Int)) =
      Model.roundDyadic fmt (Dyadic.ofScaledInt n 0) := by
  unfold Float.Model.UnpackedFloat.ofInt Float.Model.UnpackedFloat.normalize
  rw [Model.roundDyadic, ite_eq_left hfmt]
  cases n with
  | zero => simp [Dyadic.ofScaledInt, Model.ieeeRoundDyadic, Model.modelSign]
  | succ n =>
      have hp : (0 : Int) < ((n + 1 : ℕ) : Int) := by simp
      have hc := Int.compare_eq_gt.mpr hp
      rw [hc]
      change Model.ofModel fmt (Float.Model.UnpackedFloat.round fmt.toModel .positive
          (n + 1) 0) =
        Model.ofModel fmt (Float.Model.UnpackedFloat.round fmt.toModel
          (Model.modelSign (decide (((n + 1 : ℕ) : Int) < 0))) (n + 1) 0)
      rw [decide_eq_false (not_lt.mpr hp.le)]
      rfl

/-! ## Real numbers: the error of one gain (both precisions) -/

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



/-- Size of the rounded difference. -/
theorem ramp_abs_d_le (u η D d : ℝ) (hu : u ≤ 1 / 16)
    (e1 : |d - D| ≤ u * |D| + η) : |d| ≤ 17 / 16 * |D| + η := by
  have h := abs_sub_abs_le_abs_sub d D
  have : u * |D| ≤ 1 / 16 * |D| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  linarith

/-- Size of the rounded quotient times `i`. -/
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

/-- Size of the rounded product. -/
theorem ramp_abs_p_le (u η q p : ℝ) (hu : u ≤ 1 / 16)
    (e3 : |p - q| ≤ u * |q| + η) : |p| ≤ 17 / 16 * |q| + η := by
  have h := abs_sub_abs_le_abs_sub p q
  have : u * |q| ≤ 1 / 16 * |q| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
  linarith

/-- **The error of one gain, in real numbers.** If `d`, `s`, `p` and `g` are the rounded
difference, quotient, product and sum, each within `u·|exact| + η` of the exact operation on the
rounded operands, then `g` is within `u·|S| + 5u·|D| + (2N + 4)·η` of `S + D·i/N`. -/
theorem ramp_error_real (u η S D d s p g N i : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 16)
    (hη : 0 ≤ η)    (hN : 1 ≤ N) (hi0 : 0 ≤ i) (hiN : i ≤ N)
    (e1 : |d - D| ≤ u * |D| + η)
    (e2 : |s - d / N| ≤ u * |d / N| + η)
    (e3 : |p - s * i| ≤ u * |s * i| + η)
    (e4 : |g - (S + p)| ≤ u * |S + p| + η) :
    |g - (S + D * i / N)| ≤ u * |S| + 5 * u * |D| + (2 * N + 4) * η := by
  have hN0 : 0 < N := by linarith
  have hd := ramp_abs_d_le u η D d hu e1
  have hq := ramp_abs_si_le u η d s N i hu hη hN hi0 hiN e2
  have hp := ramp_abs_p_le u η (s * i) p hu e3
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
  nlinarith

theorem ramp_step_error_real (u η D d s N : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 16)
    (hη : 0 ≤ η)    (hN : 1 ≤ N)
    (e1 : |d - D| ≤ u * |D| + η)
    (e2 : |s - d / N| ≤ u * |d / N| + η) :
    |s - D / N| ≤ 3 * u * |D| + 3 * η := by
  have hN0 : 0 < N := by linarith
  have hd := ramp_abs_d_le u η D d hu e1
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

/-! ## The ramp's values in binary64

Facts about `rampGain_f64` on Lean's `Float`: which samples are exact, what happens when an end
is not finite, how `i as f64` rounds, and how far each gain is from the exact straight line. -/

/-- The step of the ramp: `(end - start) / n` in binary64, with `n` converted by `castNat_f64`. -/
def rampStep_f64 (start «end» : Float) (n : ℕ) : Float := («end» - start) / castNat_f64 n

/-- `rampGain_f64` is `start + rampStep_f64 start end n * castNat_f64 i`. -/
theorem rampGain_f64_eq (start «end» : Float) (n i : ℕ) :
    rampGain_f64 start «end» n i = start + rampStep_f64 start «end» n * castNat_f64 i := rfl

/-! ### Infinity and NaN -/

/-- Unpacking a packed value of Lean's binary64 model is Lean core's `UnpackedFloat.unpack` of
`UnpackedFloat.pack`. -/
theorem unpack_pack_f64 (u : UnpackedFloat) :
    (Float.Model.pack u).unpack =
      UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 u) := by
  simp [Float.Model.pack, Float.Model.unpack]

/-- A sum with an operand that is not finite (infinite or NaN) is not finite. -/
theorem isFinite_add_eq_false_f64 (x y : Float) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x + y).isFinite = false := by
  show (Float.Model.pack (UnpackedFloat.add Format.binary64 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float.isFinite, Float.Model.isFinite] at h
  unfold Float.Model.isFinite
  rw [unpack_pack_f64]
  rcases h with h | h
  all_goals
    cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.add, UnpackedFloat.isFinite]
  all_goals split_ifs <;> simp

/-- A difference with an operand that is not finite is not finite. -/
theorem isFinite_sub_eq_false_f64 (x y : Float) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x - y).isFinite = false := by
  show (Float.Model.pack (UnpackedFloat.sub Format.binary64 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float.isFinite, Float.Model.isFinite] at h
  unfold Float.Model.isFinite
  rw [unpack_pack_f64]
  rcases h with h | h
  all_goals
    cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.sub, UnpackedFloat.isFinite]
  all_goals split_ifs <;> simp

/-- A product with an operand that is not finite is not finite (infinity times zero is NaN). -/
theorem isFinite_mul_eq_false_f64 (x y : Float) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x * y).isFinite = false := by
  show (Float.Model.pack (UnpackedFloat.mul Format.binary64 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float.isFinite, Float.Model.isFinite] at h
  unfold Float.Model.isFinite
  rw [unpack_pack_f64]
  rcases h with h | h <;>
  · cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.mul, UnpackedFloat.isFinite]

/-- A quotient whose dividend is not finite is not finite, whatever the divisor. -/
theorem isFinite_div_eq_false_f64 (x y : Float) (h : x.isFinite = false) :
    (x / y).isFinite = false := by
  show (Float.Model.pack (UnpackedFloat.div Format.binary64 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float.isFinite, Float.Model.isFinite] at h
  unfold Float.Model.isFinite
  rw [unpack_pack_f64]
  cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
    simp_all [UnpackedFloat.div, UnpackedFloat.isFinite]

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

/-- A Lean `Float` is the packed form of its own unpacked form. -/
theorem ofModel_pack_eq_of_unpack_f64 (x : Float) (u : UnpackedFloat)
    (h : u = x.toModel.unpack) : Float.ofModel (Float.Model.pack u) = x := by
  rcases x with ⟨⟨b, hb⟩⟩
  subst h
  simp only [Float.Model.pack, Float.Model.unpack, Float.ofModel.injEq,
    Float.Model.mk.injEq]
  rw [Model.pack_unpack_of_valid _ _ hb]

/-- A `Float` that unpacks to a zero has the bits of that packed zero. -/
theorem toBits_of_unpack_eq_zero_f64 (x : Float) (s : UnpackedFloat.Sign)
    (h : x.toModel.unpack = .zero s) :
    x.toBits = UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (.zero s)) := by
  rcases x with ⟨⟨b, hb⟩⟩
  simp only [Float.Model.unpack] at h
  simp only [Float.toBits]
  rw [← h, Model.pack_unpack_of_valid _ _ hb]

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

/-- Adding a zero to `x` gives exactly `x`, unless `x` is `-0` (bits `0x8000000000000000`). -/
theorem add_zero_of_ne_negZero_f64 (x z : Float) (τ : UnpackedFloat.Sign)
    (hz : z.toModel.unpack = .zero τ) (hx : x.toBits ≠ 0x8000000000000000) : x + z = x := by
  show Float.ofModel (Float.Model.pack (UnpackedFloat.add Format.binary64 x.toModel.unpack
    z.toModel.unpack)) = x
  apply ofModel_pack_eq_of_unpack_f64
  rw [hz]
  cases h : x.toModel.unpack with
  | zero σ =>
    cases σ with
    | negative => exact absurd ((toBits_of_unpack_eq_zero_f64 x _ h).trans (by decide)) hx
    | positive => cases τ <;> rfl
  | _ => rfl

/-- When the step is finite, the first gain is exactly `start` (as bits, so also its sign),
unless `start` is `-0` (bits `0x8000000000000000`). `start` itself may be anything else, even
infinite or NaN. -/
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

/-! ### Numbers -/

/-- `8·2^1020` is at most the largest finite binary64 value. -/
theorem maxFinite_f64_ge : (8 : ℝ) * 2 ^ 1020 ≤ maxFinite_f64 := by
  rw [maxFinite_f64_eq]
  have h : (8 : ℝ) * 2 ^ 1020 = 2 ^ 52 * 2 ^ 971 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
  rw [h]
  gcongr
  norm_num

theorem unitRoundoff_f64_le : unitRoundoff_f64 ≤ 1 / 16 := by
  rw [unitRoundoff_f64_eq, zpow_neg]; norm_num

theorem underflowErr_f64_nonneg : 0 ≤ underflowErr_f64 := by
  rw [underflowErr_f64_eq]; positivity

theorem mul_underflowErr_f64_le (N : ℝ) (hN : N ≤ 2 ^ 53) : N * underflowErr_f64 ≤ 1 := by
  have h1 : (2 : ℝ) ^ 53 * 2 ^ (-1075 : ℤ) ≤ 1 := by
    rw [zpow_neg, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 53 ≤ 1075)
  calc N * underflowErr_f64 ≤ 2 ^ 53 * 2 ^ (-1075 : ℤ) := by
        rw [underflowErr_f64_eq]
        exact mul_le_mul_of_nonneg_right hN (by positivity)
    _ ≤ 1 := h1

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
  have hη1 : underflowErr_f64 ≤ 1 := by nlinarith
  have hDb : |real_f64 «end» - real_f64 start| ≤ 2 * B := by
    have := abs_sub (real_f64 «end») (real_f64 start); linarith
  have hd := ramp_abs_d_le _ _ _ _ hu e1
  have hcif := isFinite_castNat_f64 i (hni.trans (by norm_num))
  have hcir := real_castNat_f64 i hni
  have hq := ramp_abs_si_le _ _ _ _ _ _ hu hη hN1 (Nat.cast_nonneg i) hiN e2
  -- The product.
  have hpf : (rampStep_f64 start «end» n * castNat_f64 i).isFinite = true :=
    isFinite_mul_f64 _ _ hsf hcif (by rw [hcir]; linarith)
  have e3 := abs_real_mul_sub_le_f64 _ _ hsf hcif hpf
  rw [hcir] at e3
  have hp := ramp_abs_p_le _ _ _ _ hu e3
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
  have he : real_f64 (rampGain_f64 start «end» n (n - 1)) -
        (real_f64 «end» - real_f64 (rampStep_f64 start «end» n)) =
      (real_f64 (rampGain_f64 start «end» n (n - 1)) -
          (real_f64 start + (real_f64 «end» - real_f64 start) * (n - 1) / n)) +
        (real_f64 (rampStep_f64 start «end» n) - (real_f64 «end» - real_f64 start) / n) := by
    field_simp; ring
  rw [he]
  have := abs_add_le (real_f64 (rampGain_f64 start «end» n (n - 1)) -
      (real_f64 start + (real_f64 «end» - real_f64 start) * (n - 1) / n))
    (real_f64 (rampStep_f64 start «end» n) - (real_f64 «end» - real_f64 start) / n)
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
  set g1 := real_f64 (rampGain_f64 start «end» n (i + 1))
  set g0 := real_f64 (rampGain_f64 start «end» n i)
  set s := real_f64 (rampStep_f64 start «end» n)
  set S := real_f64 start
  set E := real_f64 «end»
  have he : g1 - g0 - s = (g1 - (S + (E - S) * (i + 1) / n)) - (g0 - (S + (E - S) * i / n)) -
      (s - (E - S) / n) := by field_simp; ring
  rw [he]
  have ha := abs_sub (g1 - (S + (E - S) * (i + 1) / n) - (g0 - (S + (E - S) * i / n)))
    (s - (E - S) / n)
  have hb := abs_sub (g1 - (S + (E - S) * (i + 1) / n)) (g0 - (S + (E - S) * i / n))
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

/-- The real value of a finite sum, product or quotient of finite binary64 numbers is the exact
result rounded to nearest. -/
theorem real_add_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x + y).isFinite = true) :
    real_f64 (x + y) = Model.roundAt FloatFormat.binary64 (real_f64 x + real_f64 y) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_add_of_isFinite x y hx hy] at h ⊢
  exact toReal_add_eq_roundAt h

theorem real_sub_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x - y).isFinite = true) :
    real_f64 (x - y) = Model.roundAt FloatFormat.binary64 (real_f64 x - real_f64 y) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_sub_of_isFinite x y hx hy] at h ⊢
  exact toReal_sub_eq_roundAt h

theorem real_mul_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x * y).isFinite = true) :
    real_f64 (x * y) = Model.roundAt FloatFormat.binary64 (real_f64 x * real_f64 y) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_mul_of_isFinite x y hx hy] at h ⊢
  exact toReal_mul_eq_roundAt h

theorem real_div_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x / y).isFinite = true) :
    real_f64 (x / y) = Model.roundAt FloatFormat.binary64 (real_f64 x / real_f64 y) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_div_of_isFinite x y hx hy] at h ⊢
  exact toReal_div_eq_roundAt (isFinite_ofFloat y hy) h

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
  have hn0 : 0 ≤ Model.roundAt FloatFormat.binary64 (n : ℝ) :=
    Model.roundAt_nonneg FloatFormat.binary64 (by positivity)
  have hij' : Model.roundAt FloatFormat.binary64 (i : ℝ) ≤
      Model.roundAt FloatFormat.binary64 (j : ℝ) :=
    Model.roundAt_mono FloatFormat.binary64 (by exact_mod_cast hij)
  rw [hgi, hgj]
  constructor
  · intro hSE
    have hs0 : 0 ≤ real_f64 (rampStep_f64 start «end» n) := by
      rw [hs]
      exact Model.roundAt_nonneg FloatFormat.binary64
        (div_nonneg (Model.roundAt_nonneg FloatFormat.binary64 (by linarith)) hn0)
    have h1 := Model.roundAt_mono FloatFormat.binary64 (mul_le_mul_of_nonneg_left hij' hs0)
    apply Model.roundAt_mono FloatFormat.binary64
    linarith
  · intro hES
    have hs0 : real_f64 (rampStep_f64 start «end» n) ≤ 0 := by
      rw [hs]
      exact Model.roundAt_nonpos FloatFormat.binary64 (div_nonpos_of_nonpos_of_nonneg
        (Model.roundAt_nonpos FloatFormat.binary64 (by linarith)) hn0)
    have h1 := Model.roundAt_mono FloatFormat.binary64 (mul_le_mul_of_nonpos_left hij' hs0)
    apply Model.roundAt_mono FloatFormat.binary64
    linarith

/-! ## The ramp's values in binary32

Facts about `rampGain_f32` on Lean's `Float32`: which samples are exact, what happens when an end
is not finite, how `i as f32` rounds, and how far each gain is from the exact straight line. -/

/-- The step of the ramp: `(end - start) / n` in binary32, with `n` converted by `castNat_f32`. -/
def rampStep_f32 (start «end» : Float32) (n : ℕ) : Float32 := («end» - start) / castNat_f32 n

/-- `rampGain_f32` is `start + rampStep_f32 start end n * castNat_f32 i`. -/
theorem rampGain_f32_eq (start «end» : Float32) (n i : ℕ) :
    rampGain_f32 start «end» n i = start + rampStep_f32 start «end» n * castNat_f32 i := rfl

/-! ### Infinity and NaN -/

/-- Unpacking a packed value of Lean's binary32 model is Lean core's `UnpackedFloat.unpack` of
`UnpackedFloat.pack`. -/
theorem unpack_pack_f32 (u : UnpackedFloat) :
    (Float32.Model.pack u).unpack =
      UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32 u) := by
  simp [Float32.Model.pack, Float32.Model.unpack]

/-- A sum with an operand that is not finite (infinite or NaN) is not finite. -/
theorem isFinite_add_eq_false_f32 (x y : Float32) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x + y).isFinite = false := by
  show (Float32.Model.pack (UnpackedFloat.add Format.binary32 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float32.isFinite, Float32.Model.isFinite] at h
  unfold Float32.Model.isFinite
  rw [unpack_pack_f32]
  rcases h with h | h
  all_goals
    cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.add, UnpackedFloat.isFinite]
  all_goals split_ifs <;> simp

/-- A difference with an operand that is not finite is not finite. -/
theorem isFinite_sub_eq_false_f32 (x y : Float32) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x - y).isFinite = false := by
  show (Float32.Model.pack (UnpackedFloat.sub Format.binary32 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float32.isFinite, Float32.Model.isFinite] at h
  unfold Float32.Model.isFinite
  rw [unpack_pack_f32]
  rcases h with h | h
  all_goals
    cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.sub, UnpackedFloat.isFinite]
  all_goals split_ifs <;> simp

/-- A product with an operand that is not finite is not finite (infinity times zero is NaN). -/
theorem isFinite_mul_eq_false_f32 (x y : Float32) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x * y).isFinite = false := by
  show (Float32.Model.pack (UnpackedFloat.mul Format.binary32 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float32.isFinite, Float32.Model.isFinite] at h
  unfold Float32.Model.isFinite
  rw [unpack_pack_f32]
  rcases h with h | h <;>
  · cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.mul, UnpackedFloat.isFinite]

/-- A quotient whose dividend is not finite is not finite, whatever the divisor. -/
theorem isFinite_div_eq_false_f32 (x y : Float32) (h : x.isFinite = false) :
    (x / y).isFinite = false := by
  show (Float32.Model.pack (UnpackedFloat.div Format.binary32 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float32.isFinite, Float32.Model.isFinite] at h
  unfold Float32.Model.isFinite
  rw [unpack_pack_f32]
  cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
    simp_all [UnpackedFloat.div, UnpackedFloat.isFinite]

/-- **If an end is not finite, or `end - start` is not finite (it overflowed), every gain is
infinite or NaN**, for every block length `n` and every sample `i`, the first (`i = 0`)
included. -/
theorem rampGain_f32_not_finite (start «end» : Float32) (n i : ℕ)
    (h : start.isFinite = false ∨ «end».isFinite = false ∨
      («end» - start).isFinite = false) :
    (rampGain_f32 start «end» n i).isFinite = false := by
  have hd : («end» - start).isFinite = false := by
    rcases h with h | h | h
    · exact isFinite_sub_eq_false_f32 _ _ (Or.inr h)
    · exact isFinite_sub_eq_false_f32 _ _ (Or.inl h)
    · exact h
  have hs := isFinite_div_eq_false_f32 _ (castNat_f32 n) hd
  have hp := isFinite_mul_eq_false_f32 _ (castNat_f32 i) (Or.inl hs)
  exact isFinite_add_eq_false_f32 _ _ (Or.inr hp)

/-- When a gain is finite, so are `start`, `end`, `end - start` and the step: the
contrapositive of `rampGain_f32_not_finite`. -/
theorem isFinite_of_rampGain_f32 (start «end» : Float32) (n i : ℕ)
    (h : (rampGain_f32 start «end» n i).isFinite = true) :
    start.isFinite = true ∧ «end».isFinite = true ∧ («end» - start).isFinite = true ∧
      (rampStep_f32 start «end» n).isFinite = true := by
  have key : ∀ b : Bool, b ≠ false → b = true := by decide
  refine ⟨key _ fun hS => ?_, key _ fun hE => ?_, key _ fun hD => ?_, key _ fun hs => ?_⟩
  · rw [rampGain_f32_not_finite _ _ _ _ (Or.inl hS)] at h; exact absurd h (by decide)
  · rw [rampGain_f32_not_finite _ _ _ _ (Or.inr (Or.inl hE))] at h; exact absurd h (by decide)
  · rw [rampGain_f32_not_finite _ _ _ _ (Or.inr (Or.inr hD))] at h; exact absurd h (by decide)
  · rw [rampGain_f32_eq, isFinite_add_eq_false_f32 _ _
      (Or.inr (isFinite_mul_eq_false_f32 _ _ (Or.inl hs)))] at h
    exact absurd h (by decide)

/-! ### The first gain -/

/-- A Lean `Float32` is the packed form of its own unpacked form. -/
theorem ofModel_pack_eq_of_unpack_f32 (x : Float32) (u : UnpackedFloat)
    (h : u = x.toModel.unpack) : Float32.ofModel (Float32.Model.pack u) = x := by
  rcases x with ⟨⟨b, hb⟩⟩
  subst h
  simp only [Float32.Model.pack, Float32.Model.unpack, Float32.ofModel.injEq,
    Float32.Model.mk.injEq]
  rw [Model.pack_unpack_of_valid _ _ hb]

/-- A `Float32` that unpacks to a zero has the bits of that packed zero. -/
theorem toBits_of_unpack_eq_zero_f32 (x : Float32) (s : UnpackedFloat.Sign)
    (h : x.toModel.unpack = .zero s) :
    x.toBits = UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (.zero s)) := by
  rcases x with ⟨⟨b, hb⟩⟩
  simp only [Float32.Model.unpack] at h
  simp only [Float32.toBits]
  rw [← h, Model.pack_unpack_of_valid _ _ hb]

/-- `castNat_f32 0` is `+0`. -/
theorem unpack_castNat_f32_zero : (castNat_f32 0).toModel.unpack = .zero .positive := by
  show (Float32.Model.pack (UnpackedFloat.ofNat Format.binary32 0)).unpack = _
  rw [unpack_pack_f32]
  rfl

/-- A finite value times `castNat_f32 0` is a zero (`+0` or `-0`). -/
theorem unpack_mul_castNat_f32_zero (s : Float32) (hs : s.isFinite = true) :
    ∃ τ, (s * castNat_f32 0).toModel.unpack = .zero τ := by
  show ∃ τ, (Float32.Model.pack (UnpackedFloat.mul Format.binary32 s.toModel.unpack
    (castNat_f32 0).toModel.unpack)).unpack = _
  rw [unpack_pack_f32, unpack_castNat_f32_zero]
  simp only [Float32.isFinite, Float32.Model.isFinite] at hs
  cases h : s.toModel.unpack <;> simp_all [UnpackedFloat.mul, UnpackedFloat.isFinite]

/-- Adding a zero to `x` gives exactly `x`, unless `x` is `-0` (bits `0x80000000`). -/
theorem add_zero_of_ne_negZero_f32 (x z : Float32) (τ : UnpackedFloat.Sign)
    (hz : z.toModel.unpack = .zero τ) (hx : x.toBits ≠ 0x80000000) : x + z = x := by
  show Float32.ofModel (Float32.Model.pack (UnpackedFloat.add Format.binary32 x.toModel.unpack
    z.toModel.unpack)) = x
  apply ofModel_pack_eq_of_unpack_f32
  rw [hz]
  cases h : x.toModel.unpack with
  | zero σ =>
    cases σ with
    | negative => exact absurd ((toBits_of_unpack_eq_zero_f32 x _ h).trans (by decide)) hx
    | positive => cases τ <;> rfl
  | _ => rfl

/-- When the step is finite, the first gain is exactly `start` (as bits, so also its sign),
unless `start` is `-0` (bits `0x80000000`). `start` itself may be anything else, even
infinite or NaN. -/
theorem rampGain_f32_zero_of_step (start «end» : Float32) (n : ℕ)
    (hs : (rampStep_f32 start «end» n).isFinite = true)
    (hz : start.toBits ≠ 0x80000000) : rampGain_f32 start «end» n 0 = start := by
  obtain ⟨τ, hτ⟩ := unpack_mul_castNat_f32_zero _ hs
  exact add_zero_of_ne_negZero_f32 _ _ τ hτ hz

/-- When the step is finite and `start` is `-0` (bits `0x80000000`), the first gain is `+0`
(bits `0`) or `-0`. -/
theorem rampGain_f32_zero_of_step_negZero (start «end» : Float32) (n : ℕ)
    (hs : (rampStep_f32 start «end» n).isFinite = true)
    (hz : start.toBits = 0x80000000) :
    (rampGain_f32 start «end» n 0).toBits = 0 ∨
      (rampGain_f32 start «end» n 0).toBits = 0x80000000 := by
  obtain ⟨τ, hτ⟩ := unpack_mul_castNat_f32_zero _ hs
  have hu : start.toModel.unpack = .zero .negative := by
    simp only [Float32.toBits] at hz
    simp only [Float32.Model.unpack, hz]
    rfl
  have hg : (rampGain_f32 start «end» n 0).toModel.unpack =
      .zero (if UnpackedFloat.Sign.negative = τ then .negative else .positive) := by
    show (Float32.Model.pack (UnpackedFloat.add Format.binary32 start.toModel.unpack
      (rampStep_f32 start «end» n * castNat_f32 0).toModel.unpack)).unpack = _
    rw [unpack_pack_f32, hu, hτ]
    cases τ <;> simp [UnpackedFloat.add]
  rw [toBits_of_unpack_eq_zero_f32 _ _ hg]
  cases τ
  · right; decide
  · left; decide

/-! ### Numbers -/

/-- `8·2^124` is at most the largest finite binary32 value. -/
theorem maxFinite_f32_ge : (8 : ℝ) * 2 ^ 124 ≤ maxFinite_f32 := by
  rw [maxFinite_f32_eq]
  have h : (8 : ℝ) * 2 ^ 124 = 2 ^ 23 * 2 ^ 104 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
  rw [h]
  gcongr
  norm_num

theorem unitRoundoff_f32_le : unitRoundoff_f32 ≤ 1 / 16 := by
  rw [unitRoundoff_f32_eq, zpow_neg]; norm_num

theorem underflowErr_f32_nonneg : 0 ≤ underflowErr_f32 := by
  rw [underflowErr_f32_eq]; positivity

theorem mul_underflowErr_f32_le (N : ℝ) (hN : N ≤ 2 ^ 24) : N * underflowErr_f32 ≤ 1 := by
  have h1 : (2 : ℝ) ^ 24 * 2 ^ (-150 : ℤ) ≤ 1 := by
    rw [zpow_neg, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 24 ≤ 150)
  calc N * underflowErr_f32 ≤ 2 ^ 24 * 2 ^ (-150 : ℤ) := by
        rw [underflowErr_f32_eq]
        exact mul_le_mul_of_nonneg_right hN (by positivity)
    _ ≤ 1 := h1

/-! ### Converting the index -/

/-- `castNat_f32 k`, imported into FloatLib, is Lean's integer conversion of `k`. -/
theorem toModel_ofFloat_castNat_f32 (k : ℕ) :
    toModel (ofFloat32 (castNat_f32 k) : Binary32) =
      Model.ofModel FloatFormat.binary32
        (Float.Model.UnpackedFloat.ofInt FloatFormat.binary32.toModel (k : Int)) := by
  rw [toModel_ofFloat32]
  rfl

/-- Converting any `k ≤ 2^64` (every `usize`) gives a finite value. -/
theorem isFinite_castNat_f32 (k : ℕ) (hk : k ≤ 2 ^ 64) : (castNat_f32 k).isFinite = true := by
  rw [← isFinite_ofFloat32_iff]
  unfold isFinite
  rw [toModel_ofFloat_castNat_f32, ofModel_ofNat_eq_roundDyadic _ (by decide)]
  apply Model.isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite _ (by decide)
  rw [Model.Dyadic.toReal_ofScaledInt_zero]
  have hk' : (k : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hk
  have hm : (k : ℝ) ≤ maxFinite_f32 := by
    have h1 : (2 : ℝ) ^ 64 ≤ 2 ^ 124 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    have h2 := maxFinite_f32_ge
    have h3 : (0 : ℝ) ≤ 2 ^ 124 := by positivity
    generalize (2 : ℝ) ^ 124 = B at h1 h2 h3
    linarith
  have : |((k : ℤ) : ℝ)| ≤ maxFinite_f32 := by
    simpa using hm
  exact this

/-- **How `i as f32` rounds:** for every `k ≤ 2^64` (every `usize`), the real value of
`castNat_f32 k` is `k` rounded to the nearest binary32 number, ties to even (FloatLib's
`roundAt`). -/
theorem real_castNat_f32_eq_roundAt (k : ℕ) (hk : k ≤ 2 ^ 64) :
    real_f32 (castNat_f32 k) = Model.roundAt FloatFormat.binary32 (k : ℝ) := by
  have hf := isFinite_ofFloat32 _ (isFinite_castNat_f32 k hk)
  unfold real_f32
  unfold isFinite at hf
  unfold toReal
  rw [toModel_ofFloat_castNat_f32] at hf ⊢
  rw [ofModel_ofNat_eq_roundDyadic _ (by decide)] at hf ⊢
  have h := Model.toReal_roundDyadic_eq_roundAt FloatFormat.binary32 (by decide) _ hf
  rw [Model.Dyadic.toReal_ofScaledInt_zero] at h
  exact h

/-- **`i as f32` is exact up to `2^24`:** for every `k ≤ 2^24`, the real value of
`castNat_f32 k` is exactly `k`. -/
theorem real_castNat_f32 (k : ℕ) (hk : k ≤ 2 ^ 24) : real_f32 (castNat_f32 k) = k := by
  rw [real_castNat_f32_eq_roundAt k (hk.trans (by norm_num))]
  have := Model.roundAt_intCast_of_abs_le FloatFormat.binary32 (n := (k : ℤ)) (by
    have hk' : (k : ℝ) ≤ 2 ^ 24 := by exact_mod_cast hk
    simpa [FloatFormat.binary32] using hk')
  simpa using this

/-- For `1 ≤ k ≤ 2^64`, `castNat_f32 k` is at least 1. -/
theorem one_le_real_castNat_f32 (k : ℕ) (h1 : 1 ≤ k) (hk : k ≤ 2 ^ 64) :
    1 ≤ real_f32 (castNat_f32 k) := by
  rw [real_castNat_f32_eq_roundAt k hk]
  have h := Model.roundAt_mono FloatFormat.binary32 (show (1 : ℝ) ≤ k by exact_mod_cast h1)
  rwa [Model.roundAt_one] at h

/-- **The step is finite** when `end - start` is (that is, when `start` and `end` are finite and
`end - start` does not overflow), for any block length `1 ≤ n < 2^64` (every nonempty
block). -/
theorem isFinite_rampStep_f32 (start «end» : Float32) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64)
    (hD : («end» - start).isFinite = true) : (rampStep_f32 start «end» n).isFinite = true := by
  have hcf := isFinite_castNat_f32 n hn.le
  have hc1 := one_le_real_castNat_f32 n hn1 hn.le
  apply isFinite_div_f32 _ _ hD hcf (ne_of_gt (by linarith))
  rw [abs_div, abs_of_pos (show 0 < real_f32 (castNat_f32 n) by linarith)]
  exact (div_le_self (abs_nonneg _) hc1).trans (abs_real_le_maxFinite_f32 _ hD)

/-- **The first gain is exactly `start`** (as bits) when `end - start` is finite (that is,
`start` and `end` are finite and `end - start` does not overflow), `1 ≤ n < 2^64`, and `start`
is not `-0` (bits `0x80000000`). -/
theorem rampGain_f32_zero (start «end» : Float32) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2 ^ 64)
    (hD : («end» - start).isFinite = true) (hz : start.toBits ≠ 0x80000000) :
    rampGain_f32 start «end» n 0 = start :=
  rampGain_f32_zero_of_step _ _ _ (isFinite_rampStep_f32 _ _ _ hn1 hn hD) hz

/-- Under the same conditions, but with `start` equal to `-0`, the first gain is `+0` (bits `0`)
or `-0`. -/
theorem rampGain_f32_zero_negZero (start «end» : Float32) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : n < 2 ^ 64)
    (hD : («end» - start).isFinite = true) (hz : start.toBits = 0x80000000) :
    (rampGain_f32 start «end» n 0).toBits = 0 ∨
      (rampGain_f32 start «end» n 0).toBits = 0x80000000 :=
  rampGain_f32_zero_of_step_negZero _ _ _ (isFinite_rampStep_f32 _ _ _ hn1 hn hD) hz

/-! ### Distance from the exact straight line -/

/-- The no-overflow bookkeeping shared by the theorems below: under their conditions,
`end - start` and the step are finite, and each is within one rounding of the exact
operation on its operands. -/
theorem rampStep_f32_facts (start «end» : Float32) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 24)
    (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f32 start| ≤ 2 ^ 124) (hEb : |real_f32 «end»| ≤ 2 ^ 124) :
    («end» - start).isFinite = true ∧ (rampStep_f32 start «end» n).isFinite = true ∧
      |real_f32 («end» - start) - (real_f32 «end» - real_f32 start)| ≤
        unitRoundoff_f32 * |real_f32 «end» - real_f32 start| + underflowErr_f32 ∧
      |real_f32 (rampStep_f32 start «end» n) - real_f32 («end» - start) / n| ≤
        unitRoundoff_f32 * |real_f32 («end» - start) / n| + underflowErr_f32 := by
  have hmax := maxFinite_f32_ge
  have hB1 : (1 : ℝ) ≤ 2 ^ 124 := one_le_pow₀ (by norm_num)
  generalize (2 : ℝ) ^ 124 = B at hmax hB1 hSb hEb
  have hDf : («end» - start).isFinite = true := by
    apply isFinite_sub_f32 _ _ hE hS
    have := abs_sub (real_f32 «end») (real_f32 start); linarith
  have hsf := isFinite_rampStep_f32 start «end» n hn1 (by omega) hDf
  have e2 := abs_real_div_sub_le_f32 _ _ hDf (isFinite_castNat_f32 n (by omega)) hsf
  rw [real_castNat_f32 n hn] at e2
  exact ⟨hDf, hsf, abs_real_sub_sub_le_f32 _ _ hE hS hDf, e2⟩

/-- **Each gain is close to the exact straight line.** When `start` and `end` are finite and at
most `2^124` in size, `1 ≤ n ≤ 2^24` and `i < n`: the gain of sample `i` is finite, and its
real value is within `u·|S| + 5u·|E - S| + (2n + 4)·η` of `S + (E - S)·i/n`, the exact straight
line through `S` at `i = 0` and `E` at `i = n`. Here `S` and `E` are the real values of `start`
and `end`, `u = 2^-24` the unit roundoff and `η = 2^-150` the underflow error. -/
theorem rampGain_f32_error (start «end» : Float32) (n i : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 24)
    (hi : i < n) (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f32 start| ≤ 2 ^ 124) (hEb : |real_f32 «end»| ≤ 2 ^ 124) :
    (rampGain_f32 start «end» n i).isFinite = true ∧
      |real_f32 (rampGain_f32 start «end» n i) -
          (real_f32 start + (real_f32 «end» - real_f32 start) * i / n)| ≤
        unitRoundoff_f32 * |real_f32 start| +
          5 * unitRoundoff_f32 * |real_f32 «end» - real_f32 start| +
          (2 * n + 4) * underflowErr_f32 := by
  obtain ⟨hDf, hsf, e1, e2⟩ := rampStep_f32_facts start «end» n hn1 hn hS hE hSb hEb
  have hu0 : 0 ≤ unitRoundoff_f32 := by rw [unitRoundoff_f32_eq]; positivity
  have hu := unitRoundoff_f32_le
  have hη := underflowErr_f32_nonneg
  have hmax := maxFinite_f32_ge
  have hB1 : (1 : ℝ) ≤ 2 ^ 124 := one_le_pow₀ (by norm_num)
  generalize (2 : ℝ) ^ 124 = B at hmax hB1 hSb hEb
  have hni : i ≤ 2 ^ 24 := by omega
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hNη : (n : ℝ) * underflowErr_f32 ≤ 1 := mul_underflowErr_f32_le n (by exact_mod_cast hn)
  have hiN : (i : ℝ) ≤ n := by exact_mod_cast hi.le
  have hη1 : underflowErr_f32 ≤ 1 := by nlinarith
  have hDb : |real_f32 «end» - real_f32 start| ≤ 2 * B := by
    have := abs_sub (real_f32 «end») (real_f32 start); linarith
  have hd := ramp_abs_d_le _ _ _ _ hu e1
  have hcif := isFinite_castNat_f32 i (hni.trans (by norm_num))
  have hcir := real_castNat_f32 i hni
  have hq := ramp_abs_si_le _ _ _ _ _ _ hu hη hN1 (Nat.cast_nonneg i) hiN e2
  -- The product.
  have hpf : (rampStep_f32 start «end» n * castNat_f32 i).isFinite = true :=
    isFinite_mul_f32 _ _ hsf hcif (by rw [hcir]; linarith)
  have e3 := abs_real_mul_sub_le_f32 _ _ hsf hcif hpf
  rw [hcir] at e3
  have hp := ramp_abs_p_le _ _ _ _ hu e3
  -- The sum.
  have hgf : (rampGain_f32 start «end» n i).isFinite = true := by
    apply isFinite_add_f32 _ _ hS hpf
    have := abs_add_le (real_f32 start) (real_f32 (rampStep_f32 start «end» n * castNat_f32 i))
    linarith
  have e4 := abs_real_add_sub_le_f32 _ _ hS hpf hgf
  exact ⟨hgf, ramp_error_real _ _ _ _ _ _ _ _ _ _ hu0 hu hη hN1 (Nat.cast_nonneg i) hiN
    e1 e2 e3 e4⟩

/-- **The step is close to `(E - S)/n`.** Under the conditions of `rampGain_f32_error`, the real
value of the step is within `3u·|E - S| + 3η` of `(E - S)/n`. -/
theorem rampStep_f32_error (start «end» : Float32) (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 24)
    (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f32 start| ≤ 2 ^ 124) (hEb : |real_f32 «end»| ≤ 2 ^ 124) :
    |real_f32 (rampStep_f32 start «end» n) - (real_f32 «end» - real_f32 start) / n| ≤
      3 * unitRoundoff_f32 * |real_f32 «end» - real_f32 start| + 3 * underflowErr_f32 := by
  obtain ⟨-, -, e1, e2⟩ := rampStep_f32_facts start «end» n hn1 hn hS hE hSb hEb
  have hu0 : 0 ≤ unitRoundoff_f32 := by rw [unitRoundoff_f32_eq]; positivity
  exact ramp_step_error_real _ _ _ _ _ _ hu0 unitRoundoff_f32_le underflowErr_f32_nonneg
    (by exact_mod_cast hn1) e1 e2

/-- **The last gain is close to `end - step`.** Under the conditions of `rampGain_f32_error`,
the real value of the last gain (`i = n - 1`) is within `u·|S| + 8u·|E - S| + (2n + 7)·η` of
`E - s`, where `s` is the real value of the step. -/
theorem rampGain_f32_last_error (start «end» : Float32) (n : ℕ) (hn1 : 1 ≤ n)
    (hn : n ≤ 2 ^ 24)
    (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f32 start| ≤ 2 ^ 124) (hEb : |real_f32 «end»| ≤ 2 ^ 124) :
    |real_f32 (rampGain_f32 start «end» n (n - 1)) -
        (real_f32 «end» - real_f32 (rampStep_f32 start «end» n))| ≤
      unitRoundoff_f32 * |real_f32 start| +
        8 * unitRoundoff_f32 * |real_f32 «end» - real_f32 start| +
        (2 * n + 7) * underflowErr_f32 := by
  have h1 := (rampGain_f32_error start «end» n (n - 1) hn1 hn (by omega) hS hE hSb hEb).2
  have h2 := rampStep_f32_error start «end» n hn1 hn hS hE hSb hEb
  have hN : (((n - 1 : ℕ) : ℝ)) = n - 1 := by rw [Nat.cast_sub hn1]; simp
  rw [hN] at h1
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  have he : real_f32 (rampGain_f32 start «end» n (n - 1)) -
        (real_f32 «end» - real_f32 (rampStep_f32 start «end» n)) =
      (real_f32 (rampGain_f32 start «end» n (n - 1)) -
          (real_f32 start + (real_f32 «end» - real_f32 start) * (n - 1) / n)) +
        (real_f32 (rampStep_f32 start «end» n) - (real_f32 «end» - real_f32 start) / n) := by
    field_simp; ring
  rw [he]
  have := abs_add_le (real_f32 (rampGain_f32 start «end» n (n - 1)) -
      (real_f32 start + (real_f32 «end» - real_f32 start) * (n - 1) / n))
    (real_f32 (rampStep_f32 start «end» n) - (real_f32 «end» - real_f32 start) / n)
  linarith

/-- **Steps inside a block are close to the step.** Under the conditions of
`rampGain_f32_error`, for `i + 1 < n`, the real gains of samples `i + 1` and `i` differ by `s`
(the real value of the step) to within `2u·|S| + 13u·|E - S| + (4n + 11)·η`. -/
theorem rampGain_f32_succ_sub (start «end» : Float32) (n i : ℕ) (hn1 : 1 ≤ n)
    (hn : n ≤ 2 ^ 24)
    (hi : i + 1 < n) (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hSb : |real_f32 start| ≤ 2 ^ 124) (hEb : |real_f32 «end»| ≤ 2 ^ 124) :
    |real_f32 (rampGain_f32 start «end» n (i + 1)) - real_f32 (rampGain_f32 start «end» n i) -
        real_f32 (rampStep_f32 start «end» n)| ≤
      2 * unitRoundoff_f32 * |real_f32 start| +
        13 * unitRoundoff_f32 * |real_f32 «end» - real_f32 start| +
        (4 * n + 11) * underflowErr_f32 := by
  have h1 := (rampGain_f32_error start «end» n (i + 1) hn1 hn hi hS hE hSb hEb).2
  have h0 := (rampGain_f32_error start «end» n i hn1 hn (by omega) hS hE hSb hEb).2
  have h2 := rampStep_f32_error start «end» n hn1 hn hS hE hSb hEb
  push_cast at h1
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  set g1 := real_f32 (rampGain_f32 start «end» n (i + 1))
  set g0 := real_f32 (rampGain_f32 start «end» n i)
  set s := real_f32 (rampStep_f32 start «end» n)
  set S := real_f32 start
  set E := real_f32 «end»
  have he : g1 - g0 - s = (g1 - (S + (E - S) * (i + 1) / n)) - (g0 - (S + (E - S) * i / n)) -
      (s - (E - S) / n) := by field_simp; ring
  rw [he]
  have ha := abs_sub (g1 - (S + (E - S) * (i + 1) / n) - (g0 - (S + (E - S) * i / n)))
    (s - (E - S) / n)
  have hb := abs_sub (g1 - (S + (E - S) * (i + 1) / n)) (g0 - (S + (E - S) * i / n))
  linarith

/-- **From one block to the next.** If a block from `start` to `end` of `n` samples is followed
by a block from `end` to any `end₂` of any length `1 ≤ m < 2^64`, with `end₂ - end` finite
(`end₂` finite and no overflow) and `end` not `-0`: the next block's first gain is exactly `end`,
and it differs from the real value of this block's last gain by `s` (this block's step) to
within `u·|S| + 8u·|E - S| + (2n + 7)·η`, under the conditions of `rampGain_f32_error` on this
block. -/
theorem rampGain_f32_next_block (start «end» end₂ : Float32) (n m : ℕ) (hn1 : 1 ≤ n)
    (hn : n ≤ 2 ^ 24) (hm1 : 1 ≤ m) (hm : m < 2 ^ 64)
    (hS : start.isFinite = true) (hE : «end».isFinite = true)
    (hD₂ : (end₂ - «end»).isFinite = true) (hz : «end».toBits ≠ 0x80000000)
    (hSb : |real_f32 start| ≤ 2 ^ 124) (hEb : |real_f32 «end»| ≤ 2 ^ 124) :
    rampGain_f32 «end» end₂ m 0 = «end» ∧
      |real_f32 (rampGain_f32 «end» end₂ m 0) -
          real_f32 (rampGain_f32 start «end» n (n - 1)) -
          real_f32 (rampStep_f32 start «end» n)| ≤
        unitRoundoff_f32 * |real_f32 start| +
          8 * unitRoundoff_f32 * |real_f32 «end» - real_f32 start| +
          (2 * n + 7) * underflowErr_f32 := by
  have h0 := rampGain_f32_zero «end» end₂ m hm1 hm hD₂ hz
  refine ⟨h0, ?_⟩
  rw [h0]
  have h := rampGain_f32_last_error start «end» n hn1 hn hS hE hSb hEb
  have he : real_f32 «end» - real_f32 (rampGain_f32 start «end» n (n - 1)) -
        real_f32 (rampStep_f32 start «end» n) =
      -(real_f32 (rampGain_f32 start «end» n (n - 1)) -
        (real_f32 «end» - real_f32 (rampStep_f32 start «end» n))) := by ring
  rw [he, abs_neg]
  exact h

/-! ### Direction -/

/-- The real value of a finite sum, product or quotient of finite binary32 numbers is the exact
result rounded to nearest. -/
theorem real_add_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x + y).isFinite = true) :
    real_f32 (x + y) = Model.roundAt FloatFormat.binary32 (real_f32 x + real_f32 y) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_add_of_isFinite x y hx hy] at h ⊢
  exact toReal_add_eq_roundAt h

theorem real_sub_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x - y).isFinite = true) :
    real_f32 (x - y) = Model.roundAt FloatFormat.binary32 (real_f32 x - real_f32 y) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_sub_of_isFinite x y hx hy] at h ⊢
  exact toReal_sub_eq_roundAt h

theorem real_mul_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x * y).isFinite = true) :
    real_f32 (x * y) = Model.roundAt FloatFormat.binary32 (real_f32 x * real_f32 y) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_mul_of_isFinite x y hx hy] at h ⊢
  exact toReal_mul_eq_roundAt h

theorem real_div_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x / y).isFinite = true) :
    real_f32 (x / y) = Model.roundAt FloatFormat.binary32 (real_f32 x / real_f32 y) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_div_of_isFinite x y hx hy] at h ⊢
  exact toReal_div_eq_roundAt (isFinite_ofFloat32 y hy) h

/-- The real value of a finite gain, as nested roundings. -/
theorem real_rampGain_f32 (start «end» : Float32) (n i : ℕ) (hn : n ≤ 2 ^ 64)
    (hi : i ≤ 2 ^ 64)
    (h : (rampGain_f32 start «end» n i).isFinite = true) :
    real_f32 (rampGain_f32 start «end» n i) =
      Model.roundAt FloatFormat.binary32 (real_f32 start +
        Model.roundAt FloatFormat.binary32 (real_f32 (rampStep_f32 start «end» n) *
          Model.roundAt FloatFormat.binary32 i)) ∧
      real_f32 (rampStep_f32 start «end» n) =
        Model.roundAt FloatFormat.binary32 (Model.roundAt FloatFormat.binary32
          (real_f32 «end» - real_f32 start) / Model.roundAt FloatFormat.binary32 n) := by
  obtain ⟨hS, hE, hD, hs⟩ := isFinite_of_rampGain_f32 start «end» n i h
  have hci := isFinite_castNat_f32 i hi
  have hcn := isFinite_castNat_f32 n hn
  have hp : (rampStep_f32 start «end» n * castNat_f32 i).isFinite = true := by
    cases hp : (rampStep_f32 start «end» n * castNat_f32 i).isFinite
    · rw [rampGain_f32_eq, isFinite_add_eq_false_f32 _ _ (Or.inr hp)] at h
      exact absurd h (by decide)
    · rfl
  constructor
  · rw [rampGain_f32_eq, real_add_f32 _ _ hS hp h, real_mul_f32 _ _ hs hci hp,
      real_castNat_f32_eq_roundAt i hi]
  · rw [rampStep_f32, real_div_f32 _ _ hD hcn hs, real_sub_f32 _ _ hE hS hD,
      real_castNat_f32_eq_roundAt n hn]

/-- **The gains never go the wrong way.** For samples `i ≤ j ≤ 2^64` of a block of length
`n ≤ 2^64` whose gains are finite: if `start ≤ end` (as real numbers) then gain `i` is at most
gain `j`, and if `end ≤ start` then gain `j` is at most gain `i`. -/
theorem rampGain_f32_mono (start «end» : Float32) (n i j : ℕ) (hn : n ≤ 2 ^ 64)
    (hij : i ≤ j) (hj : j ≤ 2 ^ 64)
    (hi_fin : (rampGain_f32 start «end» n i).isFinite = true)
    (hj_fin : (rampGain_f32 start «end» n j).isFinite = true) :
    (real_f32 start ≤ real_f32 «end» →
        real_f32 (rampGain_f32 start «end» n i) ≤
          real_f32 (rampGain_f32 start «end» n j)) ∧
      (real_f32 «end» ≤ real_f32 start →
        real_f32 (rampGain_f32 start «end» n j) ≤
          real_f32 (rampGain_f32 start «end» n i)) := by
  obtain ⟨hgi, hs⟩ := real_rampGain_f32 start «end» n i hn (hij.trans hj) hi_fin
  obtain ⟨hgj, -⟩ := real_rampGain_f32 start «end» n j hn hj hj_fin
  have hn0 : 0 ≤ Model.roundAt FloatFormat.binary32 (n : ℝ) :=
    Model.roundAt_nonneg FloatFormat.binary32 (by positivity)
  have hij' : Model.roundAt FloatFormat.binary32 (i : ℝ) ≤
      Model.roundAt FloatFormat.binary32 (j : ℝ) :=
    Model.roundAt_mono FloatFormat.binary32 (by exact_mod_cast hij)
  rw [hgi, hgj]
  constructor
  · intro hSE
    have hs0 : 0 ≤ real_f32 (rampStep_f32 start «end» n) := by
      rw [hs]
      exact Model.roundAt_nonneg FloatFormat.binary32
        (div_nonneg (Model.roundAt_nonneg FloatFormat.binary32 (by linarith)) hn0)
    have h1 := Model.roundAt_mono FloatFormat.binary32 (mul_le_mul_of_nonneg_left hij' hs0)
    apply Model.roundAt_mono FloatFormat.binary32
    linarith
  · intro hES
    have hs0 : real_f32 (rampStep_f32 start «end» n) ≤ 0 := by
      rw [hs]
      exact Model.roundAt_nonpos FloatFormat.binary32 (div_nonpos_of_nonpos_of_nonneg
        (Model.roundAt_nonpos FloatFormat.binary32 (by linarith)) hn0)
    have h1 := Model.roundAt_mono FloatFormat.binary32 (mul_le_mul_of_nonpos_left hij' hs0)
    apply Model.roundAt_mono FloatFormat.binary32
    linarith

end RampValues

end conjure_dsp_lib.gain
