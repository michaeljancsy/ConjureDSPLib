module

public import ConjureDSPLib.LinearSmoother.SpecF64
public import ConjureDSPLib.Gain.BridgeF64
public import ConjureDSPLib.Gain.Line

/-!
# The linear smoother in f64: distance from the exact straight line

`rampValue_f64_error`: with the starting value `S` and the target `T` finite and at most
`2^1020` in size, and `1 ≤ n ≤ 2^53` steps, the value after `k < n` steps,
`rampValue_f64 start target n k = target - ((target - start) / n) * (n - k)` in binary64, is
finite and within `u·|T| + 5u·|T - S| + (2n + 4)·η` of the straight line `S + (T - S)·k/n`
(`u = 2⁻⁵³`, `η = 2⁻¹⁰⁷⁵`). The real-number argument is the gain ramp's (`gain.ramp_error_real`),
run from the target backwards.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange
open conjure_dsp_lib.gain (castNat_f64 rampStep_f64)

namespace conjure_dsp_lib.linear_smoother

/-- **Close to the exact straight line.** When `start` and `target` are finite and at most
`2^1020` in size, `1 ≤ n ≤ 2^53` and `k < n`: `rampValue_f64 start target n k` is finite, and its
real value is within `u·|T| + 5u·|T - S| + (2n + 4)·η` of `S + (T - S)·k/n`, where `S` and `T`
are the real values of `start` and `target`, `u = 2⁻⁵³` the unit roundoff and `η = 2⁻¹⁰⁷⁵` the
underflow error. -/
theorem rampValue_f64_error (start target : Float) (n k : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 2 ^ 53)
    (hk : k < n) (hS : start.isFinite = true) (hT : target.isFinite = true)
    (hSb : |real_f64 start| ≤ 2 ^ 1020) (hTb : |real_f64 target| ≤ 2 ^ 1020) :
    (rampValue_f64 start target n k).isFinite = true ∧
      |real_f64 (rampValue_f64 start target n k) -
          (real_f64 start + (real_f64 target - real_f64 start) * k / n)| ≤
        unitRoundoff_f64 * |real_f64 target| +
          5 * unitRoundoff_f64 * |real_f64 target - real_f64 start| +
          (2 * n + 4) * underflowErr_f64 := by
  obtain ⟨hDf, hsf, e1, e2⟩ := gain.rampStep_f64_facts start target n hn1 hn hS hT hSb hTb
  have hu0 : 0 ≤ unitRoundoff_f64 := by rw [unitRoundoff_f64_eq]; positivity
  have hu := unitRoundoff_f64_le
  have hη := underflowErr_f64_nonneg
  have hmax := maxFinite_f64_ge
  have hB1 : (1 : ℝ) ≤ 2 ^ 1020 := one_le_pow₀ (by norm_num)
  generalize (2 : ℝ) ^ 1020 = B at hmax hB1 hSb hTb
  have hr : n - k ≤ 2 ^ 53 := by omega
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hNη : (n : ℝ) * underflowErr_f64 ≤ 1 := mul_underflowErr_f64_le n (by exact_mod_cast hn)
  have hrN : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
  have hη1 : underflowErr_f64 ≤ 1 := by
    have := le_mul_of_one_le_left hη hN1
    linarith
  have hDb : |real_f64 target - real_f64 start| ≤ 2 * B := by
    have := abs_sub (real_f64 target) (real_f64 start); linarith
  have hd := gain.abs_rounded_le _ _ _ _ hu e1
  have hcrf := gain.isFinite_castNat_f64 (n - k) (hr.trans (by norm_num))
  have hcrr := gain.real_castNat_f64 (n - k) hr
  have hq := gain.ramp_abs_si_le _ _ _ _ _ _ hu hη hN1 (Nat.cast_nonneg _) hrN e2
  -- The product.
  have hpf : (rampStep_f64 start target n * castNat_f64 (n - k)).isFinite = true :=
    isFinite_mul_f64 _ _ hsf hcrf (by rw [hcrr]; linarith)
  have e3 := abs_real_mul_sub_le_f64 _ _ hsf hcrf hpf
  rw [hcrr] at e3
  have hp := gain.abs_rounded_le _ _ _ _ hu e3
  -- The difference.
  have hvf : (rampValue_f64 start target n k).isFinite = true := by
    apply isFinite_sub_f64 _ _ hT hpf
    have := abs_sub (real_f64 target) (real_f64 (rampStep_f64 start target n * castNat_f64 (n - k)))
    linarith
  have e4 := abs_real_sub_sub_le_f64 _ _ hT hpf hvf
  refine ⟨hvf, ?_⟩
  -- The gain ramp's argument, with every quantity but the target negated.
  have h := gain.ramp_error_real unitRoundoff_f64 underflowErr_f64 (real_f64 target)
    (-(real_f64 target - real_f64 start)) (-real_f64 (target - start))
    (-real_f64 (rampStep_f64 start target n))
    (-real_f64 (rampStep_f64 start target n * castNat_f64 (n - k)))
    (real_f64 (rampValue_f64 start target n k)) n ((n - k : ℕ) : ℝ) hu0 hu hη hN1
    (Nat.cast_nonneg _) hrN
    (by rw [show -real_f64 (target - start) - -(real_f64 target - real_f64 start) =
          -(real_f64 (target - start) - (real_f64 target - real_f64 start)) by ring, abs_neg,
          abs_neg]; exact e1)
    (by rw [show -real_f64 (rampStep_f64 start target n) - -real_f64 (target - start) / n =
          -(real_f64 (rampStep_f64 start target n) - real_f64 (target - start) / n) by ring,
          abs_neg, neg_div, abs_neg]; exact e2)
    (by rw [show -real_f64 (rampStep_f64 start target n * castNat_f64 (n - k)) -
            -real_f64 (rampStep_f64 start target n) * ((n - k : ℕ) : ℝ) =
          -(real_f64 (rampStep_f64 start target n * castNat_f64 (n - k)) -
            real_f64 (rampStep_f64 start target n) * ((n - k : ℕ) : ℝ)) by ring, abs_neg,
          neg_mul, abs_neg]; exact e3)
    (by rw [← sub_eq_add_neg]; exact e4)
  rw [abs_neg] at h
  have hline : real_f64 target + -(real_f64 target - real_f64 start) * ((n - k : ℕ) : ℝ) / n =
      real_f64 start + (real_f64 target - real_f64 start) * k / n := by
    rw [Nat.cast_sub hk.le]
    field_simp
    ring
  rw [hline] at h
  exact h

end conjure_dsp_lib.linear_smoother

end
