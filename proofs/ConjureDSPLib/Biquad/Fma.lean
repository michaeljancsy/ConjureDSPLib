module

public import ConjureDSPLib.Biquad.Block

/-!
# The fused biquad step: its roundings, on real numbers

The fused step (`step_fma_f64`, `step_fma_f32` in `src/biquad.rs`) computes
`y = b0.mul_add(x, s1)`, `s1' = b1.mul_add(x, -(a1·y)) + s2`, `s2' = b2.mul_add(x, -(a2·y))`:
six roundings instead of nine, since the products `b0·x`, `b1·x` and `b2·x` are not rounded on
their own. `step_localErr_fma` gives it the same per-step bound `α + β·Sb` as the unfused step
(`step_localErr`), so the whole-block theorems of `Block.lean`, the `Contraction`s of
`Contraction.lean` and the constants built from `localErrBase` and `localErrSlope` all apply
unchanged.
-/

@[expose] public section

namespace conjure_dsp_lib.biquad

/-- An exact operation is within any rounding bound `u·|e| + η` (`u, η ≥ 0`) of itself. -/
theorem exact_within {u η e : ℝ} (hu : 0 ≤ u) (hη : 0 ≤ η) : |e - e| ≤ u * |e| + η := by
  rw [sub_self, abs_zero]; positivity

/-- **One fused step's roundings, on real numbers.** The fused transposed-direct-form-II step,
with six roundings, each within `u·|e| + η` of the exact operation `e` on the computed operands:
output `Y ≈ b0·X + S1`, `Q1 ≈ a1·Y`, `D1 ≈ b1·X - Q1`, new state `T1 ≈ D1 + S2`, `Q2 ≈ a2·Y`, new
state `T2 ≈ b2·X - Q2`. If `0 ≤ u ≤ 1`, `0 ≤ η`, `|X| ≤ M` and `|S1|, |S2| ≤ Sb`, then `Y`, `T1`
and `T2` are each within `localErrBase c u η M + localErrSlope c u · Sb` of the exact step from
the computed state and the computed output: the bound of the unfused step (`step_localErr`). -/
theorem step_localErr_fma (c : CoeffsReal) {u η M Sb X S1 S2 Y Q1 D1 T1 Q2 T2 : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hη : 0 ≤ η)
    (hX : |X| ≤ M) (hS1 : |S1| ≤ Sb) (hS2 : |S2| ≤ Sb)
    (hY : |Y - (c.b0 * X + S1)| ≤ u * |c.b0 * X + S1| + η)
    (hQ1 : |Q1 - c.a1 * Y| ≤ u * |c.a1 * Y| + η)
    (hD1 : |D1 - (c.b1 * X - Q1)| ≤ u * |c.b1 * X - Q1| + η)
    (hT1 : |T1 - (D1 + S2)| ≤ u * |D1 + S2| + η)
    (hQ2 : |Q2 - c.a2 * Y| ≤ u * |c.a2 * Y| + η)
    (hT2 : |T2 - (c.b2 * X - Q2)| ≤ u * |c.b2 * X - Q2| + η) :
    let L := localErrBase c u η M + localErrSlope c u * Sb
    |Y - (c.b0 * X + S1)| ≤ L ∧ |T1 - (c.b1 * X - c.a1 * Y + S2)| ≤ L ∧
      |T2 - (c.b2 * X - c.a2 * Y)| ≤ L :=
  -- The unfused bound, with the three products `b·X` taken as exact.
  step_localErr c hu0 hu1 hη hX hS1 hS2 (exact_within hu0 hη) hY (exact_within hu0 hη) hQ1 hD1
    hT1 (exact_within hu0 hη) hQ2 hT2

end conjure_dsp_lib.biquad

end
