module

public import ConjureDSPLib.Svf.Block
public import ConjureDSPLib.Biquad.Fma

/-!
# The fused state-variable-filter step: its roundings, on real numbers

The fused step (`step_fma_f64`, `step_fma_f32` in `src/svf.rs`) computes
`hp = ((-(k + g)).mul_add(s1, x) - s2)·d`, `bp = g.mul_add(hp, s1)`, `lp = g.mul_add(bp, s2)`,
`s1' = g.mul_add(hp, bp)`, `s2' = g.mul_add(bp, lp)` and
`y = m_lp.mul_add(lp, m_hp.mul_add(hp, m_bp·bp))`: eleven roundings instead of sixteen, since the
products `(k + g)·s1`, `g·hp`, `g·bp`, `m_hp·hp` and `m_lp·lp` are not rounded on their own.
`step_localErr_fma` gives it the bounds `stepErrOut` and `stepErrState` of the unfused step
(`step_localErr`), so the whole-block theorems of `Block.lean`, the `Contraction`s of
`Contraction.lean` and the constants built from those bounds all apply unchanged.
-/

@[expose] public section

namespace conjure_dsp_lib.svf

open conjure_dsp_lib.biquad (exact_within)

/-- **One fused step's roundings, on real numbers.** The fused step, with eleven roundings, each
within `u·|e| + η` of the exact operation `e` on the computed operands: `K1 ≈ k + g`,
`D1 ≈ X - K1·S1`, `D2 ≈ D1 - S2`, `H ≈ D2·d` (the computed `hp`), `B ≈ g·H + S1` (`bp`),
`Lp ≈ g·B + S2` (`lp`), `Y2 ≈ m_bp·B`, `Y3 ≈ m_hp·H + Y2`, output `Y ≈ Y3 + m_lp·Lp`, new state
`T1 ≈ g·H + B` and `T2 ≈ g·B + Lp`. If `0 ≤ u`, `0 ≤ η`, `|X| ≤ M` and `|S1|, |S2| ≤ Sb`, then
the output is within `stepErrOut c u η M Sb` of the exact step's (`svfStep_real`), and the
distances of the two new state values from the exact step's add up to at most
`stepErrState c u η M Sb`: the bounds of the unfused step (`step_localErr`). -/
theorem step_localErr_fma (c : CoeffsReal)
    {u η M Sb X S1 S2 K1 D1 D2 H B Lp Y2 Y3 Y T1 T2 : ℝ}
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hX : |X| ≤ M) (hS1 : |S1| ≤ Sb) (hS2 : |S2| ≤ Sb)
    (h1 : |K1 - (c.k + c.g)| ≤ u * |c.k + c.g| + η)
    (h3 : |D1 - (X - K1 * S1)| ≤ u * |X - K1 * S1| + η)
    (h4 : |D2 - (D1 - S2)| ≤ u * |D1 - S2| + η)
    (h5 : |H - D2 * c.d| ≤ u * |D2 * c.d| + η)
    (h7 : |B - (c.g * H + S1)| ≤ u * |c.g * H + S1| + η)
    (h9 : |Lp - (c.g * B + S2)| ≤ u * |c.g * B + S2| + η)
    (h11 : |Y2 - c.m_bp * B| ≤ u * |c.m_bp * B| + η)
    (h12 : |Y3 - (c.m_hp * H + Y2)| ≤ u * |c.m_hp * H + Y2| + η)
    (h14 : |Y - (Y3 + c.m_lp * Lp)| ≤ u * |Y3 + c.m_lp * Lp| + η)
    (h15 : |T1 - (c.g * H + B)| ≤ u * |c.g * H + B| + η)
    (h16 : |T2 - (c.g * B + Lp)| ≤ u * |c.g * B + Lp| + η) :
    |Y - (svfStep_real c (S1, S2) X).1| ≤ stepErrOut c u η M Sb ∧
      |T1 - (svfStep_real c (S1, S2) X).2.1| + |T2 - (svfStep_real c (S1, S2) X).2.2| ≤
        stepErrState c u η M Sb :=
  -- The unfused bounds, with the five fused products taken as exact.
  step_localErr c (P := K1 * S1) (Q := c.g * H) (R := c.g * B) (Y1 := c.m_hp * H)
    (Y4 := c.m_lp * Lp) hu hη hX hS1 hS2 h1 (exact_within hu hη) h3 h4 h5 (exact_within hu hη)
    h7 (exact_within hu hη) h9 (exact_within hu hη) h11 h12 (exact_within hu hη) h14 h15 h16

end conjure_dsp_lib.svf

end
