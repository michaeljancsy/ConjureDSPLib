module

public import ConjureDSPLib.Code.Funs

/-!
# The state-variable filter in f64: what the translated Rust does

About `CoeffsF64.new`, its design functions (`low_pass` to `high_shelf`), `step_f64` and
`process_f64` from `src/svf.rs`, as Aeneas translated them. This file proves:

1. `CoeffsF64.new_eq`: the Rust constructor never fails, keeps `g`, `k` and the output mix, and
   computes `d` as exactly `1 / (1 + g * (g + k))` in Lean's `Float` (IEEE binary64), in that
   order.
2. `CoeffsF64.low_pass_eq`, `high_pass_eq`, `band_pass_eq`, `notch_eq`, `all_pass_eq`, `bell_eq`,
   `low_shelf_eq`, `high_shelf_eq`: each design function never fails and returns exactly the
   coefficients of its formula, in binary64, in the Rust code's order, with libm's functions as
   the unknown functions `libm.tanModel_f64`, `libm.powModel_f64` and `libm.sqrtModel_f64`. Nothing
   about the resulting frequency responses is proved.
3. `step_f64_eq`: one Rust step is exactly `svfStep_f64` in binary64, in the Rust code's order,
   and never fails.
4. `process_f64_spec`: the Rust block loop never fails and produces exactly the outputs and final
   state of `filt_f64`, which applies `svfStep_f64` to each sample in turn.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.svf

/-- The Rust constructor never fails: it keeps `g`, `k`, `m_hp`, `m_bp` and `m_lp`, and computes
`d = 1 / (1 + g * (g + k))` in binary64, in that order (`1` is the binary64 number 1). -/
theorem CoeffsF64.new_eq (g k m_hp m_bp m_lp : Float) :
    CoeffsF64.new g k m_hp m_bp m_lp =
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := m_hp, m_bp := m_bp,
           m_lp := m_lp } := rfl

/-- Low-pass design: never fails, and returns exactly these coefficients, each operation in
binary64 in this order:
`g = libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)`,
`k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix
`(m_hp, m_bp, m_lp) = (0, 0, 1)`. `libm.tanModel_f64` is an unknown function
(`Code/FunsExternal.lean`). -/
theorem CoeffsF64.low_pass_eq (cutoff_hz sample_rate_hz q : Float) :
    CoeffsF64.low_pass cutoff_hz sample_rate_hz q =
      let g := libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)
      let k := 1 / q
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := 0, m_bp := 0,
           m_lp := 1 } := by
  simp only [CoeffsF64.low_pass, libm.math.tan.tan, bind_ok]
  rfl

/-- High-pass design: never fails, and returns exactly these coefficients, each operation in
binary64 in this order:
`g = libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)`,
`k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix
`(m_hp, m_bp, m_lp) = (1, 0, 0)`. `libm.tanModel_f64` is an unknown function
(`Code/FunsExternal.lean`). -/
theorem CoeffsF64.high_pass_eq (cutoff_hz sample_rate_hz q : Float) :
    CoeffsF64.high_pass cutoff_hz sample_rate_hz q =
      let g := libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)
      let k := 1 / q
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := 1, m_bp := 0,
           m_lp := 0 } := by
  simp only [CoeffsF64.high_pass, libm.math.tan.tan, bind_ok]
  rfl

/-- Band-pass design: never fails, and returns exactly these coefficients, each operation in
binary64 in this order:
`g = libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)`,
`k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix
`(m_hp, m_bp, m_lp) = (0, k, 0)`. `libm.tanModel_f64` is an unknown function
(`Code/FunsExternal.lean`). -/
theorem CoeffsF64.band_pass_eq (cutoff_hz sample_rate_hz q : Float) :
    CoeffsF64.band_pass cutoff_hz sample_rate_hz q =
      let g := libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)
      let k := 1 / q
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := 0, m_bp := k,
           m_lp := 0 } := by
  simp only [CoeffsF64.band_pass, libm.math.tan.tan, bind_ok]
  rfl

/-- Notch design: never fails, and returns exactly these coefficients, each operation in
binary64 in this order:
`g = libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)`,
`k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix
`(m_hp, m_bp, m_lp) = (1, 0, 1)`. `libm.tanModel_f64` is an unknown function
(`Code/FunsExternal.lean`). -/
theorem CoeffsF64.notch_eq (cutoff_hz sample_rate_hz q : Float) :
    CoeffsF64.notch cutoff_hz sample_rate_hz q =
      let g := libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)
      let k := 1 / q
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := 1, m_bp := 0,
           m_lp := 1 } := by
  simp only [CoeffsF64.notch, libm.math.tan.tan, bind_ok]
  rfl

/-- All-pass design: never fails, and returns exactly these coefficients, each operation in
binary64 in this order:
`g = libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)`,
`k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix
`(m_hp, m_bp, m_lp) = (1, -k, 1)`. `libm.tanModel_f64` is an unknown function
(`Code/FunsExternal.lean`). -/
theorem CoeffsF64.all_pass_eq (cutoff_hz sample_rate_hz q : Float) :
    CoeffsF64.all_pass cutoff_hz sample_rate_hz q =
      let g := libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)
      let k := 1 / q
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := 1, m_bp := -k,
           m_lp := 1 } := by
  simp only [CoeffsF64.all_pass, libm.math.tan.tan, bind_ok]
  rfl

/-- Bell design: never fails, and returns exactly these coefficients, each operation in
binary64 in this order: `A = libm.powModel_f64 10 (gain_db / 40)`,
`g = libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)`,
`k = 1 / (q * A)`, `d = 1 / (1 + g * (g + k))` and the mix
`(m_hp, m_bp, m_lp) = (1, k * A * A, 1)`.
`libm.tanModel_f64` and `libm.powModel_f64` are unknown functions (`Code/FunsExternal.lean`). -/
theorem CoeffsF64.bell_eq (cutoff_hz sample_rate_hz q gain_db : Float) :
    CoeffsF64.bell cutoff_hz sample_rate_hz q gain_db =
      let A := libm.powModel_f64 10 (gain_db / 40)
      let g := libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz)
      let k := 1 / (q * A)
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := 1, m_bp := k * A * A,
           m_lp := 1 } := by
  simp only [CoeffsF64.bell, libm.math.pow.pow, libm.math.tan.tan, bind_ok]
  rfl

/-- Low-shelf design: never fails, and returns exactly these coefficients, each operation in
binary64 in this order: `A = libm.powModel_f64 10 (gain_db / 40)`,
`g = libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz) / libm.sqrtModel_f64 A`,
`k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix
`(m_hp, m_bp, m_lp) = (1, k * A, A * A)`.
`libm.tanModel_f64`, `libm.powModel_f64` and `libm.sqrtModel_f64` are unknown functions
(`Code/FunsExternal.lean`). -/
theorem CoeffsF64.low_shelf_eq (cutoff_hz sample_rate_hz q gain_db : Float) :
    CoeffsF64.low_shelf cutoff_hz sample_rate_hz q gain_db =
      let A := libm.powModel_f64 10 (gain_db / 40)
      let g := libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz) /
          libm.sqrtModel_f64 A
      let k := 1 / q
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := 1, m_bp := k * A,
           m_lp := A * A } := by
  simp only [CoeffsF64.low_shelf, libm.math.pow.pow, libm.math.tan.tan, libm.math.sqrt.sqrt,
    bind_ok]
  rfl

/-- High-shelf design: never fails, and returns exactly these coefficients, each operation in
binary64 in this order: `A = libm.powModel_f64 10 (gain_db / 40)`,
`g = libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz) * libm.sqrtModel_f64 A`,
`k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix
`(m_hp, m_bp, m_lp) = (A * A, k * A, 1)`.
`libm.tanModel_f64`, `libm.powModel_f64` and `libm.sqrtModel_f64` are unknown functions
(`Code/FunsExternal.lean`). -/
theorem CoeffsF64.high_shelf_eq (cutoff_hz sample_rate_hz q gain_db : Float) :
    CoeffsF64.high_shelf cutoff_hz sample_rate_hz q gain_db =
      let A := libm.powModel_f64 10 (gain_db / 40)
      let g := libm.tanModel_f64 (core.f64.consts.PI * cutoff_hz / sample_rate_hz) *
          libm.sqrtModel_f64 A
      let k := 1 / q
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := A * A, m_bp := k * A,
           m_lp := 1 } := by
  simp only [CoeffsF64.high_shelf, libm.math.pow.pow, libm.math.tan.tan,
    libm.math.sqrt.sqrt, bind_ok]
  rfl

/-- One trapezoidal state-variable-filter step in binary64, high-pass signal first: the output
and the new state, computed in the same order as the Rust code. -/
def svfStep_f64 (c : CoeffsF64) (s : StateF64) (x : Float) : Float × StateF64 :=
  let hp := (x - (c.k + c.g) * s.s1 - s.s2) * c.d
  let bp := c.g * hp + s.s1
  let lp := c.g * bp + s.s2
  (c.m_hp * hp + c.m_bp * bp + c.m_lp * lp, { s1 := c.g * hp + bp, s2 := c.g * bp + lp })

/-- One Rust step is exactly `svfStep_f64`, and cannot fail. -/
theorem step_f64_eq (c : CoeffsF64) (s : StateF64) (x : Float) :
    step_f64 c s x = ok (svfStep_f64 c s x) := rfl

/-- The filter on binary64 numbers: run `svfStep_f64` over a list of input samples from state `s`,
returning the final state and the list of outputs. -/
def filt_f64 (c : CoeffsF64) : StateF64 → List Float → StateF64 × List Float
  | s, [] => (s, [])
  | s, x :: xs =>
    let r := filt_f64 c (svfStep_f64 c s x).2 xs
    (r.1, (svfStep_f64 c s x).1 :: r.2)

/-- One loop iteration on plain lists: overwriting sample `j` with its filtered value and moving
on to `j + 1` doesn't change the final answer. -/
theorem filt_f64_set_step (c : CoeffsF64) (s : StateF64) (l : List Float) (j : ℕ)
    (hj : j < l.length) :
    (l.set j (svfStep_f64 c s l[j]).1).take (j + 1) ++
        (filt_f64 c (svfStep_f64 c s l[j]).2 ((l.set j (svfStep_f64 c s l[j]).1).drop (j + 1))).2 =
      l.take j ++ (filt_f64 c s (l.drop j)).2 ∧
    (filt_f64 c (svfStep_f64 c s l[j]).2 ((l.set j (svfStep_f64 c s l[j]).1).drop (j + 1))).1 =
      (filt_f64 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (svfStep_f64 c s l[j]).1).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (svfStep_f64 c s l[j]).1).take (j + 1) =
      l.take j ++ [(svfStep_f64 c s l[j]).1] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_f64]

/-- The loop, started at position `i`, leaves the first `i` samples alone and filters the rest.
`f ⦃ P ⦄` is Aeneas's notation for "running `f` never fails, and its result satisfies `P`". -/
theorem process_f64_loop_spec (c : CoeffsF64) (state : StateF64) (buf : Slice Float)
    (i : Std.Usize) (hi : i.val ≤ buf.length) :
    process_f64_loop c state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_f64 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_f64 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_f64_loop
  -- Invariant on the loop state `(s, b, j)`: the buffer keeps its length, and finishing the job
  -- from here (keep `b`'s first `j` samples, filter the rest from state `s`) gives the same answer
  -- as filtering from the start.
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_f64 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_f64 c state (buf.val.drop i.val)).2 ∧
      (filt_f64 c x.1 (x.2.1.val.drop x.2.2.val)).1 = (filt_f64 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_f64_loop.body, step_f64_eq]
    step*
    · -- Still looping: name the step's output and new state, then rebuild the invariant one
      -- sample further on.
      subst fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_f64_set_step c st b.val j.val hjl
      generalize hT : svfStep_f64 c st (↑b)[↑j] = T at h1 h2
      obtain ⟨y, s'⟩ := T
      step*
      subst s_post
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · -- Finished: the whole buffer is processed.
      have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_f64] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- The Rust block-processing function never fails, and its output samples and final state are
exactly those of `filt_f64`, sample by sample. -/
theorem process_f64_spec (c : CoeffsF64) (state : StateF64) (buf : Slice Float) :
    process_f64 c state buf ⦃ fun r =>
      r.2.val = (filt_f64 c state buf.val).2 ∧ r.1 = (filt_f64 c state buf.val).1 ⦄ := by
  simpa using process_f64_loop_spec c state buf 0#usize (by simp)

end conjure_dsp_lib.svf

end
