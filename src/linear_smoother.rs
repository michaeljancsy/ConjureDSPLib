//! Linear smoother: a value that moves in a straight line to a new target over a set number of
//! samples, then stays there.
//!
//! The state ([`StateF64`], [`StateF32`]) is kept by the caller and carried from block to block:
//! the current `value`, the `step` per sample, the number of samples `remaining` and the
//! `target`. Each channel or parameter needs its own state.
//!
//! - [`set_target_f64`]`(state, target, steps)` starts a ramp from the current `value` to
//!   `target` over `steps` samples. With `steps = 0` the value jumps to `target` at once. A new
//!   target in the middle of a ramp starts a new ramp from wherever the value is.
//! - [`step_f64`]`(state)` moves one sample on and returns the new value.
//! - [`process_f64`]`(state, buf)` fills `buf` with the next `buf.len()` values.
//!
//! **What each call computes.** `set_target` computes `step = (target - value) / steps`
//! once. While `remaining > 0`, each `step` call takes one off `remaining` and then sets
//! `value = target - step * remaining`, computed from the target and the count in that order,
//! not by adding `step` repeatedly; when `remaining` reaches 0 it sets `value = target` exactly,
//! by assignment. Once `remaining` is 0, `step` returns `value` unchanged and changes nothing
//! (`linear_smoother.step_f64_spec`, `linear_smoother.process_f64_spec`).
//!
//! Proved in Lean (`proofs/ConjureDSPLib/LinearSmoother/`), under the assumptions in
//! `proofs/README.md`, with `S` and `T` the values of the starting `value` and the `target`,
//! `u = 2^-53` and `η = 2^-1075` in `f64` (`u = 2^-24`, `η = 2^-150` in `f32`):
//!
//! - **Never panics**, for any state and block (`linear_smoother.process_f64_ok`; `set_target`
//!   and `step` never panic either, `linear_smoother.set_target_f64_spec`,
//!   `linear_smoother.step_f64_spec`).
//! - **Lands exactly.** After `set_target_f64(state, target, steps)`, a block run on the new state
//!   returns `target` itself, bit for bit, from step number `steps` on, and with `remaining = 0`
//!   a block changes nothing and every value is `state.value`
//!   (`linear_smoother.set_target_process_f64_lands`, `linear_smoother.process_f64_at_rest`).
//!   That the same holds when the ramp is run one `step` at a time or across several blocks, until
//!   the next `set_target`, follows from `linear_smoother.step_f64_spec` and
//!   `linear_smoother.process_f64_spec` with `linear_smoother.process_f64_lands` (no single
//!   theorem states it across blocks).
//! - **Close to the straight line before that.** Step number `k`, for `1 <= k < steps`, returns
//!   `target - step * ((steps - k) as f64)` (`linear_smoother.valueAfter_set_target_f64`). When
//!   `value` and `target` are finite and at most `2^1020` in size (`2^124` in `f32`) and
//!   `1 <= steps <= 2^53` (`2^24` in `f32`), that value is finite and within
//!   `u·|T| + 5u·|T - S| + (2·steps + 4)·η` of the straight line `S + (T - S)·k/steps`
//!   (`linear_smoother.rampValue_f64_error`).
//!
//! **Compared with `gain::ramp_*`.** `gain::ramp_f64` multiplies one block by a ramp that starts
//! and ends within that block, and keeps no state. This smoother keeps its place in its state, so
//! a ramp can last any number of samples, across any number of blocks of any sizes, and ends on
//! the target exactly. It produces the values themselves; to apply them as a gain, multiply the
//! audio by them.
//!
//! Call these through the module, as `linear_smoother::step_f32`.

/// The state of one linear smoother, in `f64`. `StateF64::default()` holds the value 0 and no
/// ramp in progress.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF64 {
    /// The current value: the last one returned by `step_f64`, or the starting value.
    pub value: f64,
    /// The step per sample of the ramp in progress, `(target - start) / steps`.
    pub step: f64,
    /// The number of samples left in the ramp in progress (0 when there is none).
    pub remaining: usize,
    /// The value the ramp ends on.
    pub target: f64,
}

/// The state of one linear smoother, in `f32`. `StateF32::default()` holds the value 0 and no
/// ramp in progress.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF32 {
    /// The current value: the last one returned by `step_f32`, or the starting value.
    pub value: f32,
    /// The step per sample of the ramp in progress, `(target - start) / steps`.
    pub step: f32,
    /// The number of samples left in the ramp in progress (0 when there is none).
    pub remaining: usize,
    /// The value the ramp ends on.
    pub target: f32,
}

/// Starts a ramp, in `f64`, from the current `state.value` to `target` over `steps` samples:
/// sets `state.target = target`, and either, for `steps = 0`, `state.value = target`,
/// `state.step = 0.0` and `state.remaining = 0`, or `state.step = (target - state.value) /
/// (steps as f64)` and `state.remaining = steps` (`linear_smoother.set_target_f64_spec`).
pub fn set_target_f64(state: &mut StateF64, target: f64, steps: usize) {
    state.target = target;
    if steps == 0 {
        state.value = target;
        state.step = 0.0;
        state.remaining = 0;
    } else {
        state.step = (target - state.value) / (steps as f64);
        state.remaining = steps;
    }
}

/// Moves one sample on, in `f64`, and returns the new value. If `state.remaining > 0`, it takes
/// one off `remaining`, then sets `state.value` to `state.target` if `remaining` is now 0, or
/// else to `state.target - state.step * (remaining as f64)`. With `remaining = 0` it changes
/// nothing. Either way it returns `state.value` (`linear_smoother.step_f64_spec`).
#[inline]
pub fn step_f64(state: &mut StateF64) -> f64 {
    if state.remaining > 0 {
        state.remaining -= 1;
        state.value = if state.remaining == 0 {
            state.target
        } else {
            state.target - state.step * (state.remaining as f64)
        };
    }
    state.value
}

/// Fills `buf` with the next `buf.len()` values, in `f64`: sample `i` becomes the value returned
/// by the `i + 1`-th call of [`step_f64`] (`linear_smoother.process_f64_spec`). An empty block
/// leaves `state` unchanged.
pub fn process_f64(state: &mut StateF64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_f64(state);
        i += 1;
    }
}

/// Starts a ramp, in `f32`: the same as [`set_target_f64`]
/// (`linear_smoother.set_target_f32_spec`).
pub fn set_target_f32(state: &mut StateF32, target: f32, steps: usize) {
    state.target = target;
    if steps == 0 {
        state.value = target;
        state.step = 0.0;
        state.remaining = 0;
    } else {
        state.step = (target - state.value) / (steps as f32);
        state.remaining = steps;
    }
}

/// Moves one sample on, in `f32`, and returns the new value: the same as [`step_f64`]
/// (`linear_smoother.step_f32_spec`).
#[inline]
pub fn step_f32(state: &mut StateF32) -> f32 {
    if state.remaining > 0 {
        state.remaining -= 1;
        state.value = if state.remaining == 0 {
            state.target
        } else {
            state.target - state.step * (state.remaining as f32)
        };
    }
    state.value
}

/// Fills `buf` with the next `buf.len()` values, in `f32`: the same as [`process_f64`]
/// (`linear_smoother.process_f32_spec`).
pub fn process_f32(state: &mut StateF32, buf: &mut [f32]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_f32(state);
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! linear_smoother_tests {
        ($name:ident, $t:ty, $state:ident, $set:ident, $step:ident, $process:ident, $tol:expr) => {
            mod $name {
                use super::*;

                #[test]
                fn lands_exactly_on_awkward_targets_and_stays() {
                    for &(start, target, steps) in &[
                        (0.0, 1.0, 3),
                        (0.1, 0.7, 7),
                        (-0.3, 0.2, 1000),
                        (1.0e-3, -2.5, 48_000),
                        (0.123_456_7, 0.123_456_8, 9),
                    ] {
                        let (start, target): ($t, $t) = (start, target);
                        let mut s = $state {
                            value: start,
                            ..Default::default()
                        };
                        $set(&mut s, target, steps);
                        let mut last = start;
                        for _ in 0..steps {
                            last = $step(&mut s);
                        }
                        assert_eq!(last.to_bits(), target.to_bits());
                        for _ in 0..10 {
                            assert_eq!($step(&mut s).to_bits(), target.to_bits());
                        }
                        assert_eq!(s.remaining, 0);
                    }
                }

                #[test]
                fn values_follow_the_straight_line() {
                    let (start, target, steps): ($t, $t, usize) = (0.25, -0.75, 1000);
                    let mut s = $state {
                        value: start,
                        ..Default::default()
                    };
                    $set(&mut s, target, steps);
                    for k in 1..=steps {
                        let v = $step(&mut s) as f64;
                        let line = start as f64
                            + (target as f64 - start as f64) * (k as f64) / (steps as f64);
                        assert!((v - line).abs() <= $tol, "step {k}: {v} vs {line}");
                    }
                }

                #[test]
                fn zero_steps_jumps_at_once() {
                    let mut s = $state {
                        value: 0.5,
                        ..Default::default()
                    };
                    $set(&mut s, 2.0, 0);
                    assert_eq!(s.value, 2.0);
                    assert_eq!(s.remaining, 0);
                    assert_eq!($step(&mut s), 2.0);
                }

                #[test]
                fn new_target_mid_ramp_restarts_from_the_current_value() {
                    let mut s = $state::default();
                    $set(&mut s, 1.0, 4);
                    assert_eq!($step(&mut s), 0.25);
                    assert_eq!($step(&mut s), 0.5);
                    $set(&mut s, 0.0, 2);
                    assert_eq!($step(&mut s), 0.25);
                    assert_eq!($step(&mut s), 0.0);
                    assert_eq!($step(&mut s), 0.0);
                }

                #[test]
                fn blocks_of_any_size_match_one_long_block() {
                    let mut whole: [$t; 23] = [9.0; 23];
                    let mut s1 = $state {
                        value: -1.0,
                        ..Default::default()
                    };
                    $set(&mut s1, 3.0, 17);
                    $process(&mut s1, &mut whole);

                    let mut split: [$t; 23] = [9.0; 23];
                    let mut s2 = $state {
                        value: -1.0,
                        ..Default::default()
                    };
                    $set(&mut s2, 3.0, 17);
                    let (a, rest) = split.split_at_mut(5);
                    let (b, c) = rest.split_at_mut(0);
                    for block in [a, b, c] {
                        $process(&mut s2, block);
                    }
                    assert_eq!(whole, split);
                    assert_eq!(s1, s2);
                    assert_eq!(whole[16], 3.0);
                    assert_eq!(whole[22], 3.0);
                    // An empty block changes nothing.
                    $process(&mut s2, &mut []);
                    assert_eq!(s1, s2);
                }
            }
        };
    }

    linear_smoother_tests!(
        f64_tests,
        f64,
        StateF64,
        set_target_f64,
        step_f64,
        process_f64,
        1e-15
    );
    linear_smoother_tests!(
        f32_tests,
        f32,
        StateF32,
        set_target_f32,
        step_f32,
        process_f32,
        1e-6
    );
}
