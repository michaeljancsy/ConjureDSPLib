//! Gain: multiply samples by a linear gain factor, either one fixed factor (`gain::apply_f32`)
//! or a factor that moves in a straight line across a block (`gain::ramp_f32`).

/// One sample multiplied by a linear gain factor, in `f64`.
#[inline]
pub fn apply_f64(gain: f64, x: f64) -> f64 {
    gain * x
}

/// One sample multiplied by a linear gain factor, in `f32`.
#[inline]
pub fn apply_f32(gain: f32, x: f32) -> f32 {
    gain * x
}

/// Multiplies `buf` in place by a gain that moves in a straight line from `start` toward `end`,
/// in `f64`.
///
/// With `n = buf.len()`: an empty block is left unchanged. Otherwise `step = (end - start) / n`
/// is computed once, and sample `i` (for `i` from 0 to `n - 1`) becomes
/// `buf[i] * (start + step * (i as f64))`, each operation rounded in `f64` in that order. When
/// `start` and `end` are finite and neither `end - start` nor `step` overflows, the gain is
/// exactly `start` at the first sample and `start + step * (n - 1)` (about `end - step`) at the
/// last: `end` itself is not reached in this block. A following block that starts at `end` takes
/// one ordinary step from about `end - step` to exactly `end`, whatever its own length or target.
/// If either end is not finite, or `end - start` overflows, the gains are infinite or NaN (the
/// first sample's included).
///
/// The gain is recomputed from the index for every sample, not built up by adding `step`
/// repeatedly, so each gain carries the same few roundings (subtract, divide, cast, multiply, add)
/// wherever it is in the block. `i as f64` and `n as f64` are exact for every value up to `2^53`
/// (9,007,199,254,740,992); above that some values may be rounded to the nearest `f64`, and the gain is computed
/// from the rounded values.
pub fn ramp_f64(start: f64, end: f64, buf: &mut [f64]) {
    let n = buf.len();
    if n == 0 {
        return;
    }
    let step = (end - start) / (n as f64);
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] *= start + step * (i as f64);
        i += 1;
    }
}

/// Multiplies `buf` in place by a gain that moves in a straight line from `start` toward `end`,
/// in `f32`.
///
/// With `n = buf.len()`: an empty block is left unchanged. Otherwise `step = (end - start) / n`
/// is computed once, and sample `i` (for `i` from 0 to `n - 1`) becomes
/// `buf[i] * (start + step * (i as f32))`, each operation rounded in `f32` in that order. When
/// `start` and `end` are finite and neither `end - start` nor `step` overflows, the gain is
/// exactly `start` at the first sample and `start + step * (n - 1)` (about `end - step`) at the
/// last: `end` itself is not reached in this block. A following block that starts at `end` takes
/// one ordinary step from about `end - step` to exactly `end`, whatever its own length or target.
/// If either end is not finite, or `end - start` overflows, the gains are infinite or NaN (the
/// first sample's included).
///
/// The gain is recomputed from the index for every sample, not built up by adding `step`
/// repeatedly, so each gain carries the same few roundings (subtract, divide, cast, multiply, add)
/// wherever it is in the block. `i as f32` and `n as f32` are exact for every value up to `2^24`
/// (16,777,216); above that some values may be rounded to the nearest `f32`, and the gain is computed
/// from the rounded values.
pub fn ramp_f32(start: f32, end: f32, buf: &mut [f32]) {
    let n = buf.len();
    if n == 0 {
        return;
    }
    let step = (end - start) / (n as f32);
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] *= start + step * (i as f32);
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unity_gain_leaves_sample_unchanged() {
        assert_eq!(apply_f64(1.0, 0.25), 0.25);
        assert_eq!(apply_f32(1.0, 0.25), 0.25);
    }

    #[test]
    fn half_gain_halves_sample() {
        assert_eq!(apply_f64(0.5, -0.5), -0.25);
        assert_eq!(apply_f32(0.5, -0.5), -0.25);
    }

    /// The same ramp tests for both precisions.
    macro_rules! ramp_tests {
        ($name:ident, $t:ty, $ramp:ident) => {
            mod $name {
                use super::*;

                #[test]
                fn empty_block_is_unchanged() {
                    let mut buf: [$t; 0] = [];
                    $ramp(0.0, 1.0, &mut buf);
                    assert_eq!(buf, []);
                }

                #[test]
                fn exact_ramps_up_and_down() {
                    // Exact in binary: step = 1 / 4.
                    let mut buf: [$t; 4] = [1.0; 4];
                    $ramp(0.0, 1.0, &mut buf);
                    assert_eq!(buf, [0.0, 0.25, 0.5, 0.75]);

                    let mut buf: [$t; 4] = [2.0, -2.0, 4.0, 0.5];
                    $ramp(1.0, 0.0, &mut buf);
                    assert_eq!(buf, [2.0, -1.5, 2.0, 0.125]);
                }

                #[test]
                fn equal_ends_are_a_fixed_gain() {
                    let input: [$t; 5] = [0.1, -0.2, 0.3, 1.0, -1.0];
                    let mut buf = input;
                    $ramp(0.7, 0.7, &mut buf);
                    for (out, x) in buf.iter().zip(input) {
                        assert_eq!(*out, x * 0.7);
                    }
                }

                #[test]
                fn consecutive_blocks_continue_the_ramp() {
                    // Two blocks 0 -> 0.5 and 0.5 -> 1 of 4 samples each equal one block 0 -> 1
                    // of 8 samples (all values exact in binary).
                    let mut whole: [$t; 8] = [1.0; 8];
                    $ramp(0.0, 1.0, &mut whole);
                    let mut split: [$t; 8] = [1.0; 8];
                    let (first, second) = split.split_at_mut(4);
                    $ramp(0.0, 0.5, first);
                    $ramp(0.5, 1.0, second);
                    assert_eq!(whole, split);
                    assert_eq!(whole, [0.0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875]);

                    // In general: the gain steps by `step` across the boundary, as inside a
                    // block, and the second block starts exactly at the first block's `end`.
                    let mut a: [$t; 3] = [1.0; 3];
                    let mut b: [$t; 3] = [1.0; 3];
                    $ramp(0.2, 0.5, &mut a);
                    $ramp(0.5, 0.8, &mut b);
                    assert_eq!(b[0], 0.5);
                    let step: $t = (0.5 - 0.2) / 3.0;
                    assert!((b[0] - a[2] - step).abs() <= 4.0 * <$t>::EPSILON);
                }

                #[test]
                fn matches_the_formula_bit_for_bit() {
                    let (start, end): ($t, $t) = (0.3, -1.7);
                    let input: [$t; 7] = [0.1, -0.2, 0.3, 1.0, -1.0, 0.123, 9.5];
                    let mut buf = input;
                    $ramp(start, end, &mut buf);
                    let step = (end - start) / (input.len() as $t);
                    for (i, (out, x)) in buf.iter().zip(input).enumerate() {
                        let gain = start + step * (i as $t);
                        assert_eq!(out.to_bits(), (x * gain).to_bits());
                    }
                }
            }
        };
    }

    ramp_tests!(ramp_f64_tests, f64, ramp_f64);
    ramp_tests!(ramp_f32_tests, f32, ramp_f32);
}
