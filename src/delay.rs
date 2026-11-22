//! Fixed-capacity delay line: each output sample is the input sample from `delay_samples`
//! samples earlier.
//!
//! The caller owns the storage: a `buffer` of any length `L`, chosen at run time (for example
//! two seconds at the current sample rate), and a write `position`. Both carry the delay line's
//! state from block to block, so pass the same ones every time. Each channel needs its own
//! buffer and position. This module never allocates memory.
//!
//! Write `L` for the length of `buffer`, `d = min(delay_samples, L - 1)` for the delay used and
//! `p = position mod L` for the write index. For each sample `x` of `audio`, in order, `process`
//! does three things:
//!
//! 1. writes `x` at `buffer[p]`;
//! 2. replaces `x` with `buffer[(p + L - d) mod L]`, the sample written `d` samples earlier (so a
//!    delay of 0 returns `x` itself);
//! 3. moves `p` on by one, back to 0 when it reaches `L`.
//!
//! At the end, `position` is set to `p`. The delay is a whole number of samples: there is no
//! interpolation between samples. The longest delay is `L - 1` samples, so for delays of up to
//! `D` samples, use a buffer of `D + 1` samples.
//!
//! Calling `process` on one block and then on the next, with the same `buffer`, `position` and
//! `delay_samples`, gives the same outputs, `buffer` and `position` as one call on the two blocks
//! joined. Before the first block, fill `buffer` with zeros (silence): then the first
//! `min(delay_samples, L - 1)` outputs of the first call are 0 (all of them, if `audio` is
//! shorter).
//!
//! `delay_samples` may change between calls. The new `buffer` and `position` do not depend on it
//! (`process_f64_state_indep`), so the stored history is kept, and the new delay takes effect
//! from the first sample of the next call, with no smoothing.
//!
//! `process` never panics, whatever its arguments:
//!
//! - an empty `buffer` (`L = 0`) can store nothing, so it behaves as a delay of 0: `audio` passes
//!   through unchanged, and `position` is left unchanged;
//! - a `delay_samples` larger than `L - 1` is treated as `L - 1`;
//! - a `position` of `L` or more is first replaced by `position mod L` (so after a call with a
//!   non-empty `buffer`, `position` is always less than `L`).
//!
//! What `process` computes is proved in Lean (`proofs/README.md`): the steps above are
//! `process_f64_spec`, joining blocks is `process_f64_append`, the zeros are
//! `process_f64_zero_prefix`, the empty buffer is `process_f64_empty_buffer` and never panicking
//! is `process_f64_ok` (and the same names with `f32`).
//!
//! Call these through the module, as `delay::process_f32`.

/// Delays `audio` in place by `delay_samples` samples, in `f64`, using `buffer` and `position`
/// as the delay line's state (see the module documentation for the exact steps and limits).
pub fn process_f64(
    buffer: &mut [f64],
    position: &mut usize,
    delay_samples: usize,
    audio: &mut [f64],
) {
    let len = buffer.len();
    if len == 0 {
        return;
    }
    let d = if delay_samples < len {
        delay_samples
    } else {
        len - 1
    };
    // The write index, and the read index `(w + len - d) mod len`, each moved on by one per
    // sample with a compare and wrap rather than `%`.
    let mut w = *position % len;
    let mut r = if d <= w { w - d } else { w + (len - d) };
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < audio.len() {
        buffer[w] = audio[i];
        audio[i] = buffer[r];
        w += 1;
        if w == len {
            w = 0;
        }
        r += 1;
        if r == len {
            r = 0;
        }
        i += 1;
    }
    *position = w;
}

/// Delays `audio` in place by `delay_samples` samples, in `f32`, using `buffer` and `position`
/// as the delay line's state (see the module documentation for the exact steps and limits).
pub fn process_f32(
    buffer: &mut [f32],
    position: &mut usize,
    delay_samples: usize,
    audio: &mut [f32],
) {
    let len = buffer.len();
    if len == 0 {
        return;
    }
    let d = if delay_samples < len {
        delay_samples
    } else {
        len - 1
    };
    // The write index, and the read index `(w + len - d) mod len`, each moved on by one per
    // sample with a compare and wrap rather than `%`.
    let mut w = *position % len;
    let mut r = if d <= w { w - d } else { w + (len - d) };
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < audio.len() {
        buffer[w] = audio[i];
        audio[i] = buffer[r];
        w += 1;
        if w == len {
            w = 0;
        }
        r += 1;
        if r == len {
            r = 0;
        }
        i += 1;
    }
    *position = w;
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! delay_tests {
        ($name:ident, $t:ty, $process:ident) => {
            mod $name {
                use super::*;

                #[test]
                fn delay_zero_passes_through() {
                    let input: [$t; 5] = [0.5, -1.0, 2.0, 0.25, 3.0];
                    let mut audio = input;
                    let mut buffer: [$t; 4] = [0.0; 4];
                    let mut position = 0;
                    $process(&mut buffer, &mut position, 0, &mut audio);
                    assert_eq!(audio, input);
                    assert_eq!(position, 1);
                }

                #[test]
                fn impulse_comes_out_delay_samples_later() {
                    let mut audio: [$t; 6] = [1.0, 0.0, 0.0, 0.0, 0.0, 0.0];
                    let mut buffer: [$t; 8] = [0.0; 8];
                    let mut position = 0;
                    $process(&mut buffer, &mut position, 3, &mut audio);
                    assert_eq!(audio, [0.0, 0.0, 0.0, 1.0, 0.0, 0.0]);
                    assert_eq!(position, 6);
                }

                #[test]
                fn blocks_of_different_sizes_match_one_long_block() {
                    let mut input: [$t; 23] = [0.0; 23];
                    for (k, x) in input.iter_mut().enumerate() {
                        *x = (k as $t) + 1.0;
                    }
                    let mut whole = input;
                    let mut whole_buffer: [$t; 7] = [0.0; 7];
                    let mut whole_position = 0;
                    $process(&mut whole_buffer, &mut whole_position, 5, &mut whole);

                    let mut split = input;
                    let mut split_buffer: [$t; 7] = [0.0; 7];
                    let mut split_position = 0;
                    let (a, rest) = split.split_at_mut(1);
                    let (b, rest) = rest.split_at_mut(9);
                    let (c, d) = rest.split_at_mut(0);
                    for block in [a, b, c, d] {
                        $process(&mut split_buffer, &mut split_position, 5, block);
                    }

                    assert_eq!(whole, split);
                    assert_eq!(whole_buffer, split_buffer);
                    assert_eq!(whole_position, split_position);
                    // The sample written 5 samples earlier, or 0 before the start.
                    for (k, y) in whole.iter().enumerate() {
                        let expected = if k >= 5 { input[k - 5] } else { 0.0 };
                        assert_eq!(*y, expected);
                    }
                }

                #[test]
                fn reads_and_writes_wrap_around_the_buffer_end() {
                    // Start near the end, so both indices wrap during the block.
                    let mut buffer: [$t; 4] = [10.0, 11.0, 12.0, 13.0];
                    let mut position = 2;
                    let mut audio: [$t; 6] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
                    $process(&mut buffer, &mut position, 3, &mut audio);
                    // The history before the block, oldest first, is 12, 13, 10, 11.
                    assert_eq!(audio, [13.0, 10.0, 11.0, 1.0, 2.0, 3.0]);
                    assert_eq!(position, 0);
                    assert_eq!(buffer, [3.0, 4.0, 5.0, 6.0]);
                }

                #[test]
                fn too_large_delay_is_clamped_and_position_wrapped() {
                    let input: [$t; 5] = [1.0, 2.0, 3.0, 4.0, 5.0];

                    let mut audio = input;
                    let mut buffer: [$t; 3] = [7.0, 8.0, 9.0];
                    let mut position = 7; // 7 mod 3 = 1
                    $process(&mut buffer, &mut position, 100, &mut audio);

                    let mut want = input;
                    let mut want_buffer: [$t; 3] = [7.0, 8.0, 9.0];
                    let mut want_position = 1;
                    $process(&mut want_buffer, &mut want_position, 2, &mut want);

                    assert_eq!(audio, want);
                    assert_eq!(buffer, want_buffer);
                    assert_eq!(position, want_position);
                    // History 8, 9, 7, then the input; a delay of 2.
                    assert_eq!(audio, [9.0, 7.0, 1.0, 2.0, 3.0]);
                }

                #[test]
                fn delay_equal_to_buffer_length_is_clamped() {
                    // L = 4, so a delay of 4 is treated as 3.
                    let mut buffer: [$t; 4] = [10.0, 11.0, 12.0, 13.0];
                    let mut position = 0;
                    let mut audio: [$t; 5] = [1.0, 2.0, 3.0, 4.0, 5.0];
                    $process(&mut buffer, &mut position, 4, &mut audio);
                    // History 10, 11, 12, 13, then the input; a delay of 3.
                    assert_eq!(audio, [11.0, 12.0, 13.0, 1.0, 2.0]);
                    assert_eq!(position, 1);
                    assert_eq!(buffer, [5.0, 2.0, 3.0, 4.0]);
                }

                #[test]
                fn read_behind_write_without_wrapping() {
                    // Position 5 and delay 2: reads start at index 3 and stay below the end.
                    let mut buffer: [$t; 8] = [10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0];
                    let mut position = 5;
                    let mut audio: [$t; 3] = [1.0, 2.0, 3.0];
                    $process(&mut buffer, &mut position, 2, &mut audio);
                    assert_eq!(audio, [13.0, 14.0, 1.0]);
                    assert_eq!(position, 0);
                    assert_eq!(buffer, [10.0, 11.0, 12.0, 13.0, 14.0, 1.0, 2.0, 3.0]);
                }

                #[test]
                fn one_sample_buffer_passes_audio_through() {
                    // L = 1: every delay is treated as 0.
                    for delay_samples in [0, 1, 5] {
                        let input: [$t; 3] = [1.0, -2.0, 3.0];
                        let mut audio = input;
                        let mut buffer: [$t; 1] = [7.0];
                        let mut position = 0;
                        $process(&mut buffer, &mut position, delay_samples, &mut audio);
                        assert_eq!(audio, input);
                        assert_eq!(position, 0);
                        assert_eq!(buffer, [3.0]);
                    }
                }

                #[test]
                fn empty_buffer_leaves_audio_unchanged() {
                    let input: [$t; 3] = [1.0, -2.0, 3.0];
                    let mut audio = input;
                    let mut position = 5;
                    $process(&mut [], &mut position, 2, &mut audio);
                    assert_eq!(audio, input);
                    assert_eq!(position, 5);
                }

                #[test]
                fn empty_audio_leaves_state_unchanged() {
                    let mut buffer: [$t; 3] = [1.0, 2.0, 3.0];
                    let mut position = 2;
                    $process(&mut buffer, &mut position, 1, &mut []);
                    assert_eq!(buffer, [1.0, 2.0, 3.0]);
                    assert_eq!(position, 2);
                }
            }
        };
    }

    delay_tests!(f64_tests, f64, process_f64);
    delay_tests!(f32_tests, f32, process_f32);
}
