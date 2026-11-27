//! Fixed-capacity delay line: each output sample is the input sample from `delay_samples`
//! samples earlier, up to the buffer's limit (exact rules below).
//!
//! The caller owns the storage: a `buffer` of any length `L`, chosen at run time (for example
//! two seconds at the current sample rate), and a write `position`. Both carry the delay line's
//! state from block to block, so pass the same ones every time. Each channel needs its own
//! buffer and position. This module never allocates memory (see the crate documentation; not
//! proved in Lean).
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
//! from the first sample of the next call, with no smoothing (`process_f64_spec`).
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
//! is `process_f64_ok` (and the same names with `f32`), under the assumptions in
//! `proofs/README.md`.
//!
//! **One sample at a time, reading first.** `process` writes each input before reading the
//! delayed sample, so the output cannot feed back into the input it is delayed from. For
//! feedback, use `read` and then `write` on each sample, with the same `buffer` and `position`:
//!
//! 1. `read(buffer, position, delay_samples)` returns `buffer[(p + L - d) mod L]` and changes
//!    nothing (`read_f64_spec`); for `d >= 1` that is the sample written `d` writes ago
//!    (`read_f64_rotate`);
//! 2. the caller computes the sample `x` to store, for example the input plus a fraction of what
//!    `read` returned;
//! 3. `write(buffer, position, x)` stores `x` at `buffer[p]` and moves `position` on by one, back
//!    to 0 when it reaches `L` (`write_f64_spec`).
//!
//! `write` changes `buffer` and `position` exactly as `process` does on a one-sample block, for
//! any delay (`write_f64_eq_process_state`), and with `d >= 1`, `read` then `write` gives the
//! output `process` would give on that sample (`read_write_f64_eq_process`), so the two styles
//! can be mixed on the same delay line. A delay of 0 is the exception: `read` cannot return the
//! sample not yet written, and returns `buffer[p]`, the one `write` then overwrites. Neither
//! panics: with an empty `buffer`, `read` returns `0.0` and `write` does nothing, leaving
//! `position` unchanged (`read_f64_empty_buffer`, `write_f64_empty_buffer`, `read_f64_ok`,
//! `write_f64_ok`, and the same names with `f32`).
//!
//! Call these through the module, as `delay::process_f32` or `delay::read_f64`.

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

/// Reads one sample from the delay line, in `f64`, without writing: returns
/// `buffer[(p + L - d) mod L]`, where `L` is the length of `buffer`, `p = position mod L` and
/// `d = min(delay_samples, L - 1)`, the same clamping as `process_f64` (see the module
/// documentation). With an empty `buffer` it returns `0.0`. It never panics.
///
/// Called before `write_f64` at the same `position`, it returns the sample written `d` writes
/// ago when `d >= 1` (`delay.read_f64_rotate`), and reading and then writing one sample gives
/// the same output, buffer and position as `process_f64` on that one sample
/// (`delay.read_write_f64_eq_process`). A delay of 0 reads `buffer[p]` (`delay.read_f64_spec`),
/// the sample `write_f64` then overwrites (`delay.write_f64_spec`), not the sample being
/// written: so for delays of 1 to `D` samples, use a buffer of `D + 1` samples, as for
/// `process_f64`.
pub fn read_f64(buffer: &[f64], position: usize, delay_samples: usize) -> f64 {
    let len = buffer.len();
    if len == 0 {
        0.0
    } else {
        let d = if delay_samples < len {
            delay_samples
        } else {
            len - 1
        };
        let w = position % len;
        let r = if d <= w { w - d } else { w + (len - d) };
        buffer[r]
    }
}

/// Writes one sample into the delay line, in `f64`: stores `x` at `buffer[position mod L]`,
/// where `L` is the length of `buffer`, and sets `position` to the next index, back to 0 when it
/// reaches `L`, so that afterwards `position < L`. With an empty `buffer` it does nothing:
/// `position` is left unchanged. It never panics. The new `buffer` and `position` are exactly
/// those `process_f64` leaves after a one-sample block holding `x`, whatever its delay
/// (`delay.read_write_f64_eq_process`).
pub fn write_f64(buffer: &mut [f64], position: &mut usize, x: f64) {
    let len = buffer.len();
    if len == 0 {
        return;
    }
    let w = *position % len;
    buffer[w] = x;
    let next = w + 1;
    *position = if next == len { 0 } else { next };
}

/// Reads one sample from the delay line, in `f32`, without writing: the same as `read_f64`
/// (`delay.read_f32_spec`).
pub fn read_f32(buffer: &[f32], position: usize, delay_samples: usize) -> f32 {
    let len = buffer.len();
    if len == 0 {
        0.0
    } else {
        let d = if delay_samples < len {
            delay_samples
        } else {
            len - 1
        };
        let w = position % len;
        let r = if d <= w { w - d } else { w + (len - d) };
        buffer[r]
    }
}

/// Writes one sample into the delay line, in `f32`: the same as `write_f64`
/// (`delay.write_f32_spec`).
pub fn write_f32(buffer: &mut [f32], position: &mut usize, x: f32) {
    let len = buffer.len();
    if len == 0 {
        return;
    }
    let w = *position % len;
    buffer[w] = x;
    let next = w + 1;
    *position = if next == len { 0 } else { next };
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! delay_tests {
        ($name:ident, $t:ty, $process:ident, $read:ident, $write:ident) => {
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

                #[test]
                fn read_then_write_matches_process_for_delays_of_one_or_more() {
                    let mut input: [$t; 13] = [0.0; 13];
                    for (k, x) in input.iter_mut().enumerate() {
                        *x = (k as $t) * 0.5 - 2.0;
                    }
                    // Delays past L - 1 = 4 are clamped to 4 by both.
                    for delay_samples in [1, 2, 3, 4, 5, 100] {
                        let start: [$t; 5] = [7.0, 8.0, 9.0, 10.0, 11.0];

                        let mut want = input;
                        let mut want_buffer = start;
                        let mut want_position = 7; // 7 mod 5 = 2
                        $process(
                            &mut want_buffer,
                            &mut want_position,
                            delay_samples,
                            &mut want,
                        );

                        let mut got = input;
                        let mut buffer = start;
                        let mut position = 7;
                        for y in got.iter_mut() {
                            let x = *y;
                            *y = $read(&buffer, position, delay_samples);
                            $write(&mut buffer, &mut position, x);
                        }

                        assert_eq!(got, want);
                        assert_eq!(buffer, want_buffer);
                        assert_eq!(position, want_position);
                    }
                }

                #[test]
                fn read_returns_the_sample_written_delay_samples_writes_ago() {
                    let mut buffer: [$t; 4] = [0.0; 4];
                    let mut position = 0;
                    for x in [1.0, 2.0, 3.0] {
                        $write(&mut buffer, &mut position, x);
                    }
                    assert_eq!(position, 3);
                    assert_eq!($read(&buffer, position, 1), 3.0);
                    assert_eq!($read(&buffer, position, 2), 2.0);
                    assert_eq!($read(&buffer, position, 3), 1.0);
                    // A delay of 0 reads the sample about to be overwritten (here the initial 0).
                    assert_eq!($read(&buffer, position, 0), 0.0);
                    // Reading writes nothing.
                    assert_eq!(buffer, [1.0, 2.0, 3.0, 0.0]);
                }

                #[test]
                fn write_wraps_position_and_reduces_it_mod_the_length() {
                    let mut buffer: [$t; 3] = [0.0; 3];
                    let mut position = 8; // 8 mod 3 = 2
                    $write(&mut buffer, &mut position, 5.0);
                    assert_eq!(buffer, [0.0, 0.0, 5.0]);
                    assert_eq!(position, 0);
                    $write(&mut buffer, &mut position, 6.0);
                    assert_eq!(buffer, [6.0, 0.0, 5.0]);
                    assert_eq!(position, 1);
                    // A position past the end is read mod L too.
                    assert_eq!($read(&buffer, 4, 1), 6.0);
                }

                #[test]
                fn read_and_write_on_an_empty_buffer() {
                    let mut position = 5;
                    assert_eq!($read(&[], position, 2), 0.0);
                    $write(&mut [], &mut position, 1.0);
                    assert_eq!(position, 5);
                }
            }
        };
    }

    delay_tests!(f64_tests, f64, process_f64, read_f64, write_f64);
    delay_tests!(f32_tests, f32, process_f32, read_f32, write_f32);
}
