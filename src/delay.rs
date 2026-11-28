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
//! At the end, `position` is set to `p`. The delay is a whole number of samples: `process` does
//! no interpolation between samples (for that, see `read_interp` below). The longest delay is `L - 1` samples, so for delays of up to
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
//!    nothing (`read_f64_spec`); for `d >= 1` that is element `L - d` of the buffer read oldest
//!    first from `position` (`read_f64_rotate`), the sample written `d` writes ago (worked out
//!    outside Lean, not proved: it also needs `write_f64_rotate` and at least `d` earlier
//!    writes);
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
//! **Reading between samples.** `read_interp(buffer, position, delay)` reads at a delay that need
//! not be a whole number, by four-point cubic Lagrange interpolation over the same `buffer` and
//! `position`, and writes nothing; it is used like `read`, before `write`. The delay is clamped to
//! the range from 2 to `L - 2` samples, and a buffer shorter than 5 samples gives `0.0` (exact
//! rules in its documentation). It never panics (`read_interp_f64_ok`), and at a whole-number
//! delay it returns the sample `read` returns, in value (`read_interp_f64_whole_eq_read`).
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
/// When `d >= 1`, it returns element `L - d` of the buffer read oldest first from `position`
/// (`delay.read_f64_rotate`), which, called before `write_f64` at the same `position`, is the
/// sample written `d` writes ago (worked out outside Lean, not proved: it also needs
/// `delay.write_f64_rotate` and at least `d` earlier writes). When `d >= 1`, reading and then
/// writing one sample gives the same output, buffer and position as `process_f64` on that one
/// sample (`delay.read_write_f64_eq_process`). A delay of 0 reads `buffer[p]`
/// (`delay.read_f64_spec`), the sample `write_f64` then overwrites (`delay.write_f64_spec`), not
/// the sample being written: so for delays of 1 to `D` samples, use a buffer of `D + 1` samples,
/// as for `process_f64`.
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
/// (`delay.write_f64_eq_process_state`).
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

/// Reads the delay line between samples, in `f64`, without writing: four-point cubic Lagrange
/// interpolation at a delay of `delay` samples, which need not be a whole number. It uses the same
/// `buffer` and `position` as [`read_f64`] and [`write_f64`], and reads only.
///
/// With `L` the length of `buffer`:
///
/// - If `L < 5` it returns `0.0`.
/// - `whole = delay as usize`: Rust's conversion, which rounds toward zero, gives 0 for a NaN or
///   a negative `delay` and saturates at `usize::MAX`.
/// - Then the sample index `n` and the fraction `t` are `n = 2`, `t = 0.0` if `whole < 2`;
///   `n = L - 3`, `t = 1.0` if `whole > L - 3`; and otherwise `n = whole` and
///   `t = delay - (whole as f64)`.
/// - The four samples are those [`read_f64`] returns at delays `n - 1`, `n`, `n + 1` and `n + 2`:
///   `xm1`, `x0`, `x1` and `x2`.
/// - With `tp1 = t + 1`, `tm1 = t - 1` and `tm2 = t - 2`, the weights are
///   `wm1 = -(t * tm1 * tm2) / 6`, `w0 = tp1 * tm1 * tm2 * 0.5`, `w1 = -(tp1 * t * tm2) * 0.5` and
///   `w2 = tp1 * t * tm1 / 6`, each product taken left to right, and the result is
///   `((wm1 * xm1 + w0 * x0) + w1 * x1) + w2 * x2`, every operation rounded in `f64` in that
///   order.
///
/// So the delay is clamped to the range from 2 to `L - 2` samples: a shorter delay, a NaN or a
/// negative one reads at 2 samples, and a longer one, or `+∞`, at `L - 2`. For delays of up to `D`
/// samples, use a buffer of at least `D + 2` samples (and at least 5). Called before
/// `write_f64` at the same `position`, the sample at delay `k >= 1` is the one written `k` writes
/// ago (worked out outside Lean, not proved; see [`read_f64`]).
///
/// It never panics, for any arguments (`delay.read_interp_f64_ok`); what it computes is
/// `delay.read_interp_f64_spec`. When `delay` is finite and `L <= 2^53`, `t` is the fractional
/// part of the clamped delay, between 0 and 1 (`delay.read_interp_f64_frac`). In exact
/// arithmetic, for `0 <= t <= 1`, the weights are the cubic Lagrange polynomials through the four
/// samples placed at `-1`, `0`, `1` and `2`, read at `t` (worked out outside Lean, not proved).
/// At a whole-number delay `d` from 2 to `L - 2`, with `L <= 2^53` and the buffer's samples
/// finite, it returns a value equal to the sample `read_f64` returns at delay `d`
/// (`delay.read_interp_f64_whole`, `delay.read_interp_f64_whole_eq_read`; equal in value, so a
/// zero may come back with the other sign). In exact arithmetic, for `0 <= t <= 1` and samples
/// at most `M` in size, the formula is at most `1.25·M` in size (`delay.lagrange4_real_abs_le`);
/// a bound on the rounded result is not proved.
pub fn read_interp_f64(buffer: &[f64], position: usize, delay: f64) -> f64 {
    let len = buffer.len();
    if len < 5 {
        return 0.0;
    }
    // `as` rounds toward zero, sends NaN to 0 and saturates at the largest `usize`, so for any
    // delay from 0 up, `whole` is its whole number of samples.
    let whole = delay as usize;
    let (n, t) = if whole < 2 {
        (2, 0.0)
    } else if whole > len - 3 {
        (len - 3, 1.0)
    } else {
        (whole, delay - whole as f64)
    };
    // The index of the sample at delay `n + 2`, then one newer sample at a time.
    let w = position % len;
    let k = n + 2;
    let mut r = if k <= w { w - k } else { w + (len - k) };
    let x2 = buffer[r];
    r = if r + 1 == len { 0 } else { r + 1 };
    let x1 = buffer[r];
    r = if r + 1 == len { 0 } else { r + 1 };
    let x0 = buffer[r];
    r = if r + 1 == len { 0 } else { r + 1 };
    let xm1 = buffer[r];
    let tp1 = t + 1.0;
    let tm1 = t - 1.0;
    let tm2 = t - 2.0;
    let wm1 = -(t * tm1 * tm2) / 6.0;
    let w0 = tp1 * tm1 * tm2 * 0.5;
    let w1 = -(tp1 * t * tm2) * 0.5;
    let w2 = tp1 * t * tm1 / 6.0;
    wm1 * xm1 + w0 * x0 + w1 * x1 + w2 * x2
}

/// Reads the delay line between samples, in `f32`: the same as [`read_interp_f64`], in `f32`
/// (`delay.read_interp_f32_spec`). Its theorems about the fraction and whole-number delays
/// (`delay.read_interp_f32_frac`, `delay.read_interp_f32_whole`) need `L <= 2^24` in place of
/// `L <= 2^53`.
pub fn read_interp_f32(buffer: &[f32], position: usize, delay: f32) -> f32 {
    let len = buffer.len();
    if len < 5 {
        return 0.0;
    }
    // `as` rounds toward zero, sends NaN to 0 and saturates at the largest `usize`, so for any
    // delay from 0 up, `whole` is its whole number of samples.
    let whole = delay as usize;
    let (n, t) = if whole < 2 {
        (2, 0.0)
    } else if whole > len - 3 {
        (len - 3, 1.0)
    } else {
        (whole, delay - whole as f32)
    };
    // The index of the sample at delay `n + 2`, then one newer sample at a time.
    let w = position % len;
    let k = n + 2;
    let mut r = if k <= w { w - k } else { w + (len - k) };
    let x2 = buffer[r];
    r = if r + 1 == len { 0 } else { r + 1 };
    let x1 = buffer[r];
    r = if r + 1 == len { 0 } else { r + 1 };
    let x0 = buffer[r];
    r = if r + 1 == len { 0 } else { r + 1 };
    let xm1 = buffer[r];
    let tp1 = t + 1.0;
    let tm1 = t - 1.0;
    let tm2 = t - 2.0;
    let wm1 = -(t * tm1 * tm2) / 6.0;
    let w0 = tp1 * tm1 * tm2 * 0.5;
    let w1 = -(tp1 * t * tm2) * 0.5;
    let w2 = tp1 * t * tm1 / 6.0;
    wm1 * xm1 + w0 * x0 + w1 * x1 + w2 * x2
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! delay_tests {
        ($name:ident, $t:ty, $process:ident, $read:ident, $write:ident, $read_interp:ident) => {
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
                fn interpolated_read_at_whole_delays_matches_read() {
                    let mut buffer: [$t; 11] = [0.0; 11];
                    let mut position = 0;
                    for k in 0..27 {
                        $write(&mut buffer, &mut position, (k as $t) * 0.37 - 3.0);
                        // Delays 2 to L - 2 = 9.
                        for d in 2..=9 {
                            let want = $read(&buffer, position, d);
                            let got = $read_interp(&buffer, position, d as $t);
                            assert_eq!(got, want, "delay {d} at position {position}");
                        }
                    }
                }

                #[test]
                fn interpolated_read_follows_a_cubic() {
                    // Write x(k) = cubic in k; cubic Lagrange reproduces it up to rounding.
                    let f = |k: f64| 0.001 * k * k * k - 0.02 * k * k + 0.3 * k - 1.0;
                    let mut buffer: [$t; 16] = [0.0; 16];
                    let mut position = 5;
                    for k in 0..40 {
                        $write(&mut buffer, &mut position, f(k as f64) as $t);
                    }
                    // The last write was k = 39, so delay j (j >= 1) holds x(40 - j).
                    for step in 0..=120 {
                        let d = 2.0 + (step as f64) * 0.1;
                        let got = $read_interp(&buffer, position, d as $t) as f64;
                        let want = f(40.0 - d);
                        assert!((got - want).abs() < 1e-4, "delay {d}: {got} vs {want}");
                    }
                }

                #[test]
                fn interpolated_read_clamps_and_never_panics() {
                    let buffer: [$t; 8] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
                    let position = 3;
                    let lo = $read(&buffer, position, 2);
                    let hi = $read(&buffer, position, 6);
                    for d in [-1.0, 0.0, 1.5, 2.0, <$t>::NAN, <$t>::NEG_INFINITY, -0.0] {
                        assert_eq!($read_interp(&buffer, position, d), lo, "delay {d}");
                    }
                    for d in [6.0, 6.5, 1.0e30, <$t>::INFINITY] {
                        assert_eq!($read_interp(&buffer, position, d), hi, "delay {d}");
                    }
                    // Positions past the end are reduced mod L, as for read.
                    assert_eq!(
                        $read_interp(&buffer, position + 8 * 3, 3.25),
                        $read_interp(&buffer, position, 3.25)
                    );
                    // Too short: 0.
                    for len in 0..5 {
                        assert_eq!($read_interp(&buffer[..len], 2, 2.5), 0.0);
                    }
                    // Size bound (exact arithmetic gives at most 1.25 times the largest sample).
                    let ones: [$t; 8] = [1.0, -1.0, 1.0, -1.0, 1.0, -1.0, 1.0, -1.0];
                    for step in 0..=40 {
                        let d = 2.0 + (step as $t) * 0.1;
                        assert!($read_interp(&ones, 0, d).abs() <= 1.2501);
                    }
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

    delay_tests!(
        f64_tests,
        f64,
        process_f64,
        read_f64,
        write_f64,
        read_interp_f64
    );
    delay_tests!(
        f32_tests,
        f32,
        process_f32,
        read_f32,
        write_f32,
        read_interp_f32
    );
}
