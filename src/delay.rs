//! Fixed-capacity delay line: each output sample is the input sample from `delay_samples`
//! samples earlier.
//!
//! The caller owns the storage: a `buffer` of any length `L`, chosen at run time (for example
//! two seconds at the current sample rate), and a write `position`. Both carry the delay line's
//! state from block to block, so pass the same ones every time. Each channel needs its own
//! buffer and position. This module never allocates memory.
//!
//! For each sample `x` of `audio`, in order, `process` does three things:
//!
//! 1. writes `x` at `buffer[position]`;
//! 2. replaces `x` with `buffer[(position + L - delay_samples) mod L]`, the sample written
//!    `delay_samples` samples earlier (so a delay of 0 returns `x` itself);
//! 3. moves `position` on by one, back to 0 when it reaches `L`.
//!
//! The longest delay is `L - 1` samples. Before the first block, fill `buffer` with zeros
//! (silence): then the first `delay_samples` outputs are 0.
//!
//! `process` never panics, whatever its arguments:
//!
//! - an empty `buffer` (`L = 0`) can store nothing, so `audio` and `position` are left unchanged;
//! - a `delay_samples` larger than `L - 1` is treated as `L - 1`;
//! - a `position` of `L` or more is first replaced by `position mod L` (so after a call with a
//!   non-empty `buffer`, `position` is always less than `L`).
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
                fn too_large_delay_and_position_are_clamped() {
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
