//! One-pole feedback filter: `y[n] = x[n] + a * y[n-1]`.
//!
//! The previous output `y[n-1]` is the filter's state, carried from block to block by the
//! caller. With `0 < a < 1` this is a leaky integrator (a smoother); `|a| < 1` keeps it stable.

/// One sample of the filter, in `f64`: the new output from the input `x` and the previous
/// output `y_prev`.
#[inline]
pub fn step(a: f64, y_prev: f64, x: f64) -> f64 {
    x + a * y_prev
}

/// Filters a block in place, in `f64`, starting from `state` (the previous output) and leaving
/// the last output in `state`.
pub fn process(a: f64, state: &mut f64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = step(a, *state, buf[i]);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

/// One sample of the filter, in `f32`.
#[inline]
pub fn step_f32(a: f32, y_prev: f32, x: f32) -> f32 {
    x + a * y_prev
}

/// Filters a block in place, in `f32`, carrying `state` as [`process`] does.
pub fn process_f32(a: f32, state: &mut f32, buf: &mut [f32]) {
    let mut i = 0;
    while i < buf.len() {
        let y = step_f32(a, *state, buf[i]);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn impulse_response_is_powers_of_a() {
        let mut state = 0.0;
        let mut buf = [1.0, 0.0, 0.0, 0.0];
        process(0.5, &mut state, &mut buf);
        assert_eq!(buf, [1.0, 0.5, 0.25, 0.125]);
        assert_eq!(state, 0.125);
    }

    #[test]
    fn f32_impulse_response_is_powers_of_a() {
        let mut state = 0.0f32;
        let mut buf = [1.0f32, 0.0, 0.0, 0.0];
        process_f32(0.5, &mut state, &mut buf);
        assert_eq!(buf, [1.0, 0.5, 0.25, 0.125]);
        assert_eq!(state, 0.125);
    }

    #[test]
    fn state_carries_across_blocks() {
        let mut whole = [1.0, 2.0, 3.0, 4.0, 5.0];
        let mut s1 = 0.25;
        process(0.75, &mut s1, &mut whole);

        let mut split = [1.0, 2.0, 3.0, 4.0, 5.0];
        let mut s2 = 0.25;
        let (first, second) = split.split_at_mut(2);
        process(0.75, &mut s2, first);
        process(0.75, &mut s2, second);

        assert_eq!(whole, split);
        assert_eq!(s1, s2);
    }

    #[test]
    fn empty_block_leaves_state_alone() {
        let mut state = 0.3f32;
        process_f32(0.9, &mut state, &mut []);
        assert_eq!(state, 0.3);
    }

    #[test]
    fn process_matches_step() {
        let a = 0.9;
        let input = [0.1, -0.2, 0.3, 1.0, -1.0];
        let mut buf = input;
        let mut state = -0.5;
        process(a, &mut state, &mut buf);
        let mut y = -0.5;
        for (out, x) in buf.iter().zip(input) {
            y = step(a, y, x);
            assert_eq!(*out, y);
        }
    }
}
