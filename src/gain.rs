//! Gain: multiply a sample by a linear gain factor. Call as `gain::apply_f32`.

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
}
