//! Shared DSP maths for ConjureDSP plug-ins.
//!
//! Functions here take numbers and buffers and return numbers or fill buffers. Per-sample code
//! does no memory allocation, takes no locks and makes no system calls. The crate is `no_std`
//! and does not use `alloc`, so it cannot allocate memory at all. These are properties of the
//! code and its build, which the compiler enforces; they are not proved in Lean, and they rely on
//! `libm` doing the same. The crate's one dependency is `libm` (pinned exactly, default features
//! off), for `tan`, `pow` and `sqrt` in filter design.
//!
//! The code is written so that Aeneas can translate it to Lean (see `proofs/`): plain loops with
//! an index rather than iterators, and no trait objects or closures in proved functions.
//!
//! Naming: each function comes in `_f32` and `_f64` versions, and is called through its module,
//! which names the algorithm: `gain::apply_f32`, `one_pole::process_f64`. Function names inside a
//! module are short (`step`, `process`, `apply`) and repeat across modules.
//! Types carry the precision as a capitalized suffix: `biquad::CoeffsF32`.

#![no_std]

pub mod biquad;
pub mod delay;
pub mod gain;
pub mod one_pole;
pub mod smoother;
pub mod svf;
