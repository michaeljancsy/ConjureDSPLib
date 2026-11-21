//! Shared DSP maths for ConjureDSP plug-ins.
//!
//! Functions here take numbers and buffers and return numbers or fill buffers. Per-sample code
//! does no memory allocation, takes no locks and makes no system calls. The crate is `no_std`
//! and has no dependencies; without `alloc` it cannot allocate memory at all.
//!
//! The code is written so that Aeneas can translate it to Lean (see `proofs/`): plain loops with
//! an index rather than iterators, and no trait objects or closures in proved functions.
//!
//! Each function comes in `_f32` and `_f64` versions, named that way so both read alike.

#![no_std]

pub mod gain;
pub mod one_pole;
