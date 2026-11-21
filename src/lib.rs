//! Shared DSP maths for ConjureDSP plug-ins.
//!
//! Functions here take numbers and buffers and return numbers or fill buffers. Per-sample code
//! does no memory allocation, takes no locks and makes no system calls. The crate is `no_std`
//! and has no dependencies.
//!
//! The code is written so that Aeneas can translate it to Lean (see `proofs/`): plain loops with
//! an index rather than iterators, and no trait objects or closures in proved functions.

#![no_std]
#![forbid(unsafe_code)]
#![warn(missing_docs)]

pub mod gain;
