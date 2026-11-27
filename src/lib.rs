//! Audio DSP building blocks with Lean proofs about the code.
//!
//! Functions here take numbers and buffers and return numbers or fill buffers. Per-sample code
//! does no memory allocation, takes no locks and makes no system calls. Allocation and system
//! calls are ruled out by the build together with one property of the code: the crate is `no_std`
//! and has no `extern crate alloc` or `extern crate std` (the compiler does not forbid adding
//! them), so it links no allocator and no operating-system interface; and it forbids `unsafe` code
//! (`unsafe_code = "forbid"` in `Cargo.toml`), so it cannot call foreign code or use inline
//! assembly; `libm` is relied on to do the same. That it takes no locks is a property of the code
//! (it uses no atomics or other synchronization); the compiler does not enforce it. A panic would
//! run the program's panic handler, which can allocate, lock and make system calls; that the
//! functions never panic is proved of the translated code (`proofs/README.md`). None of this is
//! otherwise proved in Lean. The crate's one dependency is `libm` (pinned exactly, default
//! features off), for `tan`, `pow` and `sqrt` in filter design.
//!
//! The optional `std` feature adds fused multiply-add versions of the one-pole, biquad and SVF
//! (`step_fma_f64`, `process_fma_f64` and the `f32` ones), which call `f64::mul_add` and
//! `f32::mul_add`; those are in `std`, not `core`, on stable Rust. With it on, the crate is not
//! `no_std` and links the standard library, so the build no longer rules out allocation and system
//! calls as above; the functions themselves are unchanged.
//!
//! The code is written so that Aeneas can translate it to Lean (see `proofs/`): plain loops with
//! an index rather than iterators, and no trait objects or closures in proved functions.
//!
//! Naming: each function comes in `_f32` and `_f64` versions, and is called through its module,
//! which names the algorithm: `gain::apply_f32`, `one_pole::process_f64`. Function names inside a
//! module are short (`step`, `process`, `apply`) and repeat across modules.
//! Types carry the precision as a capitalized suffix: `biquad::CoeffsF32`.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod biquad;
pub mod delay;
pub mod gain;
pub mod one_pole;
pub mod smoother;
pub mod svf;
