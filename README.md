# ConjureDSPLib

The shared DSP maths used by every ConjureDSP plug-in, in Rust, with Lean proofs about the code.

It takes numbers and buffers and returns numbers or fills buffers. Per-sample code does no
memory allocation, takes no locks and makes no system calls. It knows nothing about plug-in
formats, hosts, threads, parameters, saved state or the user interface: those live in
the plug-in framework. ConjureDSPLib never depends on the plug-in framework.

## Proofs

The `proofs/` folder holds Lean proofs about this crate's code. The Rust is translated to Lean
with Aeneas, using the `conjure` branch of
[michaeljancsy/aeneas](https://github.com/michaeljancsy/aeneas). The exact Aeneas, Lean and
Mathlib versions are pinned.

For each function, a proof can establish:
- that it never panics;
- that it computes exactly the textbook algorithm;
- how far its floating-point result can be from the exact real-number answer.

Each release lists which functions are proved, and under which stated assumptions (for example,
that `sin` is accurate to within one unit in the last place).

## Licence

Dual-licensed under either of [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.
