# Language surface

The authoritative capability list is available through `qrust capabilities` and is defined in `src/surface.rs`. Available syntax depends on the frontend and whether an operation is compile-time or runtime.

## Implemented categories

- Quantum handles, named gates, measurement, reset, and barriers
- Scalar expressions and compile-time math functions
- Compile-time `let`, `const`, selected mutable scalars, and static assertions
- Functions and restricted reference parameters, including `&mut Qubit`
- Compile-time `if`/`else`, `match`, loops, and range iteration in the supported surface
- Static typed integers (`i64`, `u64`) with checked arithmetic in the supported compile-time path
- Compile-time scalar structs and fieldless enums without a general runtime layout or ABI
- Measurement-dependent branching and looping for supported runtime operations
- A restricted Rust-like typed frontend with ownership and reference checking

## Distinct execution modes

`run` handles supported pure quantum sources through the local simulator and supported host programs through the host runner. `run-host` is specifically for the host program path. OpenQASM output is generated from checked pure quantum IR, not arbitrary host I/O programs.

## Unsupported general Rust language features

Rust `std`, general `trait`/`impl` resolution, GAT, HRTB, closures capturing borrows, async state-machine execution, user `Drop` and drop check, heap `Box` semantics, and general dereference coercions are not implemented as complete Rust features.

This document defines the intended test-release scope. Specific compiler diagnostics and the `capabilities` command take precedence over inferred Rust equivalence.
