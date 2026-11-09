# Limitations

## Language compatibility

QRust implements a restricted Rust-inspired language. It does not support the complete Rust standard library, arbitrary traits or methods, generic associated types, higher-ranked trait bounds, closure capture analysis, general async/await execution, user-defined `Drop` and associated drop checking, heap `Box` ownership, or full deref coercions.

Compile-time structs and fieldless enums are not general runtime ABI-compatible Rust types. Quantum ownership rules also differ from general Rust value semantics.

## Borrow checking

The borrow checker validates supported constructs and MIR certificates. Some valid Rust programs can be conservatively rejected. Successful checks are not a formal proof of compiler-wide soundness or equivalence with `rustc`.

Interprocedural effect analysis and CFG reasoning use finite search budgets. Unsupported evidence is not a certificate of safety. Runtime host checks remain active where the host execution model requires them.

## Runtime and backends

The local simulator is bounded and does not represent quantum hardware. OpenQASM 3 and QCU exports describe supported generated programs. QPU or external backend execution requires separately implemented and configured adapters; no hardware availability is implied by the compiler's CLI.

## Platform and validation

The reported complete validation baseline was run on Windows. Other platforms may require additional testing. Historical scripts in `scripts/` are retained for regression purposes and are not a uniform supported release interface.
