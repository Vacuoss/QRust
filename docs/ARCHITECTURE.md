# Architecture

## Entry point

`src/main.rs` implements CLI command selection and source compilation. `compile()` selects the typed frontend when `typed_frontend::enabled()` identifies supported typed source constructs. Otherwise it uses the lexer, parser, optional language lowering, and semantic checking path.

## Modules

| Module | Responsibility |
|---|---|
| `syntax.rs` | Lexing and parsing of the core language |
| `language.rs` | Lowering of parsed language constructs |
| `sema.rs` | Semantic validation and OpenQASM emission |
| `typed_frontend.rs` | Restricted Rust-like typed source frontend and lowering |
| `typed_mir.rs` | Typed MIR structures, interprocedural analysis, proof cases, and validation |
| `cfg_borrow.rs` | CFG ownership events, loans, and borrow checking |
| `cfg_nll.rs` | Region liveness, NLL analysis, and move-path tracking |
| `region_infer.rs` | Named region constraints and region inference helpers |
| `ids.rs` | Stable internal identifiers for symbols and paths |
| `ir.rs` | Quantum instruction representation |
| `atomic_qasm.rs` | Atomic OpenQASM output writing |
| `qcu.rs` | QCU interchange encoding and decoding |
| `local_sim.rs` | Bounded local quantum simulation |
| `host_runtime.rs` | Restricted host execution and backend selection |
| `host_static.rs` | Static analysis of the supported host subset |
| `surface.rs` | Language capability registry and reserved identifiers |

Additional modules implement supporting runtime, math, I/O, and profiling facilities.

## Compilation and validation boundaries

Static ownership checks apply to the constructs lowered through the supported MIR/CFG paths. `qrust check` handles the normal compiler checking path; host source may be dispatched to its own static checks. `qrust check-host` is not a general Rust borrow checker.

Interprocedural cases use bounded symbolic provenance and effect-case analyses. A certificate is valid only for the represented case. Unsupported or unresolved combinations must not be reported as proven safe by the certifier.

The local simulator and QCU codec are separate from Rust-style ownership validation. A successful source check does not certify an external hardware execution environment.
