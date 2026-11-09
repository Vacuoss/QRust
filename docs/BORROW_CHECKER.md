# Ownership and borrow checking

## Scope

QRust applies Rust-inspired static ownership checks to supported typed MIR and CFG constructs. The implementation is not equivalent to the complete `rustc` borrow checker.

## Components

- `src/cfg_borrow.rs` defines ownership events, read/write/move conflicts, loans, parent-child relationships, and exclusive-borrow checks
- `src/cfg_nll.rs` implements CFG-based liveness, NLL region processing, and move-path information
- `src/region_infer.rs` implements named lifetime constraints for supported signatures and region relationships
- `src/typed_mir.rs` represents verified calls, conditional path cases, PHI origins, and interprocedural provenance
- `src/typed_frontend.rs` constructs supported MIR from typed source constructs

## Verified internal mechanisms

The implementation contains handling for shared and mutable loans, nested reborrows, active descendant suspension, disjoint field paths, partial moves, CFG alternatives, PHI provenance, and conditional interprocedural effects. Inferred NLL end points are represented in the CFG analysis. Exact support depends on the form lowered by the frontend.

The interprocedural proof search is bounded. Exhausting a proof budget or encountering an unsupported construct does not establish safety. A fallback path may conservatively reject source that Rust accepts.

## Test coverage

The internal unit suite is supplemented by 21 paired `rustc`/QRust fixtures covering NLL, reborrows, field projections, CFG, lifetime regions, and returned PHI references. Eight additional Rust-only fixtures track unsupported language features. Matching accept/reject decisions provide evidence for the tested cases only.

No formal soundness proof, complete Rust compatibility, or universal borrow-check equivalence is claimed.
