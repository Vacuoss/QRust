# Development

## Checks

Run `cargo test --quiet` before changing the language frontend, Typed MIR, borrow checker, or output formats. Run `cargo build --release` and the differential oracle after semantic modifications. On Windows, `scripts/verify_hybrid_0616.ps1` runs the existing host regression and benchmark checks.

## Regression tests

- Add unit tests close to the relevant Rust module
- Include rejection tests for ownership or lifetime changes
- Preserve internal identifier provenance, `MovePathId`, parent-loan relationships, and path-case witnesses
- Use the existing Rust comparison corpus when a feature has a comparable Rust language surface
- Separate unsupported syntax or frontend failures from true borrow-check failures
- Treat proof-budget exhaustion as unproven, not accepted

## Source style

Write comments and documentation in English. Use `//Text` for Rust and QRust line comments, without a space after `//` or a terminal period. Do not use `//!` or `///`. Retain comments only for invariants, safety constraints, or behavior that is not evident from the code. Keep explanations of supported features in `docs/`. Do not include release history or test narration in source comments.

## Compatibility

Historical scripts and benchmark fixtures are retained to reproduce earlier checks. Some filenames contain version numbers that do not match the current package version. Renaming these scripts without updating callers is outside the documentation-only cleanup scope.
