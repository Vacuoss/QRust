# Validation

## Baseline

The most recent user-provided Windows result for version `0.6.91-borrow-checker-architecture-validation-preview.1.fix.1` is:

- 1,647 unit tests passed
- Two `borrow_rustc_oracle` integration tests passed
- 21 paired `rustc` and QRust tests had matching accept/reject verdicts
- Eight Rust-only cases remained classified as unsupported surface
- Release compilation and existing hybrid verification passed
- `rustc 1.95.0 (59807616e 2026-04-14)` was used for the oracle

The repository pins Rust 1.95.0 for reproducibility of the current differential oracle. Newer Rust versions require a separate oracle revalidation.

## Reproduction

```sh
cargo test --quiet
cargo build --release
cargo test --test borrow_rustc_oracle -- --nocapture
python scripts/audit_borrow_rustc.py --validate-only
python scripts/audit_borrow_rustc.py --self-test
python scripts/audit_borrow_rustc.py --qrust target/release/qrust --json target/borrow_audit.json --markdown target/borrow_audit.md
```

Use `target/release/qrust.exe` on Windows. The external Python audit exits unsuccessfully for unexplained discrepancies or failures to execute the required tools.

## Oracle interpretation

`tests/rustc_borrow_cases/manifest.tsv` defines the audit matrix. A paired result requires both compilers to accept or both to reject and, for a rejection, QRust must provide borrow-related evidence. A matching verdict alone is not proof that internal reasoning is identical. `rustc_only` entries are not paired tests and do not count as matches.

The audit checks static compilation results. It does not execute the Rust fixtures, establish semantic identity of every Rust/QRust source pair, prove absence of soundness bugs, or validate hardware execution.

## Performance

A user-provided Windows run of the existing hybrid check reported 30 iterations with a mean of 2,432.463 microseconds per check, median 2,434.800 microseconds, and p90 2,577.500 microseconds. The benchmark excludes parsing and does not measure a QPU.
