# QRust
**VERY EARLY RAW TEST LAGUAGE EVERYTHING CAN CHANGE IN FUTURE**

**QRust is an experimental quantum programming language** compiler written in Rust. It provides a quantum language frontend, a Rust-inspired static ownership system for supported constructs, OpenQASM 3 output, a QCU interchange format, and local execution tools.

**Status:** experimental test release, version `0.6.91-borrow-checker-architecture-validation-preview.1.fix.1`. QRust is not a Rust compiler, a `rustc` replacement, or a formally verified borrow checker. Hardware execution requires an external backend adapter.

## Requirements

- Rust 1.95.0 with Cargo (`rust-toolchain.toml` selects the tested toolchain)
- Python 3 for optional differential audit reports (standard library only)
- PowerShell for the existing Windows hybrid verification script

The compiler has no third-party Cargo dependencies in its default configuration.

## Build

```sh
cargo build --release
cargo test --quiet
```

The binary is written to `target/release/qrust.exe` on Windows or `target/release/qrust` on Unix-like systems.

## CLI

```sh
cargo run --release -- help
cargo run --release -- capabilities
cargo run --release -- check benchmark_fixtures/core_gates.qr
cargo run --release -- build benchmark_fixtures/core_gates.qr
```

`check` parses and checks a `.qr` source file. `build` emits a `.qasm` file alongside the input. `build-qcu` encodes QCU interchange data. `run` executes supported programs through the local simulator or the selected host backend. `check-host` checks the restricted host language and is not equivalent to all `check` paths.

See [CLI reference](docs/CLI.md) for command syntax and execution limits.

## Architecture

The codebase contains a lexer/parser, two compilation paths selected by source constructs, semantic checking, typed IR, MIR/CFG borrow analysis, quantum IR output, a QCU codec, and local execution components. The typed Rust-like frontend supports a restricted subset rather than arbitrary Rust syntax.

See [architecture](docs/ARCHITECTURE.md), [language surface](docs/LANGUAGE.md), and [ownership model](docs/BORROW_CHECKER.md).

## Validation

The Windows validation log for this source baseline reports:

| Check | Reported result |
|---|---|
| Unit tests (`src/main.rs`) | 1,647 passed |
| `borrow_rustc_oracle` integration tests | 2 passed |
| Rust/QRust paired borrow cases | 21 matching verdicts |
| Unsupported Rust-only oracle cases | 8 tracked |
| Release build | Passed |
| Hybrid MIR/CFG checks | Passed |

Reference toolchain reported by the audit: `rustc 1.95.0 (59807616e 2026-04-14)`. These are results of a previous Windows run, not a claim that every platform or future toolchain has been tested. Matching verdicts do not establish full Rust equivalence or formal soundness.

To reproduce the audit:

```sh
cargo test --test borrow_rustc_oracle -- --nocapture
python scripts/audit_borrow_rustc.py --validate-only
python scripts/audit_borrow_rustc.py --self-test
python scripts/audit_borrow_rustc.py --qrust target/release/qrust --json target/borrow_audit.json --markdown target/borrow_audit.md
```

On Windows, replace the audit binary path with `target/release/qrust.exe`. Build the release executable before running the Python audit. Consult [validation](docs/VALIDATION.md) for classification rules and test boundaries.

## Scope

QRust does not provide a general Rust standard library or full support for traits, GAT, HRTB, closure captures, `async`/`await` execution, user-defined destructors, `Box`, or arbitrary dereference coercions. Some language constructs are compile-time only. Runtime and hardware execution are separate from compile-time ownership checking.

See [limitations](docs/LIMITATIONS.md) for specific boundaries.

## Repository

- `src/` — compiler, IR, borrow checking, QCU encoding, and local execution code
- `tests/` — integration tests and `rustc` comparison fixtures
- `benchmark_fixtures/` — benchmark input data
- `examples/` — pre-existing language and verification fixtures
- `scripts/` — audits, smoke tests, and historical benchmark scripts
- `docs/` — current English-language reference documentation

Older version-by-version development notes are not included in this public test package. The existing verification fixtures and scripts are retained for reproducibility.

## Support

For technical support, questions, and bug reports, use [QRust Support Discussions](https://github.com/Vacuoss/Support/discussions).

## License

MIT. See [LICENSE](LICENSE).
