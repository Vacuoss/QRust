# Command-line interface

The CLI usage is defined in `src/main.rs` and can be displayed with `qrust help`.

## Check, build, and run

| Command | Behavior |
|---|---|
| `qrust check <file.qr>` | Compile-time validation of supported `.qr` source |
| `qrust build <file.qr>` | Emit `.qasm` beside the source |
| `qrust build-qcu <file.qr>` | Encode the QCU interchange format |
| `qrust inspect-qcu <file.qcu>` | Inspect a QCU interchange file |
| `qrust run <file.qr>` | Execute supported source using the local/selected backend |
| `qrust run-qcu <file.qcu>` | Simulate a QCU file locally |
| `qrust run-host <file.qr>` | Execute the supported host language |
| `qrust check-host <file.qr>` | Restricted host-source validation |
| `qrust capabilities` | List capability descriptors |
| `qrust ops` | List quantum operations and builtins |
| `qrust ir-stats <file.qr>` | Report quantum IR metrics |

`build` accepts `--skip-unchanged`, `--force-write`, `--sync`, `--stream`, and `--string` subject to CLI compatibility checks. `run` accepts shot and seed options and additional supported host input/backend options. `build-qcu` accepts `--sync`.

## Benchmarks

Commands include `bench`, `bench-stages`, `bench-host-check`, `bench-e2e`, `bench-regions`, `bench-qasm`, and I/O benchmarks. These tools measure different stages or execution paths and should not be compared without matching their parameters and scope.

## Windows example

```powershell
cargo build --release
.\target\release\qrust.exe capabilities
.\target\release\qrust.exe check benchmark_fixtures\core_gates.qr
powershell -ExecutionPolicy Bypass -File scripts\verify_hybrid_0616.ps1
```

The verification script retains its historical filename for compatibility. The filename is not the current QRust package version.
