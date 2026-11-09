use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

#[test]
#[ignore = "opt-in diagnostic: investigate Windows native redirected stdin"]
fn native_qrust_process_reads_redirected_ascii_stdin() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples").join("hybrid_coin_flip_0614.qr");
    let mut child = Command::new(env!("CARGO_BIN_EXE_qrust"))
        .arg("run-host").arg(&path).arg("--seed").arg("42")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped())
        .spawn().expect("spawn QRust native stdin test");
    child.stdin.take().expect("child stdin").write_all(b"100\n")
        .expect("write ASCII stdin to QRust");
    let result = child.wait_with_output().expect("wait for QRust");
    let stdout = String::from_utf8_lossy(&result.stdout);
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(result.status.success(), "QRust stdin subprocess failed:\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}");
    assert!(stdout.contains("Total: 100"), "QRust read unexpected stdin:\n{stdout}");
}

#[test]
fn native_qrust_process_accepts_deterministic_cli_input() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples").join("hybrid_coin_flip_0614.qr");
    let result = Command::new(env!("CARGO_BIN_EXE_qrust"))
        .arg("run-host").arg(&path).arg("--seed").arg("42")
        .arg("--input").arg("100")
        .stdin(Stdio::null()).output().expect("spawn QRust CLI input test");
    let stdout = String::from_utf8_lossy(&result.stdout);
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(result.status.success(), "QRust CLI input subprocess failed:\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}");
    assert!(stdout.contains("Total: 100"), "QRust CLI input output:\n{stdout}");
}
