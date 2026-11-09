//I/O diagnostics for QRust: distinguish temporary-file open/close latency from writes through a
//persistent handle
use std::{fs::{self, File, OpenOptions}, io::{Seek, SeekFrom, Write},
    path::{Path, PathBuf}, time::{Duration, Instant, SystemTime, UNIX_EPOCH}};

#[derive(Clone, Copy, Debug)]
pub struct LatencySummary {
    pub median: Duration,
    pub p90: Duration,
    pub min: Duration,
    pub max: Duration,
}

pub fn summarize(values: &[Duration]) -> LatencySummary {
    assert!(!values.is_empty());
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    let n = sorted.len();
    LatencySummary {
        median: if n % 2 == 0 { (sorted[n / 2 - 1] + sorted[n / 2]) / 2 } else { sorted[n / 2] },
        p90: sorted[((9 * n + 9) / 10).saturating_sub(1).min(n - 1)],
        min: sorted[0], max: sorted[n - 1],
    }
}

#[cfg(test)]
pub fn write_if_changed(path: &Path, contents: &[u8]) -> std::io::Result<bool> {
    if let Ok(info) = fs::metadata(path) {
        if info.is_file() && info.len() == contents.len() as u64 {
            if let Ok(old) = fs::read(path) {
                if old.as_slice() == contents { return Ok(false); }
            }
        }
    }
    fs::write(path, contents)?;
    Ok(true)
}

struct TemporaryPaths(Vec<PathBuf>);
impl Drop for TemporaryPaths {
    fn drop(&mut self) {
        for path in &self.0 { let _ = fs::remove_file(path); }
    }
}

pub struct IoComparison {
    pub fresh: LatencySummary,
    pub reuse: LatencySummary,
    pub bytes: usize,
    pub directory: PathBuf,
}

pub fn compare_writes(contents: &[u8], iterations: usize, directory: &Path)
    -> Result<IoComparison, String>
{
    if iterations == 0 || iterations > 1000 { return Err("repeats must be 1..1000".into()); }
    if !directory.is_dir() {
        return Err(format!("not a directory: {}", directory.display()));
    }
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH)
        .map_or(0, |duration| duration.as_nanos());
    let prefix = format!("qrust-io-{}-{nonce}", std::process::id());
    let fresh_path = directory.join(format!("{prefix}-fresh.qasm"));
    let reuse_path = directory.join(format!("{prefix}-reuse.qasm"));
    let _cleanup = TemporaryPaths(vec![fresh_path.clone(), reuse_path.clone()]);
    let mut reused: File = OpenOptions::new().create_new(true).write(true)
        .open(&reuse_path).map_err(|e| format!("cannot create {}: {e}", reuse_path.display()))?;
    let mut fresh_samples = Vec::with_capacity(iterations);
    let mut reuse_samples = Vec::with_capacity(iterations);
    for n in 0..iterations {
        let mut fresh = || -> Result<(), String> {
            let start = Instant::now();
            fs::write(&fresh_path, contents)
                .map_err(|e| format!("cannot write {}: {e}", fresh_path.display()))?;
            fresh_samples.push(start.elapsed());
            Ok(())
        };
        let mut reuse = || -> Result<(), String> {
            let start = Instant::now();
            reused.set_len(0).map_err(|e| format!("cannot truncate: {e}"))?;
            reused.seek(SeekFrom::Start(0)).map_err(|e| format!("cannot seek: {e}"))?;
            reused.write_all(contents).map_err(|e| format!("cannot write: {e}"))?;
            reuse_samples.push(start.elapsed());
            Ok(())
        };
        if n % 2 == 0 { fresh()?; reuse()?; } else { reuse()?; fresh()?; }
    }
    drop(reused);
    for path in [&fresh_path, &reuse_path] {
        let written = fs::read(path).map_err(|e| format!("cannot verify {}: {e}", path.display()))?;
        if written.as_slice() != contents {
            return Err(format!("I/O verification failed: {}", path.display()));
        }
    }
    Ok(IoComparison { fresh: summarize(&fresh_samples), reuse: summarize(&reuse_samples),
        bytes: contents.len(), directory: directory.to_path_buf() })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn latency_percentiles_handle_even_and_odd_counts() {
        let millis = |n| Duration::from_millis(n);
        let s = summarize(&[millis(8), millis(1), millis(3), millis(2), millis(5)]);
        assert_eq!((s.min, s.median, s.p90, s.max), (millis(1),millis(3),millis(8),millis(8)));
        let s = summarize(&[millis(4), millis(1), millis(3), millis(2)]);
        assert_eq!((s.min, s.median, s.p90, s.max), (millis(1),Duration::from_micros(2500),millis(4),millis(4)));
    }

    #[test]
    fn skip_unchanged_write_preserves_file_contents() {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let name = format!("qrust-skip-{}-{nonce}.qasm", std::process::id());
        let path = std::env::temp_dir().join(name);
        let _cleanup = TemporaryPaths(vec![path.clone()]);
        assert!(write_if_changed(&path, b"OPENQASM 3.0;\n").unwrap());
        assert!(!write_if_changed(&path, b"OPENQASM 3.0;\n").unwrap());
        assert!(write_if_changed(&path, b"OPENQASM 3.0;\nh q[0];\n").unwrap());
        assert_eq!(fs::read(path).unwrap(), b"OPENQASM 3.0;\nh q[0];\n");
    }

    #[test]
    fn skip_unchanged_never_accepts_same_length_different_content() {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let name = format!("qrust-unequal-{}-{nonce}.qasm", std::process::id());
        let path = std::env::temp_dir().join(name);
        let _cleanup = TemporaryPaths(vec![path.clone()]);
        assert!(write_if_changed(&path, b"abc").unwrap());
        assert!(write_if_changed(&path, b"def").unwrap());
        assert!(!write_if_changed(&path, b"def").unwrap());
    }

    #[test]
    fn io_comparison_writes_identical_bytes() {
        let data = b"OPENQASM 3.0;\ninclude \"stdgates.inc\";\nrx(0.125) q[0];\n";
        let report = compare_writes(data, 3, &std::env::temp_dir()).unwrap();
        assert_eq!(report.bytes, data.len());
        assert!(report.fresh.p90 >= report.fresh.median);
        assert!(report.reuse.p90 >= report.reuse.median);
    }

    #[test]
    fn io_comparison_rejects_invalid_directory_and_zero_runs() {
        assert!(compare_writes(b"x", 0, &std::env::temp_dir()).is_err());
        assert!(compare_writes(b"x", 1, Path::new("nonexistent-qrust-bench-folder-000")).is_err());
    }
}
