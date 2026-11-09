//Crash-safe replacement for QRust OpenQASM output
use std::{
    fs::{self, File, OpenOptions},
    io::{self, BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

const BUF_SIZE: usize = 64 * 1024;
static NEXT_TEMP_ID: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, PartialEq, Eq)]
pub enum WriteOutcome {
    Compiled { bytes: usize },
    Unchanged { bytes: usize },
}

struct TemporaryFile { path: PathBuf }
impl Drop for TemporaryFile {
    fn drop(&mut self) { let _ = fs::remove_file(&self.path); }
}

fn temporary_in_same_directory(output: &Path) -> io::Result<(TemporaryFile, File)> {
    let dir = output.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let filename = output.file_name().ok_or_else(||
        io::Error::new(io::ErrorKind::InvalidInput, "output must have a filename"))?;
    for _ in 0..128 {
        let seq = NEXT_TEMP_ID.fetch_add(1, Ordering::Relaxed);
        let mut name = filename.to_os_string();
        name.push(format!(".qrust-{}-{seq}.tmp", std::process::id()));
        let path = dir.join(name);
        match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(file) => return Ok((TemporaryFile { path }, file)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    Err(io::Error::new(io::ErrorKind::AlreadyExists, "cannot create a unique QASM temporary file"))
}

struct CompareWriter<R: Read> {
    previous: R,
    same: bool,
    bytes: usize,
}
impl<R: Read> Write for CompareWriter<R> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.bytes += buf.len();
        if self.same {
            let mut offset = 0;
            let mut block = [0u8; 4096];
            while offset < buf.len() {
                let n = (buf.len() - offset).min(block.len());
                let mut got = 0;
                while got < n {
                    let count = self.previous.read(&mut block[got..n])?;
                    if count == 0 { self.same = false; break; }
                    got += count;
                }
                if !self.same || block[..n] != buf[offset..offset+n] {
                    self.same = false;
                    break;
                }
                offset += n;
            }
        }
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> { Ok(()) }
}

fn is_unchanged(program: &crate::ir::Program, output: &Path) -> io::Result<Option<usize>> {
    let file = match File::open(output) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    if !file.metadata()?.is_file() { return Err(io::Error::other("QASM output is not a regular file")); }
    let known_len=file.metadata()?.len();
    let mut cmp = CompareWriter { previous: BufReader::with_capacity(BUF_SIZE, file), same: true, bytes: 0 };
    let bytes = crate::sema::emit_qasm_to_writer(program, &mut cmp)?;
    if cmp.same && known_len == bytes as u64 {
        let mut tail = [0u8; 1];
        if cmp.previous.read(&mut tail)? == 0 { return Ok(Some(bytes)); }
    }
    Ok(None)
}

fn replace_atomically<F>(output: &Path, sync: bool, render: F) -> io::Result<usize>
where F: FnOnce(&mut BufWriter<File>) -> io::Result<usize>
{
    let (temporary, file) = temporary_in_same_directory(output)?;
    let mut writer = BufWriter::with_capacity(BUF_SIZE, file);
    let bytes = render(&mut writer)?;
    writer.flush()?;
    if sync { writer.get_ref().sync_all()?; }
    let file = writer.into_inner().map_err(|error| error.into_error())?;
    drop(file);
    fs::rename(&temporary.path, output)?;
    #[cfg(unix)]
    if sync {
        let parent = output.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
        File::open(parent)?.sync_all()?;
    }
    Ok(bytes)
}

pub fn write_qasm_atomic(program: &crate::ir::Program, output: &Path,
    skip_unchanged: bool, sync: bool) -> io::Result<WriteOutcome>
{
    if skip_unchanged {
        if let Some(bytes) = is_unchanged(program, output)? {
            return Ok(WriteOutcome::Unchanged { bytes });
        }
    }
    let bytes = replace_atomically(output, sync, |writer|
        crate::sema::emit_qasm_to_writer(program, writer))?;
    Ok(WriteOutcome::Compiled { bytes })
}

pub fn write_bytes_atomic(contents: &[u8], output: &Path, sync: bool) -> io::Result<usize> {
    replace_atomically(output, sync, |writer| {
        writer.write_all(contents)?;
        Ok(contents.len())
    })
}

//Explicit legacy String formatter, but still write through the same temporary-file transaction: it
//cannot corrupt the existing QASM on error
pub fn write_string_atomic(contents: &str, output: &Path, sync: bool) -> io::Result<usize> {
    replace_atomically(output, sync, |writer| {
        writer.write_all(contents.as_bytes())?;
        Ok(contents.len())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};
    fn test_path() -> PathBuf {
        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        std::env::temp_dir().join(format!("qrust-0510-{}-{nanos}.qasm", std::process::id()))
    }
    struct Clean(PathBuf);
    impl Drop for Clean { fn drop(&mut self) { let _ = fs::remove_file(&self.0); } }
    fn example_program() -> crate::ir::Program {
        crate::compile("let q = qubit();\nh(q);\n").unwrap()
    }

    #[test]
    fn atomic_stream_matches_string_exactly() {
        let path = test_path(); let _clean = Clean(path.clone());
        let program = example_program();
        let expected = crate::sema::emit_qasm(&program);
        assert_eq!(write_qasm_atomic(&program, &path, false, false).unwrap(),
            WriteOutcome::Compiled { bytes: expected.len() });
        assert_eq!(fs::read(&path).unwrap(), expected.as_bytes());
    }
    #[test]
    fn unchanged_does_not_touch_existing_file_or_leave_temp() {
        let path = test_path(); let _clean = Clean(path.clone());
        let program = example_program();
        write_qasm_atomic(&program, &path, false, false).unwrap();
        let before = fs::metadata(&path).unwrap().modified().unwrap();
        let expected = fs::read(&path).unwrap();
        assert_eq!(write_qasm_atomic(&program, &path, true, false).unwrap(),
            WriteOutcome::Unchanged { bytes: expected.len() });
        assert_eq!(fs::metadata(&path).unwrap().modified().unwrap(), before);
        assert_eq!(fs::read(&path).unwrap(), expected);
    }
    #[test]
    fn changed_output_replaces_old_file_and_is_identical_to_string() {
        let path = test_path(); let _clean = Clean(path.clone());
        fs::write(&path, b"old output that must be replaced").unwrap();
        let program = example_program();
        assert!(matches!(write_qasm_atomic(&program, &path, true, false).unwrap(), WriteOutcome::Compiled { .. }));
        assert_eq!(fs::read(&path).unwrap(), crate::sema::emit_qasm(&program).as_bytes());
    }
    #[test]
    fn failed_replace_keeps_destination_and_cleans_temp() {
        let folder = test_path().with_extension("folder");
        fs::create_dir(&folder).unwrap();
        struct RemoveDir(PathBuf);
        impl Drop for RemoveDir { fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); } }
        let _clean = RemoveDir(folder.clone());
        let path = folder.join("old.qasm");
        fs::create_dir(&path).unwrap(); //a directory cannot be atomically replaced by a file
        let program = example_program();
        assert!(write_qasm_atomic(&program, &path, false, false).is_err());
        assert!(path.is_dir());
        assert_eq!(fs::read_dir(&folder).unwrap().count(), 1);
    }
    #[test]
    fn compare_detects_equal_prefix_with_extra_suffix() {
        let path = test_path(); let _clean = Clean(path.clone());
        let program = example_program();
        let mut longer = crate::sema::emit_qasm(&program).into_bytes();
        longer.extend_from_slice(b"extra");
        fs::write(&path, longer).unwrap();
        assert!(matches!(write_qasm_atomic(&program, &path, true, false).unwrap(), WriteOutcome::Compiled { .. }));
        assert_eq!(fs::read(&path).unwrap(), crate::sema::emit_qasm(&program).as_bytes());
    }
    #[test]
    fn unchanged_build_creates_no_transaction_temp_and_preserves_timestamp() {
        let folder=test_path().with_extension("skip-folder");
        fs::create_dir(&folder).unwrap();
        struct CleanupDir(PathBuf);
        impl Drop for CleanupDir { fn drop(&mut self){let _=fs::remove_dir_all(&self.0);} }
        let _cleanup=CleanupDir(folder.clone());
        let dest=folder.join("check.qasm");
        let program=example_program();
        write_qasm_atomic(&program,&dest,false,false).unwrap();
        let before=fs::metadata(&dest).unwrap().modified().unwrap();
        for _ in 0..10 {
            assert!(matches!(write_qasm_atomic(&program,&dest,true,false).unwrap(),
                WriteOutcome::Unchanged{..}));
        }
        assert_eq!(fs::metadata(&dest).unwrap().modified().unwrap(),before);
        assert_eq!(fs::read_dir(&folder).unwrap().count(),1);
    }
    #[test]
    fn replacing_shorter_qasm_discards_old_tail() {
        let dest=test_path();let _cleanup=Clean(dest.clone());
        fs::write(&dest,vec![b'a';4096]).unwrap();
        let p=example_program();
        write_qasm_atomic(&p,&dest,true,false).unwrap();
        assert_eq!(fs::read(&dest).unwrap(),crate::sema::emit_qasm(&p).as_bytes());
    }
    #[test]
    fn comparator_handles_chunk_boundaries() {
        let mut cmp = CompareWriter { previous: &b"abcdef"[..], same: true, bytes: 0 };
        cmp.write_all(b"abc").unwrap(); cmp.write_all(b"def").unwrap();
        assert!(cmp.same);
        assert_eq!(cmp.bytes, 6);
        assert_eq!(cmp.previous.len(), 0);
        let mut changed = CompareWriter { previous: &b"abcXef"[..], same: true, bytes: 0 };
        changed.write_all(b"abc").unwrap(); changed.write_all(b"def").unwrap();
        assert!(!changed.same);
    }
}
