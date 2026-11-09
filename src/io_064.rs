//Opt-in high-throughput QASM writer and filesystem phase profiler
use std::{fs::{self,File,OpenOptions},io::{self,BufWriter,Seek,SeekFrom,Write},path::{Path,PathBuf},time::{Duration,Instant,SystemTime,UNIX_EPOCH}};

pub struct PersistentQasmWriter { writer: BufWriter<File> }

impl PersistentQasmWriter {
    pub fn new(path: &Path) -> io::Result<Self> {
        let file = OpenOptions::new().create(true).read(true).write(true).open(path)?;
        Ok(Self { writer: BufWriter::with_capacity(64*1024,file) })
    }
    pub fn write(&mut self, qasm: &[u8]) -> io::Result<()> {
        self.writer.seek(SeekFrom::Start(0))?;
        self.writer.write_all(qasm)?;
        self.writer.flush()?;
        self.writer.get_ref().set_len(qasm.len() as u64)
    }
    fn write_profiled(&mut self,qasm:&[u8])->io::Result<[Duration;4]>{
        let start=Instant::now();self.writer.seek(SeekFrom::Start(0))?;
        let seek=start.elapsed();
        let start=Instant::now();self.writer.write_all(qasm)?;
        let write=start.elapsed();
        let start=Instant::now();self.writer.flush()?;
        let flush=start.elapsed();
        let start=Instant::now();self.writer.get_ref().set_len(qasm.len() as u64)?;
        Ok([seek,write,flush,start.elapsed()])
    }
}

struct Cleanup(Vec<PathBuf>);
impl Drop for Cleanup { fn drop(&mut self) {for p in &self.0 {let _=fs::remove_file(p);} } }

fn print_phase(name:&str,samples:&[Duration]) {
    let t=crate::io_bench::summarize(samples);
    println!("  {name:<22} median {:>9.2} us, p90 {:>9.2} us",
        t.median.as_secs_f64()*1e6,t.p90.as_secs_f64()*1e6);
}

pub fn run_io_phases(args:&[String])->Result<(),String> {
    if args.len()<3 || args.len()>6 {return Err("usage: qrust bench-io-phases <file.qr> [repeats] [--dir <path>]".into());}
    let mut repeats=100usize;let mut directory=std::env::temp_dir();
    let mut parsed_n=false;let mut parsed_dir=false;let mut i=3;
    while i<args.len() {
        if args[i]=="--dir" && !parsed_dir {
            i+=1;directory=PathBuf::from(args.get(i).ok_or("--dir requires a path")?);parsed_dir=true;
        } else if !parsed_n {
            repeats=args[i].parse().map_err(|_|"invalid repeats")?;parsed_n=true;
        } else{return Err("invalid bench-io-phases arguments".into());}
        i+=1;
    }
    if !(1..=1000).contains(&repeats) {return Err("repeats must be 1..1000".into());}
    if !directory.is_dir() {return Err(format!("not a directory: {}",directory.display()));}
    let src_path=Path::new(&args[2]);
    let source=fs::read_to_string(src_path).map_err(|e|e.to_string())?;
    let program=crate::compile(&source).map_err(|e|e.to_string())?;
    let qasm=crate::sema::emit_qasm(&program);
    let nonce=SystemTime::now().duration_since(UNIX_EPOCH).map_or(0,|d|d.as_nanos());
    let stem=format!("qrust-064-{}-{nonce}",std::process::id());
    let fresh=directory.join(format!("{stem}-fresh.qasm"));
    let retained=directory.join(format!("{stem}-persistent.qasm"));
    let _cleanup=Cleanup(vec![fresh.clone(),retained.clone()]);
    let now=Instant::now();
    let mut persistent=PersistentQasmWriter::new(&retained).map_err(|e|e.to_string())?;
    let setup=now.elapsed();
    let mut opens=Vec::with_capacity(repeats);
    let mut fresh_writes=Vec::with_capacity(repeats);
    let mut closes=Vec::with_capacity(repeats);
    let mut fresh_total=Vec::with_capacity(repeats);
    let mut persistent_total=Vec::with_capacity(repeats);
    let mut persistent_phases:[Vec<Duration>;4]=std::array::from_fn(|_|Vec::with_capacity(repeats));
    let mut atomic_phases:[Vec<Duration>;5]=std::array::from_fn(|_|Vec::with_capacity(repeats));
    let mut atomic_total=Vec::with_capacity(repeats);
    let atomic_dest=directory.join(format!("{stem}-atomic.qasm"));
    let _atomic_clean=Cleanup(vec![atomic_dest.clone()]);
    for index in 0..repeats {
        let mut do_fresh=||->Result<(),String>{
            let all=Instant::now();
            let start=Instant::now();
            let mut handle=OpenOptions::new().write(true).create(true).truncate(true)
                .open(&fresh).map_err(|e|e.to_string())?;
            opens.push(start.elapsed());
            let start=Instant::now();
            handle.write_all(qasm.as_bytes()).map_err(|e|e.to_string())?;
            fresh_writes.push(start.elapsed());
            let start=Instant::now();drop(handle);closes.push(start.elapsed());
            fresh_total.push(all.elapsed());Ok(())
        };
        let mut do_persistent=||->Result<(),String>{
            let start=Instant::now();
            let phases=persistent.write_profiled(qasm.as_bytes()).map_err(|e|e.to_string())?;
            persistent_total.push(start.elapsed());
            for (n,phase) in phases.into_iter().enumerate(){persistent_phases[n].push(phase);}
            Ok(())
        };
        if index%2==0{do_fresh()?;do_persistent()?;}else{do_persistent()?;do_fresh()?;}
        let temp=directory.join(format!("{stem}-{index}-atomic.tmp"));
        let _temp_cleanup=Cleanup(vec![temp.clone()]);
        let all=Instant::now();
        let now=Instant::now();
        let file=OpenOptions::new().create_new(true).write(true).open(&temp)
            .map_err(|e|format!("cannot create atomic temporary: {e}"))?;
        atomic_phases[0].push(now.elapsed());
        let mut writer=BufWriter::with_capacity(64*1024,file);
        let now=Instant::now();writer.write_all(qasm.as_bytes()).map_err(|e|e.to_string())?;
        atomic_phases[1].push(now.elapsed());
        let now=Instant::now();writer.flush().map_err(|e|e.to_string())?;
        atomic_phases[2].push(now.elapsed());
        let now=Instant::now();drop(writer);atomic_phases[3].push(now.elapsed());
        let now=Instant::now();
        fs::rename(&temp,&atomic_dest).map_err(|e|format!("cannot replace atomically: {e}"))?;
        atomic_phases[4].push(now.elapsed());
        atomic_total.push(all.elapsed());
    }
    drop(persistent);
    for path in [&fresh,&retained,&atomic_dest] {
        if fs::read(path).map_err(|e|e.to_string())?.as_slice()!=qasm.as_bytes(){
            return Err(format!("QASM read-back mismatch at {}",path.display()));
        }
    }
    println!("QRust {} filesystem phase profile ({repeats} runs; {} bytes)",env!("CARGO_PKG_VERSION"),qasm.len());
    println!("  directory: {}",directory.display());
    println!("  one-time persistent open: {:.2} us",setup.as_secs_f64()*1e6);
    print_phase("fresh open/truncate",&opens);
    print_phase("fresh write_all",&fresh_writes);
    print_phase("fresh drop/close",&closes);
    print_phase("fresh total",&fresh_total);
    print_phase("persistent seek",&persistent_phases[0]);
    print_phase("persistent buffer write",&persistent_phases[1]);
    print_phase("persistent flush",&persistent_phases[2]);
    print_phase("persistent set_len",&persistent_phases[3]);
    print_phase("persistent total",&persistent_total);
    for (name,times) in ["atomic create_new","atomic buffer write","atomic flush","atomic close","atomic rename"].into_iter().zip(&atomic_phases){
        print_phase(name,times);
    }
    print_phase("atomic total",&atomic_total);
    println!("  three outputs byte-identical; compilation excluded; no fsync; phase timing includes probes");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn path()->PathBuf{
        let nonce=SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        std::env::temp_dir().join(format!("qrust-persistent-{}-{nonce}.qasm",std::process::id()))
    }
    #[test]fn persistent_writer_overwrites_and_truncates_exactly(){
        let file=path();let _cleanup=Cleanup(vec![file.clone()]);
        let mut writer=PersistentQasmWriter::new(&file).unwrap();
        for payload in [b"OPENQASM 3.0;\nqubit[1] q;\nh q[0];\n".as_slice(), b"short\n".as_slice(), b"".as_slice(), b"long again\n".as_slice()] {
            writer.write(payload).unwrap();
            assert_eq!(fs::read(&file).unwrap(),payload);
        }
    }
    #[test]fn persistent_writer_matches_qasm_formatter(){
        let file=path();let _cleanup=Cleanup(vec![file.clone()]);
        let program=crate::compile("let q = qubit(); h(q);").unwrap();
        let expected=crate::sema::emit_qasm(&program);
        let mut writer=PersistentQasmWriter::new(&file).unwrap();
        writer.write(expected.as_bytes()).unwrap();
        writer.write(expected.as_bytes()).unwrap();
        drop(writer);
        assert_eq!(fs::read(&file).unwrap(),expected.as_bytes());
    }
}
