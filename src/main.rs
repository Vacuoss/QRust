mod atomic_qasm;
mod ids;
#[cfg(test)]
mod name_id_experiment;
mod io_bench;
mod io_064;
mod ir;
mod qcu;
mod local_sim;
mod host_runtime;
mod async_ir;
mod language;
mod math;
mod sema;
mod syntax;
mod surface;
#[cfg(test)]
#[path = "test_support/legacy_static_oracle.rs"]
mod rust_static;
mod cfg_nll;
mod cfg_borrow;
mod typed_mir;
mod typed_patterns;
mod region_infer;
mod typed_frontend;
#[cfg(feature = "alloc-profile")]
mod alloc_profile;

const MAX_BENCH_ITERATIONS: usize = 10_000_000;

use std::{env, fs, hint::black_box, io::{self, Write}, path::{Path, PathBuf}, time::{Duration, Instant, SystemTime, UNIX_EPOCH}};

fn compile(source: &str) -> Result<ir::Program, syntax::Diagnostic> {
    if typed_frontend::enabled(source) { return typed_frontend::compile(source); }
    let tokens = syntax::lex(source)?;
    let parsed = syntax::Parser::new(tokens).parse()?;
    if parsed.needs_lowering {
        let lowered = language::lower(&parsed.statements)?;
        sema::check(&lowered)
    } else {
        sema::check(&parsed.statements)
    }
}

#[derive(Default)]
struct StageTimes {
    lex: Duration,
    parse: Duration,
    lower: Duration,
    sema: Duration,
    emit: Duration,
}

fn compile_detailed(source: &str) -> Result<(ir::Program, StageTimes), syntax::Diagnostic> {
    if typed_frontend::enabled(source) {
        let (compiled, lex, parse, lower, sema)=typed_frontend::compile_timed(source)?;
        return Ok((compiled, StageTimes {lex, parse, lower, sema, ..StageTimes::default()}));
    }
    let mut times = StageTimes::default();
    let started = Instant::now();
    #[cfg(feature = "alloc-profile")]
    let alloc_stage = alloc_profile::StageScope::enter(alloc_profile::Stage::Lexer);
    let tokens = syntax::lex(source)?;
    #[cfg(feature = "alloc-profile")]
    drop(alloc_stage);
    times.lex = started.elapsed();
    let started = Instant::now();
    #[cfg(feature = "alloc-profile")]
    let alloc_stage = alloc_profile::StageScope::enter(alloc_profile::Stage::Parser);
    let parsed = syntax::Parser::new(tokens).parse()?;
    #[cfg(feature = "alloc-profile")]
    drop(alloc_stage);
    times.parse = started.elapsed();
    let checked = if parsed.needs_lowering {
        let started = Instant::now();
        #[cfg(feature = "alloc-profile")]
        let alloc_stage = alloc_profile::StageScope::enter(alloc_profile::Stage::Lowering);
        let lowered = language::lower(&parsed.statements)?;
        #[cfg(feature = "alloc-profile")]
        drop(alloc_stage);
        times.lower += started.elapsed();
        let started = Instant::now();
        #[cfg(feature = "alloc-profile")]
        let alloc_stage = alloc_profile::StageScope::enter(alloc_profile::Stage::Semantic);
        let checked = sema::check(&lowered)?;
        #[cfg(feature = "alloc-profile")]
        drop(alloc_stage);
        times.sema = started.elapsed();
        checked
    } else {
        let started = Instant::now();
        #[cfg(feature = "alloc-profile")]
        let alloc_stage = alloc_profile::StageScope::enter(alloc_profile::Stage::Semantic);
        let checked = sema::check(&parsed.statements)?;
        #[cfg(feature = "alloc-profile")]
        drop(alloc_stage);
        times.sema = started.elapsed();
        checked
    };
    Ok((checked, times))
}

fn print_stage(name: &str, time: Duration, iterations: usize, total: Duration) {
    let ms = time.as_secs_f64() * 1_000.0;
    let percent = if total.is_zero() { 0.0 } else { 100.0 * time.as_secs_f64() / total.as_secs_f64() };
    println!("  {name:<15} {ms:>10.3} ms  ({percent:>5.1}%)  {:.2} us/compile",
        time.as_secs_f64() * 1_000_000.0 / iterations as f64);
}

#[cfg(windows)]
fn peak_resident_bytes() -> Option<u64> {
    use std::ffi::c_void;
    #[repr(C)]
    struct ProcessMemoryCounters {
        cb: u32,
        page_fault_count: u32,
        peak_working_set_size: usize,
        working_set_size: usize,
        quota_peak_paged_pool_usage: usize,
        quota_paged_pool_usage: usize,
        quota_peak_non_paged_pool_usage: usize,
        quota_non_paged_pool_usage: usize,
        pagefile_usage: usize,
        peak_pagefile_usage: usize,
    }
    #[link(name = "kernel32")]
    unsafe extern "system" { fn GetCurrentProcess() -> *mut c_void; }
    #[link(name = "psapi")]
    unsafe extern "system" {
        fn GetProcessMemoryInfo(process: *mut c_void,
            counters: *mut ProcessMemoryCounters, size: u32) -> i32;
    }
    let mut counters = ProcessMemoryCounters {
        cb: std::mem::size_of::<ProcessMemoryCounters>() as u32,
        page_fault_count: 0,
        peak_working_set_size: 0,
        working_set_size: 0,
        quota_peak_paged_pool_usage: 0,
        quota_paged_pool_usage: 0,
        quota_peak_non_paged_pool_usage: 0,
        quota_non_paged_pool_usage: 0,
        pagefile_usage: 0,
        peak_pagefile_usage: 0,
    };
    let size = counters.cb;
    let status = unsafe {
        GetProcessMemoryInfo(GetCurrentProcess(), &mut counters, size)
    };
    (status != 0).then_some(counters.peak_working_set_size as u64)
}
#[cfg(target_os = "linux")]
fn peak_resident_bytes() -> Option<u64> {
    let status = fs::read_to_string("/proc/self/status").ok()?;
    let field = status.lines().find(|line| line.starts_with("VmHWM:"))?;
    let kb = field.split_whitespace().nth(1)?.parse::<u64>().ok()?;
    kb.checked_mul(1024)
}
#[cfg(not(any(windows, target_os = "linux")))]
fn peak_resident_bytes() -> Option<u64> { None }

struct TemporaryQasm(PathBuf);
impl TemporaryQasm {
    fn new() -> Self {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos());
        Self(env::temp_dir().join(format!("qrust-{}-{nonce}.qasm", std::process::id())))
    }
}
impl Drop for TemporaryQasm {
    fn drop(&mut self) { let _ = fs::remove_file(&self.0); }
}

fn print_peak_memory() {
    match peak_resident_bytes() {
        Some(bytes) => println!("Peak process RSS/working set: {:.2} MiB ({bytes} bytes)",
            bytes as f64 / 1_048_576.0),
        None => println!("Peak process memory unavailable on this platform"),
    }
}

fn run_e2e_benchmark(args: &[String]) -> Result<(), String> {
    if args.len() < 3 || args.len() > 6 {
        return Err("usage: qrust bench-e2e <file.qr> [repeats] [--emit-profile] [--persistent]".into());
    }
    let file = Path::new(&args[2]);
    let mut repeats = 5usize;
    let mut emit_profile = false;
    let mut persistent_mode = false;
    let mut count_seen = false;
    for arg in &args[3..] {
        if arg == "--emit-profile" {
            if emit_profile { return Err("duplicate --emit-profile".into()); }
            emit_profile = true;
        } else if arg == "--persistent" {
            if persistent_mode {return Err("duplicate --persistent".into());}
            persistent_mode = true;
        } else if !count_seen {
            repeats = arg.parse().map_err(|_| "repeats must be a positive integer")?;
            count_seen = true;
        } else { return Err("invalid bench-e2e arguments".into()); }
    }
    if !(1..=1000).contains(&repeats) { return Err("repeats must be 1..1000".into()); }
    let dest = TemporaryQasm::new();
    let mut persistent=if persistent_mode {
        Some(io_064::PersistentQasmWriter::new(&dest.0)
            .map_err(|e|format!("cannot open persistent output: {e}"))?)
    }else{None};
    let mut last_output=Vec::new();
    let mut read = Duration::ZERO;
    let mut check = Duration::ZERO;
    let mut emission = Duration::ZERO;
    let mut write = Duration::ZERO;
    let mut float = Duration::ZERO;
    let mut operands = Duration::ZERO;
    let mut emitted_bytes = 0;
    let mut write_samples = Vec::with_capacity(repeats);
    let mut total_samples = Vec::with_capacity(repeats);
    let start_all = Instant::now();
    for _ in 0..repeats {
        let run_started = Instant::now();
        let now = Instant::now();
        let src = fs::read_to_string(file)
            .map_err(|e| format!("cannot read {}: {e}", file.display()))?;
        read += now.elapsed();
        let now = Instant::now();
        let program = compile(black_box(&src))
            .map_err(|e| format!("{}:{e}", file.display()))?;
        check += now.elapsed();
        let now = Instant::now();
        let output = if emit_profile {
            let (qasm, timings) = sema::emit_qasm_profiled(&program);
            float += timings.float_format;
            operands += timings.operand_append;
            qasm
        } else { sema::emit_qasm(&program) };
        emitted_bytes = output.len();
        emission += now.elapsed();
        let now = Instant::now();
        if let Some(writer)=persistent.as_mut() {
            writer.write(output.as_bytes())
                .map_err(|e|format!("cannot write persistent QASM: {e}"))?;
        } else {
            fs::write(&dest.0, output.as_bytes())
                .map_err(|e| format!("cannot write {}: {e}", dest.0.display()))?;
        }
        let write_time = now.elapsed();
        write += write_time;
        write_samples.push(write_time);
        total_samples.push(run_started.elapsed());
        if persistent_mode {last_output=output.into_bytes();}
    }
    let total = start_all.elapsed();
    drop(persistent);
    if persistent_mode && fs::read(&dest.0).map_err(|e|format!("cannot verify persistent QASM: {e}"))? != last_output {
        return Err("persistent QASM read-back differs from emitted output".into());
    }
    println!("QRust {} end-to-end benchmark, {repeats} runs", env!("CARGO_PKG_VERSION"));
    println!("  read source:     {:.2} us/run", read.as_secs_f64()*1e6/repeats as f64);
    println!("  parse + check:   {:.2} us/run", check.as_secs_f64()*1e6/repeats as f64);
    println!("  emit OpenQASM:   {:.2} us/run", emission.as_secs_f64()*1e6/repeats as f64);
    println!("  write QASM:     {:.2} us/run", write.as_secs_f64()*1e6/repeats as f64);
    println!("  wall-clock:     {:.2} us/run", total.as_secs_f64()*1e6/repeats as f64);
    println!("  output bytes:   {emitted_bytes}");
    let write_stats = io_bench::summarize(&write_samples);
    let wall_stats = io_bench::summarize(&total_samples);
    println!("  write latency:  median {:.2}, p90 {:.2} us",
        write_stats.median.as_secs_f64()*1e6, write_stats.p90.as_secs_f64()*1e6);
    println!("  run latency:    median {:.2}, p90 {:.2} us",
        wall_stats.median.as_secs_f64()*1e6, wall_stats.p90.as_secs_f64()*1e6);
    if emit_profile {
        println!("  profiled float conversion: {:.2} us/run", float.as_secs_f64()*1e6/repeats as f64);
        println!("  profiled operands:         {:.2} us/run", operands.as_secs_f64()*1e6/repeats as f64);
        println!("  profiler overhead is included in emit OpenQASM; compare unprofiled runs for speed");
    }
    println!("  output mode: {}",if persistent_mode{"persistent handle (not atomic)"}else{"fresh fs::write"});
    println!("  file writing includes OS cache, not fsync or QPU execution");
    print_peak_memory();
    Ok(())
}

fn stream_qasm_file(program: &ir::Program, path: &Path) -> io::Result<usize> {
    let file = fs::File::create(path)?;
    let mut writer = io::BufWriter::with_capacity(64 * 1024, file);
    let bytes = sema::emit_qasm_to_writer(program, &mut writer)?;
    writer.flush()?;
    Ok(bytes)
}

fn run_qasm_benchmark(args: &[String]) -> Result<(), String> {
    if args.len() < 3 || args.len() > 4 {
        return Err("usage: qrust bench-qasm <file.qr> [repeats]".into());
    }
    let repeats: usize = args.get(3).map_or(Ok(20), |s| s.parse()
        .map_err(|_| "repeats must be an integer"))?;
    if !(1..=1000).contains(&repeats) { return Err("repeats must be 1..1000".into()); }
    let source_path = Path::new(&args[2]);
    let source = fs::read_to_string(source_path)
        .map_err(|e| format!("cannot read {}: {e}", source_path.display()))?;
    let program = compile(&source).map_err(|e| e.to_string())?;
    let baseline = sema::emit_qasm(&program);
    let mut streamed = Vec::new();
    let bytes = sema::emit_qasm_to_writer(&program, &mut streamed)
        .map_err(|e| format!("cannot render to memory: {e}"))?;
    if streamed != baseline.as_bytes() || bytes != baseline.len() {
        return Err("String and streamed QASM differ".into());
    }
    drop(streamed);
    drop(baseline);
    let path = TemporaryQasm::new();
    let mut string_samples = Vec::with_capacity(repeats);
    let mut sink_samples = Vec::with_capacity(repeats);
    let mut file_samples = Vec::with_capacity(repeats);
    for _ in 0..repeats {
        let started = Instant::now();
        let text = black_box(sema::emit_qasm(black_box(&program)));
        string_samples.push(started.elapsed());
        black_box(text.len());
        let started = Instant::now();
        let count = sema::emit_qasm_to_writer(black_box(&program), &mut io::sink())
            .map_err(|e| format!("sink error: {e}"))?;
        sink_samples.push(started.elapsed());
        black_box(count);
        let started = Instant::now();
        let count = stream_qasm_file(black_box(&program), &path.0)
            .map_err(|e| format!("cannot stream QASM file: {e}"))?;
        file_samples.push(started.elapsed());
        black_box(count);
    }
    println!("QRust {} QASM comparison, {repeats} runs", env!("CARGO_PKG_VERSION"));
    println!("  instructions: {}, output bytes: {}", program.instructions.len(), bytes);
    for (label, samples) in [("String only", &string_samples),
                             ("stream to io::sink", &sink_samples),
                             ("stream to new file", &file_samples)] {
        let t = io_bench::summarize(samples);
        println!("  {label}: median {:.2} us, p90 {:.2} us",
            t.median.as_secs_f64()*1e6, t.p90.as_secs_f64()*1e6);
    }
    println!("  all formats byte-identical; no fsync; streamed build uses 64 KiB buffer");
    print_peak_memory();
    Ok(())
}

fn run_io_benchmark(args: &[String]) -> Result<(), String> {
    if args.len() < 3 || args.len() > 6 {
        return Err("usage: qrust bench-io <file.qr> [repeats] [--dir <path>]".into());
    }
    let input = Path::new(&args[2]);
    let mut repeats = 25usize;
    let mut found_repeats = false;
    let mut dir = env::temp_dir();
    let mut found_dir = false;
    let mut cursor = 3;
    while cursor < args.len() {
        if args[cursor] == "--dir" && !found_dir {
            cursor += 1;
            let value = args.get(cursor).ok_or("--dir requires a path")?;
            dir = PathBuf::from(value);
            found_dir = true;
        } else if !found_repeats {
            repeats = args[cursor].parse().map_err(|_| "repeats must be an integer")?;
            found_repeats = true;
        } else {
            return Err("usage: qrust bench-io <file.qr> [repeats] [--dir <path>]".into());
        }
        cursor += 1;
    }
    if !(1..=1000).contains(&repeats) { return Err("repeats must be 1..1000".into()); }
    let source = fs::read_to_string(input)
        .map_err(|e| format!("cannot read {}: {e}", input.display()))?;
    let compiled = compile(&source).map_err(|e| format!("{}:{e}", input.display()))?;
    let qasm = sema::emit_qasm(&compiled);
    let result = io_bench::compare_writes(qasm.as_bytes(), repeats, &dir)?;
    println!("QRust {} isolated I/O benchmark, {repeats} runs", env!("CARGO_PKG_VERSION"));
    println!("  directory:     {}", result.directory.display());
    println!("  output bytes:  {}", result.bytes);
    for (label, stats) in [("fresh fs::write", result.fresh),
                           ("reused handle  ", result.reuse)] {
        println!("  {label}: median {:.2} us, p90 {:.2} us, min {:.2}, max {:.2}",
            stats.median.as_secs_f64()*1e6, stats.p90.as_secs_f64()*1e6,
            stats.min.as_secs_f64()*1e6, stats.max.as_secs_f64()*1e6);
    }
    println!("  compilation/emission excluded; read-back verified; no fsync");
    println!("  temporary QASM files removed after the benchmark");
    Ok(())
}

fn stress_source(size: usize) -> String {
    let mut source = String::new();
    for chunk in 0..(size / 100_000) {
        let base = chunk * 100_000;
        source.push_str(&format!(
            "for i in 0..100000 {{ gphase((i+{base})*pi/{size}); }}\n"));
    }
    let remainder = size % 100_000;
    if remainder != 0 {
        let base = size - remainder;
        source.push_str(&format!(
            "for i in 0..{remainder} {{ gphase((i+{base})*pi/{size}); }}\n"));
    }
    source
}
fn run_stress_benchmark(args: &[String]) -> Result<(), String> {
    if args.len() < 3 || args.len() > 4 {
        return Err("usage: qrust bench-stress <10000|100000|500000> [max_peak_mib]".into());
    }
    let size: usize = args[2].parse().map_err(|_| "invalid instruction count")?;
    if ![10_000, 100_000, 500_000].contains(&size) {
        return Err("supported stress sizes: 10000, 100000, 500000".into());
    }
    let max_peak = if let Some(value) = args.get(3) {
        let mib: u64 = value.parse().map_err(|_| "max_peak_mib must be a positive integer")?;
        Some(mib.checked_mul(1_048_576).ok_or("memory limit overflow")?)
    } else { None };
    let src = stress_source(size);
    let start = Instant::now();
    let program = compile(&src).map_err(|e| format!("stress compile failed: {e}"))?;
    let checked = start.elapsed();
    if program.instructions.len() != size {
        return Err(format!("stress expected {size} IR instructions, got {}", program.instructions.len()));
    }
    let ir_storage = program.estimated_storage_bytes();
    let start = Instant::now();
    let qasm = sema::emit_qasm(&program);
    let emit = start.elapsed();
    let target = TemporaryQasm::new();
    let start = Instant::now();
    fs::write(&target.0, qasm.as_bytes()).map_err(|e| format!("stress write failed: {e}"))?;
    let write = start.elapsed();
    println!("QRust {} stress: {size} instructions", env!("CARGO_PKG_VERSION"));
    println!("  check: {:.3} ms, emitter: {:.3} ms, write: {:.3} ms",
        checked.as_secs_f64()*1000., emit.as_secs_f64()*1000., write.as_secs_f64()*1000.);
    println!("  IR vector capacities: {ir_storage} bytes (excludes symbols/AST)");
    println!("  emitted bytes: {}", qasm.len());
    print_peak_memory();
    if let Some(limit) = max_peak {
        match peak_resident_bytes() {
            Some(peak) if peak > limit => return Err(format!("memory limit exceeded: peak {peak} > budget {limit}")),
            Some(_) => println!("  memory budget: PASS"),
            None => return Err("cannot enforce memory limit: process peak RSS unavailable".into()),
        }
    }
    Ok(())
}

fn run_stream_stress(args: &[String]) -> Result<(), String> {
    if args.len() < 3 || args.len() > 4 {
        return Err("usage: qrust bench-stress-stream <10000|100000|500000> [max_peak_mib]".into());
    }
    let size: usize = args[2].parse().map_err(|_| "invalid instruction count")?;
    if ![10_000, 100_000, 500_000].contains(&size) {
        return Err("supported stress sizes: 10000, 100000, 500000".into());
    }
    let max_peak = if let Some(value) = args.get(3) {
        let mib: u64 = value.parse().map_err(|_| "max_peak_mib must be a positive integer")?;
        Some(mib.checked_mul(1_048_576).ok_or("memory limit overflow")?)
    } else { None };
    let src = stress_source(size);
    let started = Instant::now();
    let program = compile(&src).map_err(|e| format!("stress compile failed: {e}"))?;
    let check_time = started.elapsed();
    if program.instructions.len() != size {
        return Err(format!("stress expected {size} instructions, got {}", program.instructions.len()));
    }
    let ir_storage = program.estimated_storage_bytes();
    let target = TemporaryQasm::new();
    let started = Instant::now();
    let bytes = stream_qasm_file(&program, &target.0)
        .map_err(|e| format!("stream failed: {e}"))?;
    let stream_time = started.elapsed();
    println!("QRust {} stream stress: {size} instructions", env!("CARGO_PKG_VERSION"));
    println!("  check: {:.3} ms, format + write: {:.3} ms",
        check_time.as_secs_f64()*1000., stream_time.as_secs_f64()*1000.);
    println!("  IR vector capacities: {ir_storage} bytes (excludes symbols/AST)");
    println!("  streamed bytes: {bytes}; buffer: 65536 bytes");
    print_peak_memory();
    if let Some(limit) = max_peak {
        match peak_resident_bytes() {
            Some(peak) if peak > limit => {
                return Err(format!("memory limit exceeded: peak {peak} > budget {limit}"));
            }
            Some(_) => println!("  memory budget: PASS"),
            None => return Err("cannot enforce memory budget: peak RSS unavailable".into()),
        }
    }
    Ok(())
}

fn bench_stages(args: &[String]) -> Result<(), String> {
    if args.len() < 3 || args.len() > 4 {
        return Err("usage: qrust bench-stages <file.qr> [iterations]".into());
    }
    let repeat: usize = args.get(3).map(|s| s.parse::<usize>())
        .transpose().map_err(|_| "invalid iteration count".to_string())?
        .unwrap_or(200);
    if repeat == 0 || repeat > MAX_BENCH_ITERATIONS {
        return Err("iterations must be within 1..=10000000".into());
    }
    let source = fs::read_to_string(&args[2])
        .map_err(|e| format!("cannot read {}: {e}", args[2]))?;
    let _ = compile(&source).map_err(|e| e.to_string())?;
    let mut stages: [Vec<Duration>; 4] = std::array::from_fn(|_| Vec::with_capacity(repeat));
    let started = Instant::now();
    #[cfg(feature = "alloc-profile")]
    let stages_before = alloc_profile::stage_snapshot();
    #[cfg(feature = "alloc-profile")]
    let (mut allocation_calls, mut allocation_bytes, mut peak_extra_sum, mut peak_extra_max) = (0_u64, 0_u64, 0_u64, 0_u64);
    for _ in 0..repeat {
        #[cfg(feature = "alloc-profile")]
        let alloc_before = alloc_profile::snapshot();
        #[cfg(feature = "alloc-profile")]
        alloc_profile::reset_peak();
        let (program, times) = compile_detailed(black_box(&source))
            .map_err(|e| e.to_string())?;
        #[cfg(feature = "alloc-profile")]
        {
            let alloc_after = alloc_profile::snapshot();
            allocation_calls += alloc_after.calls - alloc_before.calls;
            allocation_bytes += alloc_after.bytes - alloc_before.bytes;
            let peak_extra=alloc_after.peak.saturating_sub(alloc_before.live);
            peak_extra_sum += peak_extra;
            peak_extra_max = peak_extra_max.max(peak_extra);
        }
        black_box(program.instructions.len());
        for (row, duration) in stages.iter_mut().zip([times.lex, times.parse, times.lower, times.sema]) {
            row.push(duration);
        }
    }
    println!("QRust stage benchmark: {} iterations, no QASM or filesystem in timed stages", repeat);
    for (name, samples) in ["Lexer", "Parser", "Lowering", "Semantic Check"].iter().zip(stages.iter_mut()) {
        samples.sort_unstable();
        let middle = samples[repeat / 2];
        let median = if repeat % 2 == 1 { middle.as_secs_f64() }
            else { (middle.as_secs_f64() + samples[repeat / 2 - 1].as_secs_f64()) / 2.0 };
        let total = samples.iter().sum::<Duration>();
        println!("  {name:<15} median {:.3} us  mean {:.3} us  min {:.3} us  max {:.3} us",
            median * 1e6, total.as_secs_f64()*1e6/repeat as f64,
            samples[0].as_secs_f64()*1e6, samples[repeat-1].as_secs_f64()*1e6);
    }
    #[cfg(feature = "alloc-profile")]
    println!("  allocations/compile: {:.2} calls, {:.2} requested bytes (includes reallocations)",
        allocation_calls as f64 / repeat as f64, allocation_bytes as f64 / repeat as f64);
    #[cfg(feature = "alloc-profile")]
    {
        let after = alloc_profile::stage_snapshot();
        for (i, label) in alloc_profile::STAGE_LABELS.iter().enumerate() {
            println!("  stage allocations {label}: {:.2} calls/compile, {:.2} requested bytes/compile",
                after.calls[i].saturating_sub(stages_before.calls[i]) as f64 / repeat as f64,
                after.bytes[i].saturating_sub(stages_before.bytes[i]) as f64 / repeat as f64);
        }
    }
    #[cfg(feature = "alloc-profile")]
    println!("  live-payload peak/compile: {:.2} average bytes above baseline, {} max bytes (not RSS)",
        peak_extra_sum as f64 / repeat as f64, peak_extra_max);
    println!("  wall (includes profiling overhead): {:.3} ms", started.elapsed().as_secs_f64()*1e3);
    Ok(())
}

fn run_region_benchmark(args:&[String])->Result<(),String>{
    if args.len()<3||args.len()>4{return Err("usage: qrust bench-regions <file.qr> [iterations]".into());}
    let iterations:usize=args.get(3).map_or(Ok(1000),|s|s.parse().map_err(|_|"invalid iterations"))?;
    if !(1..=100_000).contains(&iterations){return Err("iterations must be 1..100000".into());}
    let input=Path::new(&args[2]);
    let source=fs::read_to_string(input).map_err(|e|format!("cannot read {}: {e}",input.display()))?;
    let baseline=compile(&source).map_err(|e|e.to_string())?;
    let reference_ir=baseline.instructions.len();
    for _ in 0..10 {black_box(compile(black_box(&source)).map_err(|e|e.to_string())?);}
    let start=Instant::now();
    for _ in 0..iterations {
        let output=compile(black_box(&source)).map_err(|e|e.to_string())?;
        if output.instructions.len()!=reference_ir {return Err("different IR instruction count".into());}
        black_box(output);
    }
    let unprofiled=start.elapsed();
    cfg_nll::begin_region_profile();
    let start=Instant::now();
    for _ in 0..iterations {
        let output=compile(black_box(&source)).map_err(|e|e.to_string())?;
        if output.instructions.len()!=reference_ir {return Err("different IR instruction count".into());}
        black_box(output);
    }
    let profiled=start.elapsed();
    let metrics=cfg_nll::finish_region_profile();
    let us=|d:Duration|d.as_secs_f64()*1e6/iterations as f64;
    println!("QRust {} region-only benchmark, {iterations} compiles; no file I/O or QASM emission",env!("CARGO_PKG_VERSION"));
    println!("  compile unprofiled:       {:.3} us/compile",us(unprofiled));
    println!("  compile with probes:     {:.3} us/compile",us(profiled));
    println!("  lexical binding resolve: {:.3} us/compile",us(metrics.binding));
    println!("  CFG construction:        {:.3} us/compile",us(metrics.cfg_build));
    println!("  backward fixed-point:    {:.3} us/compile",us(metrics.backward_liveness));
    println!("  local region solve:      {:.3} us/compile",us(metrics.region_solve));
    println!("  edge loan + forward:     {:.3} us/compile",us(metrics.edge_events_and_forward));
    println!("  plans/compile: {:.2}, solved CFGs/compile: {:.2}, nodes/compile: {:.2}, loans/compile: {:.2}",
        metrics.plans as f64/iterations as f64,metrics.successful_cfg as f64/iterations as f64,
        metrics.nodes as f64/iterations as f64,metrics.loans as f64/iterations as f64);
    println!("  edges/compile: {:.2}, events/compile: {:.2}, forward steps/compile: {:.2}",
        metrics.edges as f64/iterations as f64,metrics.events as f64/iterations as f64,
        metrics.edge_worklist_steps as f64/iterations as f64);
    println!("  place accesses/compile: {:.2} (candidate writes and moves)",metrics.place_accesses as f64/iterations as f64);
    println!("  stage times include instrumentation overhead; inactive CFGs report 0 for those phases");
    print_peak_memory();
    Ok(())
}

fn usage() -> &'static str {
    "Usage:\n  qrust <file.qr|file.qcu>\n  qrust run <file.qr> [--shots N] [--seed N] [--input N]... [--backend local|qpc] (host I/O: single execution)\n  qrust run-host <file.qr> [--seed N] [--input N]... [--backend local|qpc]\n  qrust check-host <file.qr>\n  qrust bench-host-check <file.qr> [iterations]\n  qrust run-qcu <file.qcu> [--shots N] [--seed N]\n  qrust check <file.qr>\n  qrust build <file.qr> [--skip-unchanged|--force-write] [--sync] [--stream|--string]\n  qrust build-qcu <file.qr> [--sync]\n  qrust inspect-qcu <file.qcu>\n  qrust ir-stats <file.qr>\n  qrust bench-stages <file.qr> [iterations]\n  qrust bench-e2e <file.qr> [repeats] [--emit-profile] [--persistent]\n  qrust bench-io <file.qr> [repeats] [--dir <path>]\n  qrust bench-io-phases <file.qr> [repeats] [--dir <path>]\n  qrust bench-regions <file.qr> [iterations]\n  qrust bench-qasm <file.qr> [repeats]\n  qrust bench-stress <10000|100000|500000> [max_peak_mib]\n  qrust bench-stress-stream <10000|100000|500000> [max_peak_mib]\n  qrust ops\n  qrust capabilities\n  qrust bench <file.qr> [iterations] [--detailed]\n  qrust help"
}

fn execute_host_with_input(source: &str, seed: u64, inputs: Vec<String>, backend:host_runtime::BackendKind) -> Result<host_runtime::RunStats,String> {
    let mut std_console=host_runtime::StdConsole;
    if inputs.is_empty() {
        host_runtime::execute_with_backend(source,&mut std_console,seed,backend)
    } else {
        let mut console=host_runtime::InputConsole::new(&mut std_console, inputs);
        host_runtime::execute_with_backend(source,&mut console,seed,backend)
    }
}

fn run_local(args:&[String],compiled:bool)->Result<(),String>{
    let command=if compiled{"run-qcu"}else{"run"};
    let extension=if compiled{"qcu"}else{"qr"};
    if args.len()<3 || (args.len()-3)%2!=0 || args.len()>133 {
        return Err(format!("usage: qrust {command} <file.{extension}> [--shots N] [--seed N]"));
    }
    let mut shots=1024usize;
    let mut seed=SystemTime::now().duration_since(UNIX_EPOCH)
        .map_or(1,|d|d.as_nanos() as u64) ^ u64::from(std::process::id());
    let mut seen_shots=false;let mut seen_seed=false;
    let mut inputs: Vec<String> = Vec::new();
    let mut backend=host_runtime::BackendKind::Local;
    for pair in args[3..].chunks_exact(2){
        match pair[0].as_str(){
            "--shots" if !seen_shots=>{
                shots=pair[1].parse().map_err(|_|"shots must be a positive integer")?;
                seen_shots=true;
            },
            "--seed" if !seen_seed=>{
                seed=pair[1].parse().map_err(|_|"seed must be a non-negative u64 integer")?;
                seen_seed=true;
            },
            "--backend" if !compiled=>{backend=host_runtime::BackendKind::parse(&pair[1])?;},
            "--input" if !compiled && inputs.len()<64=>{
                let _:i64=pair[1].parse().map_err(|_|"--input expects an i64 integer")?;
                inputs.push(pair[1].clone());
            },
            _=>return Err(format!("usage: qrust {command} <file.{extension}> [--shots N] [--seed N]")),
        }
    }
    let path=Path::new(&args[2]);
    if !path.extension().and_then(|s|s.to_str()).is_some_and(|s|s.eq_ignore_ascii_case(extension)){
        return Err(format!("{command} expects a .{extension} file"));
    }
    let program=if compiled{
        let size=fs::metadata(path).map_err(|e|format!("cannot stat {}: {e}",path.display()))?.len();
        if size>64*1024*1024{return Err("QCU file exceeds 64 MiB local runner limit".into());}
        let data=fs::read(path).map_err(|e|format!("cannot read {}: {e}",path.display()))?;
        qcu::decode(&data)?
    }else{
        let source=fs::read_to_string(path).map_err(|e|format!("cannot read {}: {e}",path.display()))?;
        if host_runtime::is_host_source(&source) {
            if seen_shots && shots!=1{return Err("host programs run once; omit --shots or set --shots 1".into());}
            let stats=execute_host_with_input(&source,seed,inputs,backend)
                .map_err(|e|format!("{}: {e}",path.display()))?;
            let _=(stats.executed_steps,stats.allocated_qubits,stats.measurements);
            return Ok(());
        }
        if backend!=host_runtime::BackendKind::Local{return Err("--backend qpc requires a hybrid program and an installed hardware adapter".into());}
        if !inputs.is_empty(){return Err("--input is only valid for hybrid host programs".into());}
        compile(&source).map_err(|e|format!("{}:{e}",path.display()))?
    };
    let output=local_sim::simulate(&program,shots,seed)?;
    println!("QRust local simulation (not QPU execution)");
    println!("  file: {}",path.display());
    println!("  qubits: {}, classical bits: {}, IR instructions: {}",
        program.qubits,program.bits,program.instructions.len());
    println!("  shots: {}, seed: {}",output.shots,seed);
    if program.bits==0 {println!("  classical measurement results: none");}
    else {println!("  measurement results (c[{}]..c[0]):",program.bits-1);}
    for (bits,count) in output.histogram {
        println!("    {bits:<20} {count:>6} ({:.2}%)",100.0*count as f64/shots as f64);
    }
    Ok(())
}

fn run_host(args:&[String],check_only:bool)->Result<(),String>{
    let command=if check_only{"check-host"}else{"run-host"};
    if args.len()<3 || (args.len()-3)%2!=0 || args.len()>133 || (check_only && args.len()!=3){
        return Err(format!("usage: qrust {command} <file.qr>{}",if check_only{""}else{" [--seed N] [--input N]... [--backend local|qpc]"}));
    }
    let path=Path::new(&args[2]);
    if !path.extension().and_then(|s|s.to_str()).is_some_and(|s|s.eq_ignore_ascii_case("qr")){
        return Err(format!("{command} expects a .qr file"));
    }
    let src=fs::read_to_string(path).map_err(|e|format!("cannot read {}: {e}",path.display()))?;
    if check_only{
        host_runtime::check_source(&src).map_err(|e|format!("{}: {e}",path.display()))?;
        println!("Hybrid static MIR/CFG ownership check OK: {}. Runtime checks remain active; unsupported Rust features are not certified.",path.display());
        return Ok(());
    }
    let mut seed=SystemTime::now().duration_since(UNIX_EPOCH).map_or(1,|d|d.as_nanos() as u64);
    let mut seen_seed=false;
    let mut inputs:Vec<String>=Vec::new();
    let mut backend=host_runtime::BackendKind::Local;
    for pair in args[3..].chunks_exact(2){
        match pair[0].as_str(){
            "--seed" if !seen_seed=>{
                seed=pair[1].parse::<u64>().map_err(|_|"seed must be a non-negative u64")?;
                seen_seed=true;
            },
            "--backend"=>{backend=host_runtime::BackendKind::parse(&pair[1])?;},
            "--input" if inputs.len()<64=>{
                let _:i64=pair[1].parse().map_err(|_|"--input expects an i64 integer")?;
                inputs.push(pair[1].clone());
            },
            _=>return Err(format!("usage: qrust {command} <file.qr> [--seed N] [--input N]... [--backend local|qpc]")),
        }
    }
    let stats=execute_host_with_input(&src,seed,inputs,backend).map_err(|e|format!("{}: {e}",path.display()))?;
    let _=(stats.executed_steps,stats.allocated_qubits,stats.measurements);
    Ok(())
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("help" | "--help" | "-h") if args.len() == 2 => {
            println!("{}", usage());
            Ok(())
        }
        Some(file) if args.len()==2 && Path::new(file).extension().and_then(|ext|ext.to_str()).is_some_and(|s|s.eq_ignore_ascii_case("qr")) => {
            run_local(&[args[0].clone(),String::from("run"),args[1].clone()],false)
        },
        Some(file) if args.len()==2 && Path::new(file).extension().and_then(|ext|ext.to_str()).is_some_and(|s|s.eq_ignore_ascii_case("qcu")) => {
            run_local(&[args[0].clone(),String::from("run-qcu"),args[1].clone()],true)
        },
        Some("run") => run_local(&args,false),
        Some("bench-host-check") if (3..=4).contains(&args.len()) => {
            let source=fs::read_to_string(&args[2]).map_err(|e|format!("cannot read {}: {e}",args[2]))?;
            let iterations=if args.len()==4{args[3].parse::<usize>().map_err(|_|"invalid iteration count")?}else{100};
            let (avg,p50,p90)=host_runtime::bench_static(&source,iterations)?;
            println!("QRust hybrid MIR+CFG/NLL benchmark (parse excluded, no QPU or file I/O)");
            println!("  runs: {iterations}");
            println!("  mean:   {avg:.3} us/check");
            println!("  median: {p50:.3} us/check");
            println!("  p90:    {p90:.3} us/check");
            Ok(())
        },
        Some("run-host") => run_host(&args,false),
        Some("check-host") => run_host(&args,true),
        Some("run-qcu") => run_local(&args,true),
        Some("build-qcu") if (args.len() == 3 || (args.len() == 4 && args[3] == "--sync")) => {
            let input = Path::new(&args[2]);
            let source = fs::read_to_string(input)
                .map_err(|e| format!("cannot read {}: {e}", input.display()))?;
            if host_runtime::is_host_source(&source){
                return Err("hybrid host I/O is not representable in QCU (pure quantum instruction packet)".into());
            }
            let program = compile(&source)
                .map_err(|e| format!("{}:{e}", input.display()))?;
            let bytes = qcu::encode(&program)?;
            let dest = input.with_extension("qcu");
            atomic_qasm::write_bytes_atomic(&bytes, &dest, args.len() == 4)
                .map_err(|e| format!("cannot safely write {}: {e}", dest.display()))?;
            println!("Compiled QCU interchange ({} instructions, {} bytes): {}",
                program.instructions.len(), bytes.len(), dest.display());
            Ok(())
        }
        Some("inspect-qcu") if args.len() == 3 => {
            let input = Path::new(&args[2]);
            let bytes = fs::read(input)
                .map_err(|e| format!("cannot read {}: {e}", input.display()))?;
            let program = qcu::decode(&bytes)?;
            print!("{}", qcu::describe(&program));
            println!("Packet validated: {} bytes", bytes.len());
            Ok(())
        }
        Some("bench-stages") => bench_stages(&args),
        Some("bench-e2e") => run_e2e_benchmark(&args),
        Some("bench-io") => run_io_benchmark(&args),
        Some("bench-io-phases") => io_064::run_io_phases(&args),
        Some("bench-regions") => run_region_benchmark(&args),
        Some("bench-qasm") => run_qasm_benchmark(&args),
        Some("bench-stress") => run_stress_benchmark(&args),
        Some("bench-stress-stream") => run_stream_stress(&args),
        Some("capabilities" | "features") if args.len() == 2 => {
            println!("QRust {} language surface revision {}", env!("CARGO_PKG_VERSION"), surface::SURFACE_REVISION);
            for (name, description) in surface::CAPABILITIES {
                println!("  {name:<20} {description}");
            }
            println!("  unsupported: Rust std, traits/impl, runtime structs/enums, async/await execution, general returns, runtime integer arithmetic, loop labels");
            Ok(())
        }
        Some("ops") if args.len() == 2 => {
            println!("QRust Core {} — gate syntax: gate(angle1, ..., qubit1, ...)", env!("CARGO_PKG_VERSION"));
            for gate in sema::STANDARD_GATES {
                println!("  {:<9} {} angle(s), {} qubit(s) -> {}", gate.name, gate.parameters, gate.qubits, gate.qasm);
            }
            println!("  extended rotations (lowered to stdgates.inc):");
            for gate in sema::EXTENDED_GATES {
                println!("  {:<9} {} angle(s), {} qubit(s) -> stdgates decomposition", gate.name, gate.parameters, gate.qubits);
            }
            println!("  qubit() -> Qubit");
            println!("  measure(q) -> Bit (consumes handle)");
            println!("  measure_keep(q) -> Bit (retains handle)");
            println!("  measure_into(mutable_bit, live_qubit) -> update an existing Bit without consuming its qubit");
            println!("  reset(q), barrier(q1, ...) ");
            println!("  aliases: i=id, cnot=cx, toffoli=ccx, fredkin=cswap, phase/u1=p, cphase=cp");
            println!("  legacy compatibility: CX, u2, u3 are separate phase-sensitive gates");
            println!("  scalar operators: + - * / %; comparisons: == != < <= > >=; logical: ! && ||");
            println!("  constants: pi tau e true false; let/const name[: Float|Bool|Qubit|Bit] = expr;");
            println!("  language core: fn name(q: &mut Qubit, theta: Float) {{ ... }}; fn main() {{ ... }}");
            println!("  compile-time if/else, match, for a..b / a..=b, while, loop, break, continue");
            println!("  compile-time scalar inference: let x=...; += -= *= /= %= on Float");
            println!("  exact typed static integers: let n: i64/u64 = value; checked operations, overflow diagnostics");
            println!("  static structs: struct P {{ angle: i64 }}; let p: P = P {{ angle: 4 }}; p.angle");
            println!("  fieldless enums: enum Axis {{ X,Y }}; let axis: Axis = Axis::Y; compile-time match");
            println!("  runtime if/else on Bit, runtime while with per-path feedback");
            println!("  compile-time safety: static_assert, static_assert_eq, static_assert_ne, static_assert_live, static_assert_distinct");
            println!("  not implemented: runtime qubit moves/allocations, mutable runtime Floats, function returns, dynamic registers");
            println!("  math functions (arity):");
            for (name, arity) in math::FUNCTIONS { println!("    {name:<12} {arity}"); }
            println!("  aliases: arcsin, arccos, arctan, log=ln, ceiling=ceil, power=pow, deg2rad, rad2deg");
            Ok(())
        }
        Some(command @ ("check" | "build" | "bench" | "ir-stats")) if args.len() >= 3 &&
            ((command == "bench" && args.len() <= 5) ||
             (command == "build" && args.len() <= 6) ||
             (command != "bench" && command != "build" && args.len() == 3)) => {
            let source_path = Path::new(&args[2]);
            let source = fs::read_to_string(source_path)
                .map_err(|error| format!("cannot read {}: {error}", source_path.display()))?;
            if host_runtime::is_host_source(&source){
                if command == "check" {
                    host_runtime::check_source(&source)
                        .map_err(|e|format!("{}: {e}",source_path.display()))?;
                    println!("Hybrid static MIR/CFG ownership check OK (restricted host subset); runtime checks remain active.");
                    return Ok(());
                }
                return Err("host I/O programs cannot be emitted as pure quantum QASM/QCU; use 'run' or 'run-host'".into());
            }
            if command == "bench" {
                let options = &args[3..];
                let detailed = options.iter().any(|arg| arg == "--detailed");
                let count_arguments: Vec<&String> = options.iter().filter(|arg| arg.as_str() != "--detailed").collect();
                if count_arguments.len() + (if detailed { 1 } else { 0 }) != options.len() || count_arguments.len() > 1 {
                    return Err("usage: qrust bench <file.qr> [iterations] [--detailed]".into());
                }
                let repeats: usize = match count_arguments.first() {
                    Some(arg) => arg.parse().map_err(|_| "iterations must be a positive integer".to_string())?,
                    None => 1000,
                };
                if repeats == 0 || repeats > MAX_BENCH_ITERATIONS {
                    return Err(format!("iterations must be between 1 and {MAX_BENCH_ITERATIONS}"));
                }
                let program = compile(&source).map_err(|error| format!("{}:{error}", source_path.display()))?;
                let gate_count = program.instructions.len();
                black_box(&program);
                if detailed {
                    let mut totals = StageTimes::default();
                    let started_all = Instant::now();
                    for _ in 0..repeats {
                        let (compiled, times) = compile_detailed(black_box(&source))
                            .map_err(|error| format!("{}:{error}", source_path.display()))?;
                        totals.lex += times.lex;
                        totals.parse += times.parse;
                        totals.lower += times.lower;
                        totals.sema += times.sema;
                        let started = Instant::now();
                        let qasm = sema::emit_qasm(black_box(&compiled));
                        black_box(qasm);
                        totals.emit += started.elapsed();
                    }
                    let wall = started_all.elapsed();
                    let checks = totals.lex + totals.parse + totals.lower + totals.sema;
                    println!("Detailed benchmark: {repeats} full pipelines, {gate_count} instructions/compile");
                    println!("Parse + check stages: {:.3} ms ({:.2} us/compile)",
                        checks.as_secs_f64() * 1_000.0, checks.as_secs_f64() * 1_000_000.0 / repeats as f64);
                    print_stage("Lexer", totals.lex, repeats, checks);
                    print_stage("Parser", totals.parse, repeats, checks);
                    print_stage("Lowering", totals.lower, repeats, checks);
                    print_stage("Semantic check", totals.sema, repeats, checks);
                    println!("  {name:<15} {ms:>10.3} ms (excluded from check)", name="QASM emission", ms=totals.emit.as_secs_f64()*1_000.0);
                    println!("Total wall-clock: {:.3} ms (includes profiler overhead)", wall.as_secs_f64()*1_000.0);
                    println!("--detailed adds clock reads and QASM emission; compare ordinary 'bench' for regression tracking.");
                } else {
                    let started = Instant::now();
                    for _ in 0..repeats {
                        let compiled = compile(black_box(&source))
                            .map_err(|error| format!("{}:{error}", source_path.display()))?;
                        black_box(compiled);
                    }
                    let seconds = started.elapsed().as_secs_f64();
                    println!("{} parses + semantic checks in {:.3} ms", repeats, seconds * 1_000.0);
                    println!("{:.1} us per compile; {:.0} checked IR instructions/s (for this file)",
                        seconds * 1_000_000.0 / repeats as f64,
                        (repeats as f64 * gate_count as f64) / seconds.max(f64::MIN_POSITIVE));
                    println!("Benchmark excludes file I/O, QASM emission, QPU execution; use --release for meaningful numbers.");
                }
                return Ok(());
            }
            let program = compile(&source)
                .map_err(|error| format!("{}:{error}", source_path.display()))?;
            if command == "ir-stats" {
                println!("QRust Typed IR {}", env!("CARGO_PKG_VERSION"));
                println!("  instructions: {} ({} bytes each)", program.instructions.len(), std::mem::size_of::<ir::Instruction>());
                println!("  qubits: {}; bits: {}", program.qubits, program.bits);
                println!("  angle pool: {} f64 values", program.angles.len());
                println!("  barrier operand pool: {} qubit IDs", program.barrier_qubits.len());
                println!("  runtime branches: {}", program.instructions.iter()
                    .filter(|i| matches!(i.opcode, ir::OpCode::IfBit)).count());
                println!("  runtime loops: {}", program.instructions.iter()
                    .filter(|i| matches!(i.opcode, ir::OpCode::WhileBit)).count());
                println!("  in-place measurements: {}", program.instructions.iter()
                    .filter(|i| matches!(i.opcode, ir::OpCode::MeasureInto)).count());
                println!("  IR storage capacity: {} bytes (excludes symbol tables/AST)", program.estimated_storage_bytes());
            } else if command == "check" {
                println!("OK: {} qubits, {} classical bits, {} IR instructions",
                    program.qubits, program.bits, program.instructions.len());
            } else {
                let options = &args[3..];
                let valid = ["--skip-unchanged", "--force-write", "--sync", "--stream", "--string"];
                if options.iter().any(|o| !valid.contains(&o.as_str()))
                    || options.iter().any(|o| options.iter().filter(|x| *x == o).count() != 1)
                    || (options.contains(&"--stream".to_owned()) && options.contains(&"--string".to_owned()))
                    || (options.contains(&"--string".to_owned()) && options.contains(&"--skip-unchanged".to_owned()))
                    || (options.contains(&"--force-write".to_owned()) && options.contains(&"--skip-unchanged".to_owned()))
                {
                    return Err("usage: qrust build <file.qr> [--skip-unchanged|--force-write] [--sync] [--stream|--string]".into());
                }
                let output_path = source_path.with_extension("qasm");
                if options.iter().any(|o| o == "--string") {
                    let qasm = sema::emit_qasm(&program);
                    let sync = options.iter().any(|o| o == "--sync");
                    atomic_qasm::write_string_atomic(&qasm, &output_path, sync)
                        .map_err(|error| format!("cannot safely write {}: {error}", output_path.display()))?;
                    println!("Compiled (legacy String, safely replaced): {}", output_path.display());
                } else {
                    let skip = !options.iter().any(|o| o == "--force-write");
                    let sync = options.iter().any(|o| o == "--sync");
                    let result = atomic_qasm::write_qasm_atomic(&program, &output_path, skip, sync)
                        .map_err(|error| format!("cannot safely write {}: {error}", output_path.display()))?;
                    match result {
                        atomic_qasm::WriteOutcome::Unchanged { .. } =>
                            println!("Unchanged: {}", output_path.display()),
                        atomic_qasm::WriteOutcome::Compiled { bytes } =>
                            println!("Compiled (streamed {bytes} bytes, safely replaced): {}", output_path.display()),
                    }
                }
            }
            Ok(())
        }
        _ => Err(usage().to_string()),
    }
}

fn main() {
    if let Err(message) = run() {
        eprintln!("{message}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn error(source: &str) -> String {
        compile(source).unwrap_err().message
    }

    #[test]
    fn surface_registry_is_consistent() {
        assert_eq!(surface::SURFACE_REVISION, 5);
        assert!(surface::reserved_identifier("match"));
        assert!(surface::reserved_identifier("__qrust_internal"));
        assert!(!surface::reserved_identifier("custom_pulse"));
        assert!(surface::CAPABILITIES.iter().any(|(name, _)| *name == "static-match"));
        assert!(surface::CAPABILITIES.iter().any(|(name, _)| *name == "static-loop-control"));
        assert!(surface::CAPABILITIES.iter().any(|(name, _)| *name == "expr-arena-fast"));
        assert!(surface::CAPABILITIES.iter().any(|(name, _)| *name == "async-ir-preview"));
        let mut unique = std::collections::HashSet::new();
        for (name, description) in surface::CAPABILITIES {
            assert!(!name.is_empty() && !description.is_empty());
            assert!(unique.insert(*name), "duplicate capability: {name}");
        }

        assert_eq!(surface::declaration_type("bool"), Some(syntax::Type::Bool));
        assert_eq!(surface::scalar_parameter_type("f64"), Some(syntax::ParamType::Float));
        assert_eq!(surface::declaration_type("usize"), None);
    }

    #[test]
    fn rust_placeholder_infers_static_float_and_bool() {
        let a="let q: _ = qubit();let mut angle: _ = 1;let flag: _ = angle > 0;if flag {angle += 2;}rz(angle,q);";
        let b="let q=qubit();rz(3,q);";
        assert_eq!(sema::emit_qasm(&compile(a).unwrap()), sema::emit_qasm(&compile(b).unwrap()));
    }

    #[test]
    fn rust_placeholder_infers_mutable_measurement_bit() {
        let a="let q: _ = qubit();let mut b: _ = measure_keep(q);measure_into(b,q);";
        let program=compile(a).unwrap();
        assert_eq!(program.qubits,1);
        assert!(program.bits >= 1);
    }

    #[test]
    fn inferred_values_retain_strict_types_and_linear_safety() {
        assert!(error("let q=qubit();let x: _=true;rx(x,q);").contains("numeric") ||
            error("let q=qubit();let x: _=true;rx(x,q);").contains("Float"));
        let message=error("let q: _=qubit();let p: _=q;h(q);");
        assert!(message.contains("consumed") || message.contains("moved"));
        assert!(error("let x: mystery = 1;").contains("unknown type"));
    }

    #[test]
    fn static_for_break_matches_manual_unroll() {
        let a = "let q=qubit();for i in 0..10 {if i==3 {break;} rx(i,q);}let b=measure(q);";
        let b = "let q=qubit();rx(0,q);rx(1,q);rx(2,q);let b=measure(q);";
        assert_eq!(sema::emit_qasm(&compile(a).unwrap()), sema::emit_qasm(&compile(b).unwrap()));
    }

    #[test]
    fn static_for_continue_rechecks_next_iteration() {
        let a = "let q=qubit();for i in 0..6 {if i%2==0 {continue;} rx(i,q);}let b=measure(q);";
        let b = "let q=qubit();rx(1,q);rx(3,q);rx(5,q);let b=measure(q);";
        assert_eq!(sema::emit_qasm(&compile(a).unwrap()), sema::emit_qasm(&compile(b).unwrap()));
    }

    #[test]
    fn static_while_break_and_continue_are_compile_time_only() {
        let a = "let q=qubit();let mut i=0;while true {i+=1;if i==2 {continue;}if i==4 {break;}rx(i,q);}let b=measure(q);";
        let b = "let q=qubit();rx(1,q);rx(3,q);let b=measure(q);";
        assert_eq!(sema::emit_qasm(&compile(a).unwrap()), sema::emit_qasm(&compile(b).unwrap()));
    }

    #[test]
    fn static_loop_uses_mutable_type_inference() {
        let a = "let q=qubit();let mut index=0;let mut skip=true;loop {index+=1;if skip {skip=false;continue;}if index==4 {break;}rx(index,q);}static_assert_eq(index,4);let b=measure(q);";
        let b = "let q=qubit();rx(2,q);rx(3,q);let b=measure(q);";
        assert_eq!(sema::emit_qasm(&compile(a).unwrap()), sema::emit_qasm(&compile(b).unwrap()));
    }

    #[test]
    fn nested_static_loops_break_only_the_innermost() {
        let a = "let q=qubit();for i in 0..3 {for j in 0..3 {if j==1 {break;}rx(i,q);}z(q);}";
        let b = "let q=qubit();rx(0,q);z(q);rx(1,q);z(q);rx(2,q);z(q);";
        assert_eq!(sema::emit_qasm(&compile(a).unwrap()), sema::emit_qasm(&compile(b).unwrap()));
    }

    #[test]
    fn static_match_and_nested_blocks_propagate_loop_signals() {
        let a = "let q=qubit();for i in 0..4 {match i {1=>{{continue;}},2=>{{break;}},_=>{}}rx(i,q);}";
        let b = "let q=qubit();rx(0,q);";
        assert_eq!(sema::emit_qasm(&compile(a).unwrap()), sema::emit_qasm(&compile(b).unwrap()));
    }

    #[test]
    fn break_continue_outside_static_loops_are_diagnosed() {
        assert!(error("break;").contains("outside a static loop"));
        assert!(error("continue;").contains("outside a static loop"));
        assert!(error("fn main(){break;}").contains("outside a static loop"));
        assert!(error("let q=qubit();if true {continue;}").contains("outside a static loop"));
    }

    #[test]
    fn static_loop_callee_cannot_break_callers_loop() {
        let source = "fn bad() {break;} fn main() {let q=qubit();for i in 0..3 {bad();}h(q);}";
        assert!(error(source).contains("outside a static loop"));
    }

    #[test]
    fn runtime_feedback_rejects_unsupported_break_continue() {
        let a = "let q=qubit();let mut b=measure_keep(q);while b {break;}";
        assert!(error(a).contains("runtime control supports only"));
        let b = "let q=qubit();let mut b=measure_keep(q);while b {continue;}";
        assert!(error(b).contains("runtime control supports only"));
    }

    #[test]
    fn loop_control_does_not_weaken_quantum_liveness() {
        let a = "let q=qubit();loop {let b=measure(q);break;}h(q);";
        let e=error(a);
        assert!(e.contains("consumed") || e.contains("moved"));
        let safe = "let q=qubit();loop {break;let b=measure(q);}h(q);";
        assert_eq!(compile(safe).unwrap().instructions.len(), 1);
    }

    #[test]
    fn static_loop_guard_rejects_missing_break() {
        assert!(error("loop {}").contains("100000 iterations"));
    }

    #[test]
    fn loop_control_keywords_are_reserved() {
        assert!(error("let loop=3;").contains("reserved"));
        assert!(error("let break=3;").contains("reserved"));
        assert!(error("let continue=3;").contains("reserved"));
    }

    #[test]
    fn loop_control_preserves_per_iteration_lexical_scopes() {
        let source="let q=qubit();for i in 0..3 {let local=i; if i==1 {continue;}}rz(local,q);";
        let e=error(source);
        assert!(e.contains("unknown") || e.contains("variable"));
    }

    #[test]
    fn no_runtime_loop_opcodes_added_for_static_loop() {
        let source="let q=qubit();let mut n=0;loop {if n==3 {break;}h(q);n+=1;}";
        let program=compile(source).unwrap();
        assert_eq!(program.instructions.len(), 3);
        let text=sema::emit_qasm(&program);
        assert!(!text.contains("while ("));
    }

    #[test]
    fn rust_inclusive_ranges_match_exclusive_output() {
        let inclusive = compile("let q=qubit(); for i in 0..=3 {rx(i*pi/4,q);} let b=measure(q);").unwrap();
        let exclusive = compile("let q=qubit(); for i in 0..4 {rx(i*pi/4,q);} let b=measure(q);").unwrap();
        assert_eq!(sema::emit_qasm(&inclusive), sema::emit_qasm(&exclusive));
    }

    #[test]
    fn inclusive_empty_range_and_boundaries() {
        let p=compile("let q=qubit();for i in 4..=3 {x(q);} h(q);").unwrap();
        assert_eq!(p.instructions.len(),1);
        let p=compile("let q=qubit();for i in 100000..=100000 {h(q);}").unwrap();
        assert_eq!(p.instructions.len(),1);
        assert!(error("let q=qubit();for i in 0..=100000 {h(q);}").contains("100000 iterations"));
    }

    #[test]
    fn compound_assigns_match_desugared_expressions() {
        let a="let q=qubit();let mut x:f64=10;x+=3;x-=2;x*=4;x/=2;x%=7;rz(x,q);";
        let b="let q=qubit();let mut x:f64=10;x=x+3;x=x-2;x=x*4;x=x/2;x=x%7;rz(x,q);";
        assert_eq!(sema::emit_qasm(&compile(a).unwrap()), sema::emit_qasm(&compile(b).unwrap()));
    }

    #[test]
    fn compound_assigns_keep_type_and_domain_checks() {
        assert!(error("let q=qubit();let a=2;a+=1;").contains("immutable"));
        assert!(error("let mut x=3;x/=0;").contains("zero"));
        assert!(error("let mut x=3;x%=0;").contains("zero"));
        assert!(error("let mut b:bool=true;b+=1;").contains("Float") ||
            error("let mut b:bool=true;b+=1;").contains("numeric"));
    }

    #[test]
    fn static_match_bool_is_exhaustive_without_wildcard() {
        let a=compile("let q=qubit(); match true {true => {x(q);},false => {z(q);}} ").unwrap();
        let b=compile("let q=qubit(); x(q);").unwrap();
        assert_eq!(sema::emit_qasm(&a), sema::emit_qasm(&b));
    }

    #[test]
    fn static_match_integer_selects_correct_arm() {
        let a=compile("let q=qubit();match -1 {0=>{h(q);},-1=>{z(q);},_=>{x(q);}} ").unwrap();
        let b=compile("let q=qubit();z(q);").unwrap();
        assert_eq!(sema::emit_qasm(&a), sema::emit_qasm(&b));
    }

    #[test]
    fn static_match_checks_all_patterns_and_exhaustiveness() {
        assert!(error("match true {true => {} }").contains("non-exhaustive"));
        assert!(error("match 1 {1 => {} }").contains("non-exhaustive"));
        assert!(error("match true {true=>{},true=>{},false=>{}}").contains("duplicate"));
        assert!(error("match 1 {1=>{},1=>{},_=>{}}").contains("duplicate"));
        assert!(error("match false {_=>{},false=>{}}").contains("must be last"));
        assert!(error("match true {0=>{},_=>{}}").contains("type"));
        assert!(error("match 1.5 {_=>{}}").contains("integer"));
    }

    #[test]
    fn static_match_does_not_validate_untaken_body() {
        let p=compile("let q=qubit();match 1 {0=>{h(unknown);},1=>{x(q);},_=>{z(q);}}").unwrap();
        assert_eq!(p.instructions.len(),1);
    }

    #[test]
    fn static_match_rejects_runtime_measurement_bit() {
        let message = error("let q=qubit();let b=measure_keep(q);match b {true=>{x(q);},false=>{z(q);}}");
        assert!(message.contains("compile-time"));
    }

    #[test]
    fn static_match_preserves_qubit_liveness() {
        let message = error("let q=qubit();let b=measure(q);match true {true=>{h(q);},false=>{}}");
        assert!(message.contains("consumed") || message.contains("moved"));
    }

    #[test]
    fn static_match_keeps_lexical_scope() {
        let msg=error("let q=qubit();match 1 {1=>{let x=5;},_=>{}} rz(x,q);");
        assert!(msg.contains("unknown") || msg.contains("variable"));
    }

    #[test]
    fn new_language_keywords_cannot_be_declarations() {
        assert!(error("let match = 3;").contains("reserved"));
        assert!(error("fn match() {} fn main() {}").contains("reserved"));
    }

    #[test]
    fn modern_surface_example_is_compilable() {
        let source=include_str!("../examples/rust_surface_0512.qr");
        let p=compile(source).unwrap();
        assert_eq!(p.qubits,1);
        assert_eq!(p.bits,1);
        assert_eq!(p.instructions.len(),5); //four gates and one measurement
    }

    #[test]
    fn bell_pair_compiles() {
        let program = compile("let a = qubit(); let b = qubit(); h(a); cx(a,b); let x = measure(a); let y = measure(b);").unwrap();
        let qasm = sema::emit_qasm(&program);
        assert!(qasm.contains("cx q[0], q[1];"));
        assert!(qasm.contains("c[1] = measure q[1];"));
        assert_eq!(program.instructions.len(), 4);
    }

    #[test]
    fn all_standard_gates_compile_and_emit() {
        for gate in sema::STANDARD_GATES {
            let mut src = String::from("let a = qubit(); let b = qubit(); let c = qubit();\n");
            let mut args: Vec<&str> = vec!["pi / 4"; gate.parameters];
            args.extend(["a", "b", "c"].into_iter().take(gate.qubits));
            src.push_str(&format!("{}({});", gate.name, args.join(", ")));
            let program = compile(&src).unwrap_or_else(|e| panic!("{} failed: {}", gate.name, e));
            let qasm = sema::emit_qasm(&program);
            assert!(qasm.contains(gate.qasm), "{gate:?} -> {qasm}");
            assert_eq!(program.instructions.len(), 1, "{}", gate.name);
        }
    }

    #[test]
    fn all_gates_check_argument_counts() {
        for gate in sema::STANDARD_GATES {
            let src = format!("{}();", gate.name);
            if gate.parameters + gate.qubits > 0 {
                assert!(error(&src).contains("requires"), "{src}");
            }
        }
    }

    #[test]
    fn rejects_same_cnot_qubit() {
        assert!(error("let a = qubit(); cx(a,a);").contains("distinct"));
    }

    #[test]
    fn rejects_same_qubit_in_other_multi_gates() {
        assert!(error("let a = qubit(); let b = qubit(); ccx(a,b,a);").contains("distinct"));
        assert!(error("let a = qubit(); swap(a,a);").contains("distinct"));
        assert!(error("let a = qubit(); barrier(a,a);").contains("distinct"));
    }

    #[test]
    fn rejects_use_after_measure() {
        assert!(error("let a = qubit(); let x = measure(a); h(a);").contains("consumed"));
    }

    #[test]
    fn measurement_can_explicitly_keep_handle() {
        let p = compile("let a = qubit(); let b = measure_keep(a); reset(a); h(a); let c = measure(a);").unwrap();
        assert_eq!(p.qubits, 1);
        assert_eq!(p.bits, 2);
        assert!(sema::emit_qasm(&p).contains("reset q[0];"));
    }

    #[test]
    fn rejects_use_after_move() {
        assert!(error("let a = qubit(); let b = a; h(a);").contains("moved"));
    }

    #[test]
    fn move_works_without_copying() {
        let program = compile("let a = qubit(); let b = a; h(b); let x = measure(b);").unwrap();
        assert_eq!(program.qubits, 1);
    }

    #[test]
    fn rejects_classical_bits_as_qubits() {
        assert!(error("let a = qubit(); let x = measure(a); h(x);").contains("classical bit"));
    }

    #[test]
    fn rejects_syntax_errors() {
        assert!(error("let a = qubit()").contains("expected ';'"));
        assert!(error("let a = qubit(); h(,a);").contains("expected expression"));
    }

    #[test]
    fn scalar_arithmetic_and_builtin_functions() {
        let p = compile("let a=qubit(); let theta = pi / 2; rx(theta, a); ry(sin(pi/2) + pow(2, 3), a); rz(-tau/4, a);").unwrap();
        let qasm = sema::emit_qasm(&p);
        assert!(qasm.contains("rx(1.5707963267948966) q[0];"));
        assert!(qasm.contains("ry(9) q[0];"));
        assert!(qasm.contains("rz(-1.5707963267948966) q[0];"));
    }

    #[test]
    fn scalar_operator_precedence_and_scientific_notation() {
        let p = compile("let a=qubit(); rz((2+3)*1e-2, a); rz(5 % 2, a);").unwrap();
        let qasm = sema::emit_qasm(&p);
        assert!(qasm.contains("rz(0.05) q[0];"));
        assert!(qasm.contains("rz(1) q[0];"));
    }

    #[test]
    fn rejects_invalid_numeric_expressions() {
        assert!(error("let a=qubit(); rz(1/0, a);").contains("division by zero"));
        assert!(error("let a=qubit(); rz(sqrt(-1), a);").contains("non-finite"));
        assert!(error("let a=qubit(); rz(1e309, a);").contains("finite"));
        assert!(error("let a=qubit(); rz(sin(1,2), a);").contains("requires 1"));
        assert!(error("let a=qubit(); rz(pi, z);").contains("unknown variable"));
    }

    #[test]
    fn aliases_have_standardized_qasm_names() {
        let p = compile("let a=qubit(); let b=qubit(); cnot(a,b); phase(pi/2,a); toffoli(a,b,c);");
        assert!(p.is_err());
        let p = compile("let a=qubit(); let b=qubit(); let c=qubit(); cnot(a,b); phase(pi/2,a); toffoli(a,b,c);").unwrap();
        let qasm = sema::emit_qasm(&p);
        assert!(qasm.contains("cx q[0], q[1];"));
        assert!(qasm.contains("p(1.5707963267948966) q[0];"));
        assert!(qasm.contains("ccx q[0], q[1], q[2];"));
    }

    #[test]
    fn legacy_cx_is_not_silently_rewritten_to_cx() {
        let p = compile("let a=qubit(); let b=qubit(); CX(a,b); cx(a,b);").unwrap();
        let qasm = sema::emit_qasm(&p);
        assert!(qasm.contains("CX q[0], q[1];"));
        assert!(qasm.contains("cx q[0], q[1];"));
    }

    #[test]
    fn constants_and_bits_cannot_be_treated_as_qubits() {
        assert!(error("let a=qubit(); let theta=3; cx(a,theta);").contains("number"));
        assert!(error("let pi = 4;").contains("reserved"));
        assert!(error("let a=qubit(); let bit=measure(a); rx(bit, a);").contains("bit") ||
                error("let a=qubit(); let bit=measure(a); rx(bit, a);").contains("consumed"));
    }

    #[test]
    fn reset_and_barrier_accept_live_qubits() {
        let p = compile("let a=qubit(); let b=qubit(); reset(a); barrier(a,b); h(a);").unwrap();
        let qasm = sema::emit_qasm(&p);
        assert!(qasm.contains("reset q[0];"));
        assert!(qasm.contains("barrier q[0], q[1];"));
    }

    #[test]
    fn comments_are_ignored() {
        let p = compile("// комментарий\nlet a = qubit(); // inline\nh(a);").unwrap();
        assert_eq!(p.instructions.len(), 1);
    }

    #[test]
    fn duplicate_names_rejected() {
        assert!(error("let a=qubit(); let a=qubit();").contains("already declared"));
    }

    #[test]
    fn long_circuit_is_linear_size() {
        let mut src = String::from("let a=qubit();\n");
        for _ in 0..10_000 { src.push_str("h(a);\n"); }
        let program = compile(&src).unwrap();
        assert_eq!(program.instructions.len(), 10_000);
        assert_eq!(program.qubits, 1);
    }

    #[test]
    fn standard_registry_has_consistent_emission() {
        for gate in sema::STANDARD_GATES {
            let mut src = String::from("let a=qubit(); let b=qubit(); let c=qubit();\n");
            let mut args = vec!["pi/3"; gate.parameters];
            args.extend(["a", "b", "c"].iter().copied().take(gate.qubits));
            src.push_str(&format!("{}({});", gate.name, args.join(",")));
            let result = compile(&src).unwrap_or_else(|e| panic!("{}: {}", gate.name, e));
            let qasm = sema::emit_qasm(&result);
            assert!(qasm.contains(gate.qasm), "{} missing in QASM", gate.name);
        }
    }

    #[test]
    fn rotations_are_lowered_to_standard_gates() {
        for gate in sema::EXTENDED_GATES {
            let src = format!("let a=qubit(); let b=qubit(); {}(pi/4, a,b);", gate.name);
            let qasm = sema::emit_qasm(&compile(&src).unwrap());
            assert!(qasm.contains("cx q[0], q[1];"));
            assert!(qasm.contains("rz(0.7853981633974483) q[1];"));
            assert!(!qasm.contains(&format!("{}(", gate.name)));
        }
    }

    #[test]
    fn numeric_functions_have_full_arity_checks() {
        for (name, arity) in math::FUNCTIONS {
            let args = vec!["1"; *arity].join(",");
            let source = format!("let q=qubit(); rz({name}({args}),q);");
            if *name == "acosh" || *name == "atanh" { continue; } //domain-specific tests below
            compile(&source).unwrap_or_else(|e| panic!("{name}: {e}"));
            let wrong = format!("let q=qubit(); rz({name}(),q);");
            assert!(error(&wrong).contains("requires"), "{name}");
        }
    }

    #[test]
    fn math_aliases_and_units() {
        let src = "let q=qubit(); rz(deg2rad(180),q); ry(rad2deg(pi),q); rx(log(exp(1)),q);";
        let qasm = sema::emit_qasm(&compile(src).unwrap());
        assert!(qasm.contains("rx(1) q[0];"));
        assert!(qasm.contains("ry(180) q[0];"));
        assert!(qasm.contains("rz(3.141592653589793) q[0];"));
    }

    #[test]
    fn typed_constant_declarations_and_boolean_logic() {
        let src = "const theta: Float = pi/2; let ok: Bool = (theta > 1.0 && true) || false; let q: Qubit=qubit(); rx(theta, q);";
        let p = compile(src).unwrap();
        assert_eq!(p.qubits, 1);
        assert_eq!(p.instructions.len(), 1);
    }

    #[test]
    fn scalar_precedence_and_short_circuit() {
        compile("const safe: Bool = false && (1/0 > 2); let q=qubit(); rx(1+2*3, q);").unwrap();
        compile("const safe: Bool = true || (1/0 > 2);").unwrap();
        assert!(error("const v = true + 1;").contains("expected Float"));
        assert!(error("const v: Bool = 2;").contains("type mismatch"));
    }

    #[test]
    fn malformed_literals_and_math_domain_errors() {
        assert!(error("let x = 1__000;").contains("numeric separators"));
        assert!(error("let x = 1e+;").contains("exponent digits"));
        assert!(error("let x = log(-1);").contains("non-finite"));
        assert!(error("let x = clamp(2,3,1);").contains("clamp minimum"));
        assert!(error("let x = 1/0;").contains("division by zero"));
        assert!(error("let x = 1 % 0;").contains("remainder by zero"));
    }

    #[test]
    fn comments_typed_bits_and_trailing_commas() {
        let src = "/* nested /* inner */ outer */ let q: Qubit = qubit(); h(q,); let b: Bit = measure(q,);";
        let program = compile(src).unwrap();
        assert_eq!(program.bits, 1);
        assert!(error("/* incomplete").contains("unterminated"));
        assert!(error("const q = qubit();").contains("const declarations require"));
    }

    #[test]
    fn reject_boolean_gate_angles_and_mixed_comparisons() {
        assert!(error("let q=qubit(); rx(true,q);").contains("expected Float"));
        assert!(error("const b = (1 == true);").contains("same type"));
        assert!(error("let q: Bit = qubit();").contains("type mismatch"));
        assert!(error("const theta = true; let q=qubit(); ry(theta,q);").contains("expected Float"));
    }

    #[test]
    fn legacy_gate_semantics_remain_distinct() {
        let qasm = sema::emit_qasm(&compile("let a=qubit(); let b=qubit(); CX(a,b); cx(a,b); u2(0,pi,a); u(0,0,pi,a);").unwrap());
        assert!(qasm.contains("CX q[0], q[1];"));
        assert!(qasm.contains("cx q[0], q[1];"));
        assert!(qasm.contains("u2(0, 3.141592653589793) q[0];"));
        assert!(qasm.contains("U(0, 0, 3.141592653589793) q[0];"));
    }


    #[test]
    fn variables_can_share_gate_names() {
        let p = compile("let q = qubit(); let x: Bit = measure_keep(q); x(q); let y = measure(q);").unwrap();
        assert_eq!(p.qubits, 1);
        assert_eq!(p.bits, 2);
        assert_eq!(p.instructions.len(), 3);
        assert!(sema::emit_qasm(&p).contains("x q[0];"));
    }

    #[test]
    fn variables_can_share_math_function_names() {
        let p = compile("let sin: Float = 2; let q = qubit(); rx(sin(pi/2), q); ry(sin, q);").unwrap();
        let qasm = sema::emit_qasm(&p);
        assert!(qasm.contains("rx(1) q[0];"));
        assert!(qasm.contains("ry(2) q[0];"));
    }

    #[test]
    fn keyword_and_constant_identifiers_remain_reserved() {
        assert!(error("let pi = 1;").contains("reserved"));
        assert!(error("let const = 1;").contains("reserved"));
        assert!(error("let true = 1;").contains("reserved"));
    }

    #[test]
    fn language_main_functions_and_mut_borrows() {
        let src = r#"
            fn prepare(q: &mut Qubit, theta: Float) {
                h(q);
                rz(theta, q);
            }
            fn main() {
                let mut q = qubit();
                prepare(&mut q, pi / 4);
                let b = measure(q);
            }
        "#;
        let p = compile(src).unwrap();
        assert_eq!(p.qubits, 1);
        assert_eq!(p.bits, 1);
        assert_eq!(p.instructions.len(), 3);
        assert!(sema::emit_qasm(&p).contains("rz(0.7853981633974483) q[0];"));
    }

    #[test]
    fn language_forward_declarations() {
        let src = "fn main() { let q = qubit(); ready(&mut q); } fn ready(q: &mut Qubit) { x(q); }";
        assert_eq!(compile(src).unwrap().instructions.len(), 1);
    }

    #[test]
    fn language_blocks_shadow_and_restore_names() {
        let src = "let q=qubit(); { let q=qubit(); x(q); } h(q);";
        let p = compile(src).unwrap();
        let qasm = sema::emit_qasm(&p);
        assert!(qasm.contains("x q[1];"));
        assert!(qasm.contains("h q[0];"));
        assert_eq!(p.qubits, 2);
        assert!(error("{ let q=qubit(); } h(q);").contains("unknown variable"));
    }

    #[test]
    fn language_if_constexpr_and_elseif() {
        let src = "let q=qubit(); const yes=true; if !yes { z(q); } else if 2>1 { h(q); } else { x(q); }";
        let p = compile(src).unwrap();
        assert_eq!(p.instructions.len(), 1);
        assert!(sema::emit_qasm(&p).contains("h q[0];"));
        assert!(error("let q=qubit(); if 1 { h(q); }").contains("compile-time Bool"));
    }

    #[test]
    fn language_for_static_range() {
        let src = "let q=qubit(); for i in 0..8 { rz(i*pi/4, q); }";
        let p = compile(src).unwrap();
        assert_eq!(p.instructions.len(), 8);
        assert!(error("let q=qubit(); for i in 0..100001 { h(q); }").contains("integer"));
    }

    #[test]
    fn language_registers_and_indices() {
        let src = "fn main() { let r=qubits(3); h(r[0]); cx(r[0],r[1]); swap(r[1],r[2]); }";
        let p = compile(src).unwrap();
        assert_eq!(p.qubits, 3);
        assert!(sema::emit_qasm(&p).contains("swap q[1], q[2];"));
        assert!(error("let r=qubits(2); x(r[2]);").contains("out of bounds"));
    }

    #[test]
    fn language_registers_in_bounded_for() {
        let src = "let r=qubits(4); for i in 0..4 { h(r[i]); }";
        let p = compile(src).unwrap();
        assert_eq!(p.qubits, 4);
        assert_eq!(p.instructions.len(), 4);
    }

    #[test]
    fn language_borrow_alias_and_ownership_checks() {
        let f = "fn join(a:&mut Qubit,b:&mut Qubit) { cx(a,b); }";
        let ok = format!("{f} fn main() {{ let a=qubit(); let b=qubit(); join(&mut a,&mut b); }}");
        assert_eq!(compile(&ok).unwrap().instructions.len(), 1);
        let invalid = format!("{f} fn main() {{ let a=qubit(); join(&mut a,&mut a); }}");
        assert!(error(&invalid).contains("alias"));
        assert!(error("fn f(q:&mut Qubit){ measure(q); } fn main(){let q=qubit(); f(&mut q);}")
            .contains("borrowed"));
        assert!(error("fn f(q:&mut Qubit){let alias=q;} fn main(){let q=qubit(); f(&mut q);}")
            .contains("borrowed"));
        assert!(error("fn f(q:&mut Qubit){} fn main(){let n=4;f(&mut n);}")
            .contains("expects a Qubit"));
    }

    #[test]
    fn language_no_capture_of_caller_locals() {
        assert!(error("fn f(q:&mut Qubit){h(other);} fn main(){let q=qubit();let other=qubit();f(&mut q);}")
            .contains("unknown variable"));
    }

    #[test]
    fn language_rejects_recursion_and_dynamic_control() {
        assert!(error("fn main(){ main(); }").contains("depth"));
        assert!(error("let q=qubit(); while 1 { h(q); }").contains("compile-time Bool"));
        assert!(error("return 1;").contains("return values are not supported"));
    }

    #[test]
    fn language_rejects_moved_borrow_and_bad_signature() {
        assert!(error("fn f(q:&mut Qubit){} fn main(){let q=qubit();let y=q;f(&mut q);}")
            .contains("consumed or moved"));
        assert!(error("fn f(q:Bit){}").contains("parameter type"));
        assert!(error("fn main(q:Float){}").contains("cannot accept parameters"));
    }

    #[test]
    fn language_repeated_functions_get_unique_local_names() {
        let src = "fn f(q:&mut Qubit){ let temp=qubit(); h(temp); cx(q,temp); } fn main(){ let a=qubit(); f(&mut a); f(&mut a); }";
        let p = compile(src).unwrap();
        assert_eq!(p.qubits, 3);
        assert_eq!(p.instructions.len(), 4);
    }

    #[test]
    fn language_unused_functions_not_silently_accepted() {
        assert!(error("fn unused(q:&mut Qubit) { h(q); }").contains("never called"));
    }

    #[test]
    fn compiler_marks_legacy_programs_without_second_ast_scan() {
        let src = "let a=qubit(); let b=qubit(); h(a); cx(a,b); let c=measure(a);";
        let tokens = syntax::lex(src).unwrap();
        let parsed = syntax::Parser::new(tokens).parse().unwrap();
        assert!(!parsed.needs_lowering);
        assert_eq!(compile(src).unwrap().instructions.len(), 3);
    }

    #[test]
    fn compiler_marks_all_language_core_syntax() {
        let examples = [
            "{ let q=qubit(); }",
            "fn main() { let q=qubit(); h(q); }",
            "if true { let q=qubit(); }",
            "for i in 0..3 { let q=qubit(); }",
            "let r = qubits(2); h(r[0]);",
            "fn f(q:&mut Qubit) { h(q); } fn main(){ let q=qubit(); f(&mut q); }",
        ];
        for src in examples {
            let parsed = syntax::Parser::new(syntax::lex(src).unwrap()).parse().unwrap();
            assert!(parsed.needs_lowering, "lowering not flagged for: {src}");
            compile(src).unwrap_or_else(|e| panic!("{src}: {e}"));
        }
    }

    #[test]
    fn instrumented_and_normal_compiler_produce_identical_qasm() {
        for src in [
            "let q=qubit(); h(q); let b=measure(q);",
            "let r=qubits(2); for i in 0..2 { h(r[i]); } cx(r[0],r[1]);",
            "fn f(q:&mut Qubit) { rz(pi/2,q); } fn main() { let q=qubit(); f(&mut q); }",
        ] {
            let normal = compile(src).unwrap();
            let (profiled, _) = compile_detailed(src).unwrap();
            assert_eq!(sema::emit_qasm(&normal), sema::emit_qasm(&profiled));
        }
    }

    #[test]
    fn hotfix_internal_names_not_rejected_after_lowering() {
        let source = "fn pulse(q:&mut Qubit) { h(q); } fn main() { let q=qubit(); pulse(&mut q); let b=measure(q); }";
        let program = compile(source).expect("lowered internal __qrust_* declarations must be legal");
        assert_eq!(program.instructions.len(), 2);
        assert!(sema::emit_qasm(&program).contains("h q[0]"));
    }

    #[test]
    fn async_syntax_requires_real_future_lowering() {
        for source in [
            "async fn work() { let q=qubit(); }",
            "async move { let q=qubit(); }",
            "let q=qubit(); let x=q.await;",
            "let q=qubit(); let x=(q).await;",
            "let q=qubit(); let x=await;",
        ] {
            let issue = error(source);
            assert!(issue.contains("async") || issue.contains("await"), "{source}: {issue}");
        }
    }

    #[test]
    fn dense_arena_matches_precedence_and_preserves_errors() {
        let prefix = "1+".repeat(250);
        let source = format!("let q=qubit(); rx({prefix}1*2-3,q);");
        let expected = "let q=qubit(); rx(249,q);";
        let a = compile(&source).unwrap();
        let b = compile(expected).unwrap();
        assert_eq!(sema::emit_qasm(&a), sema::emit_qasm(&b));
        assert_eq!(qcu::encode(&a).unwrap(), qcu::encode(&b).unwrap());
        let bad = format!("let q=qubit(); rx({prefix}1/0,q);");
        assert!(error(&bad).contains("division by zero"));
    }

    #[test]
    fn arena_short_circuit_flag_survives_rewriting() {
        let expression = "true || ".repeat(200) + "false";
        let source = format!("let q=qubit(); if {expression} {{ h(q); }}");
        let parsed = syntax::Parser::new(syntax::lex(&source).unwrap()).parse().unwrap();
        let syntax::Stmt::If {condition: syntax::Expr::Arena(arena), .. } = &parsed.statements[1]
            else { panic!("expected arena boolean expression"); };
        assert!(arena.has_short_circuit);
        let clone = arena.try_map_atoms(|expr| Ok::<_, ()>(expr.clone())).unwrap();
        assert!(clone.has_short_circuit);
        assert_eq!(sema::emit_qasm(&compile(&source).unwrap()),
                   sema::emit_qasm(&compile("let q=qubit(); h(q);").unwrap()));
    }

    #[test]
    fn short_arena_rebuild_preserves_mixed_precedence() {
        for (expression, value) in [
            ("1+2*3", 7.0),
            ("1*2+3", 5.0),
            ("1+2*3-4", 3.0),
            ("1-2-3", -4.0),
            ("12/3/2", 2.0),
            ("2*3+4*5", 26.0),
            ("2+3*4/6", 4.0),
        ] {
            let source = format!("let q=qubit(); rx({expression},q);");
            let expected = format!("let q=qubit(); rx({value},q);");
            let actual = compile(&source).unwrap_or_else(|e| panic!("{expression}: {e}"));
            let reference = compile(&expected).unwrap();
            assert_eq!(sema::emit_qasm(&actual), sema::emit_qasm(&reference), "{expression}");
            assert_eq!(qcu::encode(&actual).unwrap(), qcu::encode(&reference).unwrap(), "{expression}");
        }
    }

    #[test]
    fn short_arena_rebuild_preserves_boolean_precedence_and_laziness() {
        for (condition, gate) in [
            ("true || false && false", "h"),
            ("false && (1/0>0) || true", "h"),
            ("false || true && false", "x"),
            ("true && false || true", "h"),
        ] {
            let source = format!("let q=qubit(); if {condition} {{ h(q); }} else {{ x(q); }}");
            let reference = format!("let q=qubit(); {gate}(q);");
            let actual = compile(&source).unwrap_or_else(|e| panic!("{condition}: {e}"));
            assert_eq!(sema::emit_qasm(&actual), sema::emit_qasm(&compile(&reference).unwrap()), "{condition}");
        }
    }

    #[test]
    fn arena_nodes_are_indexed_and_topologically_ordered() {
        let source = format!("rz({},q);", "1+".repeat(200) + "1");
        let parsed = syntax::Parser::new(syntax::lex(&source).unwrap()).parse().unwrap();
        let syntax::Stmt::Call { args, .. } = &parsed.statements[0] else { panic!("expected call"); };
        let syntax::Expr::Arena(arena) = &args[0] else { panic!("expected an arena for long expression"); };
        assert_eq!(arena.nodes.len(), 401);
        assert_eq!(arena.root as usize, arena.nodes.len() - 1);
        for (id, node) in arena.nodes.iter().enumerate() {
            if let syntax::ExprNode::Binary { left, right, .. } = node {
                assert!((*left as usize) < id && (*right as usize) < id);
            }
        }
    }

    #[test]
    fn arena_and_short_circuit_skips_invalid_rhs() {
        let condition = "false && ".repeat(160) + "true";
        let source = format!("let q=qubit(); if ({condition}) && (1/0 > 0) {{h(q);}} else {{x(q);}} ");
        assert_eq!(sema::emit_qasm(&compile(&source).unwrap()),
                   sema::emit_qasm(&compile("let q=qubit();x(q);").unwrap()));
    }

    #[test]
    fn arena_precedence_matches_old_box_ast_and_qasm() {
        let huge = "1-".repeat(150) + "1";
        let src = format!("let q=qubit(); rx(({}) * 2 + 3 / 2 - 4,q);", huge);
        let old = "let q=qubit(); rx((-149) * 2 + 3 / 2 - 4,q);";
        assert_eq!(sema::emit_qasm(&compile(&src).unwrap()), sema::emit_qasm(&compile(old).unwrap()));
    }

    #[test]
    fn arena_boolean_short_circuit_does_not_evaluate_rhs() {
        let lhs = "true || ".repeat(150) + "false";
        let src = format!("let q=qubit(); if ({lhs}) || (1/0 > 0) {{h(q);}} else {{x(q);}} ");
        assert_eq!(sema::emit_qasm(&compile(&src).unwrap()),
            sema::emit_qasm(&compile("let q=qubit(); h(q);").unwrap()));
    }

    #[test]
    fn arena_rejects_late_division_by_zero_and_inexact_types() {
        let prefix = "1+".repeat(150) + "1";
        let bad = format!("let q=qubit(); rz({prefix}/0,q);");
        assert!(compile(&bad).unwrap_err().message.contains("division by zero"));
        let bad = format!("let q=qubit(); rz(({prefix})==151,q);");
        assert!(compile(&bad).unwrap_err().message.contains("Float"));
    }

    #[test]
    fn arena_index_dependent_angles_stay_correct() {
        let zeros = "0+".repeat(160) + "0";
        let source = format!("let q=qubit(); for i in 0..3 {{ rz(i+{zeros},q); }}");
        let reference = "let q=qubit(); for i in 0..3 { rz(i,q); }";
        assert_eq!(sema::emit_qasm(&compile(&source).unwrap()),
                   sema::emit_qasm(&compile(reference).unwrap()));
    }

    #[test]
    fn arena_qcu_output_matches_reference_short_expression() {
        let expr = "0+".repeat(180) + "pi/3";
        let src = format!("let q=qubit(); rz({expr},q); let b=measure(q);");
        let expected = "let q=qubit(); rz(pi/3,q); let b=measure(q);";
        assert_eq!(qcu::encode(&compile(&src).unwrap()).unwrap(),
                   qcu::encode(&compile(expected).unwrap()).unwrap());
    }

    #[test]
    fn parser_guard_rejects_deep_parentheses() {
        let source = format!("let q=qubit(); rx({}1{},q);", "(".repeat(400), ")".repeat(400));
        let issue = compile(&source).unwrap_err();
        assert!(issue.message.contains("parser recursion limit"), "{issue}");
    }

    #[test]
    fn parser_guard_rejects_deep_unary_prefixes() {
        let source = format!("let q=qubit(); rx({}1,q);", "-".repeat(400));
        let issue = compile(&source).unwrap_err();
        assert!(issue.message.contains("parser recursion limit"), "{issue}");
    }

    #[test]
    fn parser_guard_rejects_deep_nested_calls() {
        let source = format!("let q=qubit(); rx({}1{},q);", "sin(".repeat(200), ")".repeat(200));
        let issue = compile(&source).unwrap_err();
        assert!(issue.message.contains("parser recursion limit"), "{issue}");
    }

    #[test]
    fn arena_long_left_associative_expression_is_valid() {
        let source = format!("let q=qubit(); rx({},q);", "1+".repeat(10000) + "1");
        let program = compile(&source).expect("long chains must not overflow recursion");
        assert_eq!(program.instructions.len(), 1);
        assert!(sema::emit_qasm(&program).contains("10001"));
    }

    #[test]
    fn parser_guard_rejects_deep_else_if_chain() {
        let mut source = String::from("let q=qubit();");
        for n in 0..300 { if n == 0 { source.push_str("if false {} "); } else { source.push_str("else if false {} "); } }
        source.push_str("else {h(q);}");
        let issue = compile(&source).unwrap_err();
        assert!(issue.message.contains("parser recursion limit"), "{issue}");
    }

    #[test]
    fn parser_guard_rejects_mixed_prefix_and_index() {
        let source = format!("let q=qubits(1); h(q[{}0{}]);", "(".repeat(200), ")".repeat(200));
        let issue = compile(&source).unwrap_err();
        assert!(issue.message.contains("parser recursion limit"), "{issue}");
    }

    #[test]
    fn parser_guard_accepts_small_nested_expressions_and_flat_source() {
        let source = "let q=qubit(); rz(sin((pi/2)) + cos((pi/3)),q); let b=measure(q);";
        let result = compile(source).unwrap();
        assert!(!result.instructions.is_empty());
    }

    #[test]
    fn parser_guard_handles_many_flat_statements_without_recursion() {
        let mut src = String::from("let q=qubit();");
        for _ in 0..10_000 { src.push_str("h(q);"); }
        let output = compile(&src).unwrap();
        assert_eq!(output.instructions.len(), 10_000);
    }

    #[test]
    fn hotfix_source_cannot_forge_internal_identifiers() {
        for source in [
            "let __qrust_1_q=qubit();",
            "fn __qrust_1_gate() {} fn main() {}",
            "let q=qubit(); h(__qrust_1_q);",
        ] {
            let issue = compile(source).expect_err("compiler-private names must be rejected in source");
            assert!(issue.message.contains("reserved"), "{issue}");
        }
    }

    #[test]
    fn hotfix_nested_blocks_fail_with_diagnostic_not_stack_overflow() {
        let mut source = "{".repeat(200);
        source.push_str("h(q);");
        source.push_str(&"}".repeat(200));
        let issue = compile(&source).expect_err("deep input must fail without recursing unboundedly");
        assert!(issue.message.contains("scope limit"), "{issue}");
        assert!(issue.at.column > 1);
    }

    #[test]
    fn nested_blocks_limit_reports_source_position() {
        let mut src = "{".repeat(129);
        src.push_str("let q=qubit();");
        src.push_str(&"}".repeat(129));
        let issue = compile(&src).unwrap_err();
        assert!(issue.message.contains("scope limit"), "{issue}");
        assert!(issue.at.column > 1);
    }

    #[test]
    fn parser_fast_arguments_match_parenthesized_expressions() {
        let plain = "let q=qubit(); let r=qubit(); rx(1_000, q); cx(q,r); rz(pi/2,r); let b=measure(q);";
        let wrapped = "let q=qubit(); let r=qubit(); rx((1_000), (q)); cx((q),(r)); rz((pi/2),(r)); let b=measure((q));";
        assert_eq!(sema::emit_qasm(&compile(plain).unwrap()),
                   sema::emit_qasm(&compile(wrapped).unwrap()));
    }

    #[test]
    fn parser_fast_literal_arguments_cover_signed_and_scientific() {
        let source = "let q=qubit(); rx(1e-3,q); ry(-2.5,q); rz(+3.0,q);";
        assert_eq!(compile(source).unwrap().instructions.len(), 3);
    }

    #[test]
    fn parser_fast_boolean_arguments_work_in_language_functions() {
        let source = "fn choose(q:&mut Qubit, flag:Bool) { if flag { h(q); } } \
            fn main(){ let q=qubit(); choose(&mut q,true); choose(&mut q,false); }";
        let result = compile(source).unwrap();
        assert_eq!(result.instructions.len(), 1);
    }

    #[test]
    fn parser_nested_arguments_remain_full_expressions() {
        let source = "let q=qubit(); rz(pow(2,3) / 4 + sin(pi/2), q);";
        let result = compile(source).unwrap();
        assert_eq!(result.instructions.len(), 1);
        assert!(sema::emit_qasm(&result).contains("rz(3)"));
    }

    #[test]
    fn parser_fast_numeric_errors_are_still_rejected() {
        assert!(error("let q=qubit(); rx(1e999,q);").contains("finite"));
        assert!(error("let q=qubit(); rx(1__000,q);").contains("separator"));
    }

    #[test]
    fn parser_call_syntax_errors_still_have_positions() {
        let error = compile("let q = qubit();\nrx(1, q\n").unwrap_err();
        assert!(error.message.contains("expected"));
        assert!(error.at.line >= 2);
    }

    #[test]
    fn ten_thousand_gates_keep_legacy_fast_path() {
        let mut src = String::from("let q=qubit();");
        for _ in 0..10_000 { src.push_str("h(q);"); }
        let parsed = syntax::Parser::new(syntax::lex(&src).unwrap()).parse().unwrap();
        assert!(!parsed.needs_lowering);
        assert_eq!(sema::check(&parsed.statements).unwrap().instructions.len(), 10_000);
    }

    #[test]
    fn static_assert_true_emits_no_qasm_instructions() {
        let src = "const theta = pi / 2; static_assert(theta > 0 && theta < pi); let q=qubit(); h(q);";
        let compiled = compile(src).unwrap();
        assert_eq!(compiled.instructions.len(), 1);
        let qasm = sema::emit_qasm(&compiled);
        assert!(qasm.contains("h q[0];"));
        assert!(!qasm.contains("static_assert"));
    }

    #[test]
    fn static_assert_rejects_false_and_nonnumeric_boolean_confusion() {
        assert!(error("static_assert(false);").contains("condition is false"));
        assert!(error("static_assert(1);").contains("requires compile-time Bool"));
        assert!(error("static_assert(1 / 0 > 0);").contains("division by zero"));
    }

    #[test]
    fn static_assert_eq_and_ne_check_types_and_values() {
        assert_eq!(compile("static_assert_eq(1+2, 3); static_assert_ne(true, false);").unwrap().instructions.len(), 0);
        assert!(error("static_assert_eq(1, 2);").contains("static_assert_eq failed"));
        assert!(error("static_assert_ne(true, true);").contains("static_assert_ne failed"));
        assert!(error("static_assert_eq(1, true);").contains("same type"));
    }

    #[test]
    fn static_assert_checks_argument_counts() {
        assert!(error("static_assert();").contains("requires 1 argument"));
        assert!(error("static_assert_eq(1);").contains("requires 2 argument"));
        assert!(error("static_assert_ne(1,2,3);").contains("requires 2 argument"));
        assert!(error("let q=qubit(); static_assert_distinct(q);").contains("requires 2 argument"));
    }

    #[test]
    fn static_assert_distinct_tracks_register_qubits() {
        let src = "let r=qubits(3); static_assert_distinct(r[0],r[1]); static_assert_distinct(r[0],r[2]); cx(r[0],r[1]);";
        assert_eq!(compile(src).unwrap().instructions.len(), 1);
        assert!(error("let r=qubits(2); static_assert_distinct(r[1],r[1]);").contains("same Qubit"));
        assert!(error("let r=qubits(2); static_assert_distinct(r[0],r[2]);").contains("out of bounds"));
    }

    #[test]
    fn static_assert_distinct_requires_two_live_qubits() {
        assert!(error("let a=qubit(); let b=measure(a); static_assert_distinct(a,a);").contains("consumed or moved"));
        assert!(error("let a=qubit(); let b=1; static_assert_distinct(a,b);").contains("expects Qubit"));
    }

    #[test]
    fn static_assert_inside_function_sees_compile_time_parameters() {
        let src = "fn f(q:&mut Qubit, a:Float) { static_assert(a > 0); h(q); } fn main() {let q=qubit(); f(&mut q,pi/2);}";
        assert_eq!(compile(src).unwrap().instructions.len(), 1);
        assert!(error("fn f(q:&mut Qubit, a:Float) { static_assert(a > 0); } fn main() {let q=qubit(); f(&mut q,-1);}").contains("condition is false"));
    }

    #[test]
    fn static_assert_check_is_path_sensitive_for_const_if() {
        assert_eq!(compile("if true {static_assert(true);} else {static_assert(false);}").unwrap().instructions.len(), 0);
        assert!(error("if true {static_assert(false);} else {static_assert(true);}").contains("condition is false"));
    }

    #[test]
    fn reserved_and_built_in_function_names_are_rejected() {
        assert!(error("fn if() {} fn main() {}").contains("reserved"));
        assert!(error("fn static_assert() {} fn main() {}").contains("conflicts"));
        assert!(error("fn __qrust_internal() {} fn main() {}").contains("reserved"));
    }

    #[test]
    fn language_no_capture_of_top_level_qubit() {
        let src = "let leaked=qubit(); fn use_it() { h(leaked); } use_it();";
        assert!(error(src).contains("pass it as an explicit parameter"));
    }

    #[test]
    fn language_no_capture_of_top_level_float() {
        let src = "let theta=pi/4; fn f(q:&mut Qubit) { rz(theta,q); } let q=qubit(); f(&mut q);";
        assert!(error(src).contains("unknown variable 'theta'"));
    }

    #[test]
    fn language_no_capture_of_top_level_bool() {
        let src = "const enabled=true; fn f(q:&mut Qubit) { if enabled {h(q);} } let q=qubit(); f(&mut q);";
        assert!(error(src).contains("unknown variable 'enabled'"));
    }

    #[test]
    fn language_explicit_parameter_prevents_capture() {
        let src = "fn f(q:&mut Qubit,theta:Float) {rz(theta,q);} let theta=pi/4; let q=qubit(); f(&mut q,theta);";
        assert!(sema::emit_qasm(&compile(src).unwrap()).contains("rz(0.7853981633974483) q[0];"));
    }

    #[test]
    fn language_nested_explicit_borrow_remains_valid() {
        let src = "fn inner(q:&mut Qubit){h(q);} fn outer(q:&mut Qubit){inner(&mut q); z(q);} fn main(){let q=qubit();outer(&mut q);}";
        assert_eq!(compile(src).unwrap().instructions.len(), 2);
    }

    #[test]
    fn language_constant_pi_is_available_inside_function() {
        let src = "fn f(q:&mut Qubit){rz(pi/2,q);} fn main(){let q=qubit();f(&mut q);}";
        assert_eq!(compile(src).unwrap().instructions.len(), 1);
    }

    #[test]
    fn static_assert_live_tracks_moves_and_measurements() {
        assert_eq!(compile("let q=qubit();static_assert_live(q);h(q);").unwrap().instructions.len(),1);
        assert!(error("let q=qubit();let moved=q;static_assert_live(q);").contains("consumed or moved"));
        assert!(error("let q=qubit();let x=measure(q);static_assert_live(q);").contains("consumed or moved"));
    }

    #[test]
    fn static_assert_live_handles_register_and_measure_keep() {
        let src = "let r=qubits(2); let bit=measure_keep(r[0]); static_assert_live(r[0]);static_assert_distinct(r[0],r[1]);";
        assert_eq!(compile(src).unwrap().bits, 1);
    }

    #[test]
    fn static_assert_live_rejects_types_and_arity() {
        assert!(error("static_assert_live();").contains("requires 1 argument"));
        assert!(error("let q=qubit();static_assert_live(q,q);").contains("requires 1 argument"));
        assert!(error("let value=42;static_assert_live(value);").contains("expects Qubit"));
    }

    #[test]
    fn static_assert_live_does_not_emit_qasm() {
        let with_assertion = compile("let q=qubit();static_assert_live(q);x(q);").unwrap();
        let baseline = compile("let q=qubit();x(q);").unwrap();
        assert_eq!(sema::emit_qasm(&with_assertion), sema::emit_qasm(&baseline));
    }

    #[test]
    fn static_assert_is_not_a_gate_in_legacy_fast_path() {
        let src = "let a=qubit(); static_assert_eq(2*2,4); h(a);";
        let parsed = syntax::Parser::new(syntax::lex(src).unwrap()).parse().unwrap();
        assert!(parsed.needs_lowering);
        assert_eq!(compile(src).unwrap().instructions.len(), 1);
        let simple = "let a=qubit(); h(a);";
        assert!(!syntax::Parser::new(syntax::lex(simple).unwrap()).parse().unwrap().needs_lowering);
    }

    #[test]
    fn language_many_calls_preserve_output_and_ownership() {
        let src = r#"
            fn pulse(q: &mut Qubit, angle: Float) {
                h(q); rz(angle, q); x(q); h(q);
                ry(angle / 2, q); z(q);
            }
            fn main() {
                let q = qubit();
                for i in 0..300 { pulse(&mut q, pi / 4); }
                let b = measure(q);
            }
        "#;
        let p = compile(src).unwrap();
        assert_eq!(p.qubits, 1);
        assert_eq!(p.bits, 1);
        assert_eq!(p.instructions.len(), 300 * 6 + 1);
        let output = sema::emit_qasm(&p);
        assert_eq!(output.matches("rz(").count(), 300);
    }

    #[test]
    fn function_expansion_with_two_borrowed_qubits_remains_safe() {
        let src = "fn pair(a:&mut Qubit,b:&mut Qubit){h(a);cx(a,b);} \
                   fn main(){let a=qubit();let b=qubit();for i in 0..100 {pair(&mut a,&mut b);}}";
        let p = compile(src).unwrap();
        assert_eq!(p.instructions.len(), 200);
        assert!(error("fn pair(a:&mut Qubit,b:&mut Qubit){cx(a,b);} \
                       fn main(){let a=qubit();pair(&mut a,&mut a);}").contains("alias"));
    }

    #[test]
    fn builtin_zero_and_multi_argument_calls_keep_parser_behavior() {
        let code = "let a=qubit();let b=qubit();let c=qubit();\
                   u(pi/4,pi/3,pi/2,a);ccx(a,b,c);let d=measure(a);";
        let p = compile(code).unwrap();
        assert_eq!(p.instructions.len(), 3);
        assert_eq!(p.qubits, 3);
    }

    #[test]
    fn high_iteration_benchmark_limit_is_explicit() {
        assert_eq!(MAX_BENCH_ITERATIONS, 10_000_000);
    }


    #[test]
    fn optimized_index_free_loop_matches_flat_gates() {
        let src = "let q=qubit();for i in 0..40 {h(q);x(q);} let b=measure(q);";
        let mut flat = String::from("let q=qubit();");
        for _ in 0..40 { flat.push_str("h(q);x(q);"); }
        flat.push_str("let b=measure(q);");
        assert_eq!(sema::emit_qasm(&compile(src).unwrap()),
                   sema::emit_qasm(&compile(&flat).unwrap()));
    }

    #[test]
    fn optimized_index_free_loop_preserves_outer_shadowed_name() {
        let src = "let i=qubit();let q=qubit();for i in 0..3 {h(q);} x(i);";
        let p = compile(src).unwrap();
        assert_eq!(p.qubits, 2);
        assert_eq!(p.instructions.len(), 4);
    }

    #[test]
    fn used_index_still_has_iteration_values_and_bounds_checks() {
        let src = "let q=qubit();for i in 0..4 {rz(i*pi/4,q);}";
        let flat = "let q=qubit();rz(0*pi/4,q);rz(1*pi/4,q);rz(2*pi/4,q);rz(3*pi/4,q);";
        assert_eq!(sema::emit_qasm(&compile(src).unwrap()), sema::emit_qasm(&compile(flat).unwrap()));
        assert!(error("let q=qubit();for i in 0..2 {static_assert_eq(i,1);}").contains("failed"));
    }

    #[test]
    fn repeated_local_declarations_remain_unique() {
        let src = "fn f(q:&mut Qubit){let temp=qubit();cx(q,temp);let bit=measure(temp);}";
        let p = compile(&format!("{src} fn main(){{let q=qubit();for i in 0..10{{f(&mut q);}}}}" )).unwrap();
        assert_eq!(p.qubits, 11);
        assert_eq!(p.bits, 10);
        assert_eq!(p.instructions.len(), 20);
    }

    #[test]
    fn recycled_function_scopes_still_reject_capture_and_borrow_alias() {
        let invalid_capture = "fn f(q:&mut Qubit){h(q);} fn bad(q:&mut Qubit){h(leaked);} \
                              fn main(){let leaked=qubit();let q=qubit();f(&mut q);bad(&mut q);}";
        assert!(error(invalid_capture).contains("explicit parameter"));
        let invalid_alias = "fn pair(a:&mut Qubit,b:&mut Qubit){cx(a,b);} \
                            fn main(){let q=qubit();for i in 0..3{pair(&mut q,&mut q);}}";
        assert!(error(invalid_alias).contains("alias"));
    }


    #[test]
    fn leaf_gate_function_matches_flat_reference() {
        let expanded = "fn pulse(q:&mut Qubit,theta:Float){h(q);rx(theta,q);x(q);rz(theta/2,q);}";
        let with_fn = format!("{expanded} fn main(){{let q=qubit();for i in 0..8{{pulse(&mut q,pi/4);}}let bit=measure(q);}}");
        let mut flat = String::from("let q=qubit();");
        for _ in 0..8 { flat.push_str("h(q);rx(pi/4,q);x(q);rz(pi/8,q);"); }
        flat.push_str("let bit=measure(q);");
        assert_eq!(sema::emit_qasm(&compile(&with_fn).unwrap()),
                   sema::emit_qasm(&compile(&flat).unwrap()));
    }

    #[test]
    fn leaf_gate_functions_preserve_phase_sensitive_gates() {
        let result = compile("fn ent(a:&mut Qubit,b:&mut Qubit){CX(a,b);cx(a,b);} \
                              fn main(){let a=qubit();let b=qubit();ent(&mut a,&mut b);}").unwrap();
        let qasm = sema::emit_qasm(&result);
        assert!(qasm.contains("CX q[0], q[1];"));
        assert!(qasm.contains("cx q[0], q[1];"));
    }

    #[test]
    fn leaf_gate_function_rejects_mutable_borrow_alias() {
        let msg = error("fn pair(a:&mut Qubit,b:&mut Qubit){cx(a,b);} \
                         fn main(){let q=qubit();pair(&mut q,&mut q);}");
        assert!(msg.contains("alias"), "{msg}");
    }

    #[test]
    fn leaf_gate_function_rejects_consumed_qubit() {
        let msg = error("fn pulse(q:&mut Qubit){h(q);} \
                         fn main(){let q=qubit();let c=measure(q);pulse(&mut q);}");
        assert!(msg.contains("consumed") || msg.contains("moved"), "{msg}");
    }

    #[test]
    fn leaf_gate_function_still_checks_gate_arity_and_angle_types() {
        let arity = error("fn bad(q:&mut Qubit){h(q,q);} fn main(){let q=qubit();bad(&mut q);}");
        assert!(arity.contains("requires"), "{arity}");
        let kind = error("fn bad(q:&mut Qubit,v:Bool){rz(v,q);} \
                          fn main(){let q=qubit();bad(&mut q,true);}");
        assert!(kind.contains("Bool") || kind.contains("Float"), "{kind}");
    }

    #[test]
    fn leaf_gate_function_does_not_capture_outer_names() {
        let msg = error("fn bad(q:&mut Qubit){rz(angle,q);} \
                         fn main(){let angle=1;let q=qubit();bad(&mut q);}");
        assert!(msg.contains("explicit parameter"), "{msg}");
    }

    #[test]
    fn leaf_gate_function_does_not_skip_invalid_parameter_names() {
        let msg = error("fn bad(pi:Float,q:&mut Qubit){rz(pi,q);} \
                         fn main(){let q=qubit();bad(1,&mut q);}");
        assert!(msg.contains("reserved"), "{msg}");
    }

    #[test]
    fn phase_gate_name_is_not_available_for_user_function() {
        let msg = error("fn p(q:&mut Qubit){h(q);}fn main(){let q=qubit();p(&mut q);}");
        assert!(msg.contains("builtin"), "{msg}");
    }

    #[test]
    fn nested_mut_borrow_survives_recycled_environments() {
        let src = "fn inner(q:&mut Qubit){h(q);} \
                   fn outer(q:&mut Qubit){inner(&mut q);z(q);} \
                   fn main(){let q=qubit();for i in 0..20{outer(&mut q);}}";
        assert_eq!(compile(src).unwrap().instructions.len(), 40);
    }

    #[test]
    fn optimized_unused_index_still_rejects_reserved_names() {
        let message = error("let q=qubit();for pi in 0..2 {h(q);}");
        assert!(message.contains("reserved"), "{message}");
    }

    #[test]
    fn repeated_function_static_asserts_still_run_per_call() {
        let src = "fn f(q:&mut Qubit){static_assert_live(q);h(q);} \
                   fn main(){let q=qubit();for i in 0..30{f(&mut q);}}";
        assert_eq!(compile(src).unwrap().instructions.len(), 30);
    }

    #[test]
    fn lowering_elides_static_parameter_and_loop_declarations() {
        let src = "fn pulse(q:&mut Qubit, angle:Float){rz(angle,q);}                    fn main(){let q=qubit();for i in 0..10 {pulse(&mut q,i*pi/8);}let b=measure(q);}";
        let parsed = syntax::Parser::new(syntax::lex(src).unwrap()).parse().unwrap();
        let lowered = language::lower(&parsed.statements).unwrap();
        assert_eq!(lowered.len(), 3); //qubit + indexed template + measurement
        assert!(matches!(&lowered[1],
            syntax::Stmt::RepeatIndexedGates { start: 0, end: 10, template, .. }
                if template.len() == 1));
        let checked = sema::check(&lowered).unwrap();
        assert_eq!(checked.instructions.len(), 11); //10 rotations + measurement
        let mut flat = String::from("let q=qubit();");
        for i in 0..10 { flat.push_str(&format!("rz(({i})*pi/8,q);")); }
        flat.push_str("let b=measure(q);");
        assert_eq!(sema::emit_qasm(&checked),
                   sema::emit_qasm(&compile(&flat).unwrap()));
    }

    #[test]
    fn lowering_elision_preserves_reference_qasm() {
        let with_functions = "fn pulse(q:&mut Qubit, v:Float){rz(v,q);h(q);}                               fn main(){let q=qubit();for i in 0..12{pulse(&mut q,i*pi/8);}let b=measure(q);}";
        let mut flat = String::from("let q=qubit();");
        for i in 0..12 { flat.push_str(&format!("rz({i}*pi/8,q);h(q);")); }
        flat.push_str("let b=measure(q);");
        let lhs = sema::emit_qasm(&compile(with_functions).unwrap());
        let rhs = sema::emit_qasm(&compile(&flat).unwrap());
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn lowering_nested_scalar_arguments_remain_lexical() {
        let src = "fn inner(q:&mut Qubit,angle:Float){rz(angle,q);}                    fn outer(q:&mut Qubit,angle:Float){inner(&mut q,angle/2);}                    fn main(){let q=qubit();outer(&mut q,pi);}";
        let p = compile(src).unwrap();
        assert_eq!(p.instructions.len(), 1);
        assert!(sema::emit_qasm(&p).contains("rz(1.5707963267948966)"));
    }

    #[test]
    fn lowering_boolean_parameters_preserve_branch_checks() {
        let src = "fn flip(q:&mut Qubit, enabled:Bool){if enabled{x(q);}else{z(q);}}                    fn main(){let q=qubit();flip(&mut q,true);flip(&mut q,false);}";
        let output = sema::emit_qasm(&compile(src).unwrap());
        assert!(output.contains("x q[0];"));
        assert!(output.contains("z q[0];"));
        assert_eq!(compile(src).unwrap().instructions.len(), 2);
    }

    #[test]
    fn lowering_register_index_from_loop_constant() {
        let src = "fn turn(q:&mut Qubit,angle:Float){ry(angle,q);}                    fn main(){let r=qubits(4);for i in 0..4{turn(&mut r[i],i*pi/4);}}";
        let p = compile(src).unwrap();
        assert_eq!(p.qubits, 4);
        assert_eq!(p.instructions.len(), 4);
    }

    #[test]
    fn lowering_shadowed_loop_variable_does_not_escape() {
        let src = "let q=qubit();for i in 0..2 {for i in 0..3 {rz(i*pi/3,q);}}";
        assert_eq!(compile(src).unwrap().instructions.len(), 6);
        assert!(error("let q=qubit();for i in 0..2{x(q);}rz(i,q);").contains("unknown"));
    }

    #[test]
    fn lowering_static_parameter_mismatch_still_rejected() {
        let float_error = error("fn f(q:&mut Qubit,v:Float){rz(v,q);} fn main(){let q=qubit();f(&mut q,true);}");
        assert!(float_error.contains("expects Float"), "{float_error}");
        let bool_error = error("fn f(q:&mut Qubit,b:Bool){if b{x(q);}} fn main(){let q=qubit();f(&mut q,pi);}");
        assert!(bool_error.contains("expects Bool"), "{bool_error}");
        let alias_error = error("fn f(a:&mut Qubit,b:&mut Qubit){cx(a,b);} fn main(){let q=qubit();f(&mut q,&mut q);}");
        assert!(alias_error.contains("alias"), "{alias_error}");
    }


    #[test]
    fn prepared_leaf_matches_unrolled_gates_with_varying_angles() {
        let source = "fn spin(q:&mut Qubit,theta:Float){h(q);rz(theta,q);ry(theta/2,q);x(q);} \
                      fn main(){let q=qubit();for i in 0..24{spin(&mut q,i*pi/12);}let bit=measure(q);}";
        let mut reference = String::from("let q=qubit();");
        for i in 0..24 {
            reference.push_str(&format!("h(q);rz({i}*pi/12,q);ry({i}*pi/12/2,q);x(q);"));
        }
        reference.push_str("let bit=measure(q);");
        let actual = sema::emit_qasm(&compile(source).unwrap());
        let expected = sema::emit_qasm(&compile(&reference).unwrap());
        assert_eq!(actual, expected);
    }

    #[test]
    fn prepared_leaf_handles_multiple_qubit_parameters() {
        let source = "fn entangle(a:&mut Qubit,b:&mut Qubit,angle:Float){h(a);cx(a,b);rz(angle,b);} \
                      fn main(){let q=qubits(2);for i in 0..10 {entangle(&mut q[0],&mut q[1],pi/8);}}";
        let result = compile(source).unwrap();
        assert_eq!(result.qubits, 2);
        assert_eq!(result.instructions.len(), 30);
    }

    #[test]
    fn prepared_leaf_keeps_aliased_borrow_rejection() {
        let msg = error("fn entangle(a:&mut Qubit,b:&mut Qubit){cx(a,b);} \
                         fn main(){let q=qubit();entangle(&mut q,&mut q);}");
        assert!(msg.contains("alias"), "{msg}");
    }

    #[test]
    fn prepared_leaf_checks_gate_types_and_liveness() {
        let wrong = error("fn spin(q:&mut Qubit,theta:Bool){rz(theta,q);} \
                           fn main(){let q=qubit();spin(&mut q,true);}");
        assert!(wrong.contains("Bool") || wrong.contains("Float"), "{wrong}");
        let consumed = error("fn spin(q:&mut Qubit){h(q);} \
                              fn main(){let q=qubit();let bit=measure(q);spin(&mut q);}");
        assert!(consumed.contains("consumed"), "{consumed}");
    }

    #[test]
    fn prepared_leaf_preserves_nested_mathematical_expressions() {
        let source = "fn spin(q:&mut Qubit,v:Float){rx(sin(v)+cos(v),q);} \
                      fn main(){let q=qubit();spin(&mut q,pi/4);}";
        let reference = "let q=qubit();rx(sin(pi/4)+cos(pi/4),q);";
        assert_eq!(sema::emit_qasm(&compile(source).unwrap()),
                   sema::emit_qasm(&compile(reference).unwrap()));
    }

    #[test]
    fn borrowed_top_level_lowering_matches_flat_program() {
        let source = "let q=qubit();for i in 0..20{h(q);rz(i*pi/10,q);}let bit=measure(q);";
        let mut flat = String::from("let q=qubit();");
        for i in 0..20 { flat.push_str(&format!("h(q);rz({i}*pi/10,q);")); }
        flat.push_str("let bit=measure(q);");
        assert_eq!(sema::emit_qasm(&compile(source).unwrap()),
                   sema::emit_qasm(&compile(&flat).unwrap()));
    }

    #[test]
    fn prepared_leaf_does_not_capture_caller_symbols() {
        let msg = error("fn spin(q:&mut Qubit){rz(angle,q);} \
                         fn main(){let angle=pi/4;let q=qubit();spin(&mut q);}");
        assert!(msg.contains("unknown variable"), "{msg}");
    }

    #[test]
    fn typed_ir_uses_compact_numeric_operands() {
        use crate::ids::{QubitId, SymbolId, BitId};
        assert_eq!(std::mem::size_of::<QubitId>(), 4);
        assert_eq!(std::mem::size_of::<SymbolId>(), 4);
        assert_eq!(std::mem::size_of::<BitId>(), 4);
        assert!(std::mem::size_of::<ir::Instruction>() <= 32);
    }

    #[test]
    fn typed_ir_separates_angle_pool_and_gates() {
        let program = compile("let q=qubit(); h(q); rx(pi/3,q); rz(0.5,q); let m=measure(q);").unwrap();
        assert_eq!(program.instructions.len(), 4);
        assert_eq!(program.angles.len(), 2);
        assert_eq!(program.instructions[0].count, 0);
        assert_eq!(program.instructions[1].count, 1);
        assert_eq!(program.instructions[2].offset, 1);
        assert!(matches!(program.instructions[3].opcode, ir::OpCode::Measure));
    }

    #[test]
    fn typed_ir_barrier_operand_pool_roundtrip() {
        let program = compile("let a=qubit();let b=qubit();let c=qubit();barrier(a,b,c);h(a);").unwrap();
        assert_eq!(program.barrier_qubits.len(), 3);
        assert_eq!(program.instructions.len(), 2);
        assert_eq!(program.instructions[0].count, 3);
        let qasm = sema::emit_qasm(&program);
        assert!(qasm.contains("barrier q[0], q[1], q[2];"));
    }

    #[test]
    fn typed_ir_preserves_phase_sensitive_gate_names() {
        let program = compile("let a=qubit();let b=qubit();CX(a,b);cx(a,b);u2(0,pi,a);u3(1,2,3,b);").unwrap();
        let qasm = sema::emit_qasm(&program);
        assert!(qasm.contains("CX q[0], q[1];"));
        assert!(qasm.contains("cx q[0], q[1];"));
        assert!(qasm.contains("u2(0, 3.141592653589793) q[0];"));
        assert!(qasm.contains("u3(1, 2, 3) q[1];"));
    }

    #[test]
    fn gate_id_table_covers_all_gates() {
        for gate in sema::STANDARD_GATES.iter().chain(sema::EXTENDED_GATES) {
            let found = sema::gate_spec(gate.id);
            assert_eq!(gate.name, found.name);
            assert_eq!(gate.parameters, found.parameters);
            assert_eq!(gate.qubits, found.qubits);
        }
    }

    #[test]
    fn interner_assigns_stable_symbol_slots() {
        let mut table = ids::SymbolTable::<i32>::with_capacity(4);
        let first = table.insert("q", 1);
        assert_eq!(table.get("q"), Some(1));
        assert_eq!(table.insert("q", 2), first);
        assert_eq!(table.by_id(first), 2);
        assert_eq!(table.slot_count(), 1);
        let second = table.insert("bit", 3);
        assert_ne!(first, second);
    }

    #[test]
    fn typed_ir_still_rejects_aliased_borrows() {
        let msg = error("fn entangle(a:&mut Qubit,b:&mut Qubit){cx(a,b);}fn main(){let q=qubit();entangle(&mut q,&mut q);}");
        assert!(msg.contains("alias"), "{msg}");
    }

    #[test]
    fn compact_ir_static_loop_matches_flat_qasm() {
        let source="fn pulse(q:&mut Qubit){h(q);rz(pi/2,q);} fn main(){let q=qubit();for i in 0..40{pulse(&mut q);}}";
        let mut flat=String::from("let q=qubit();");
        for _ in 0..40 {flat.push_str("h(q);rz(pi/2,q);");}
        assert_eq!(sema::emit_qasm(&compile(source).unwrap()), sema::emit_qasm(&compile(&flat).unwrap()));
    }


    #[test]
    fn high_level_name_interner_reuses_numeric_id() {
        let mut names = ids::NameInterner::default();
        let a = names.intern("state");
        assert_eq!(a, names.intern("state"));
        assert_eq!(names.id("state"), Some(a));
        assert_eq!(names.name(a), "state");
        assert_eq!(names.len(), 1);
        let b = names.intern("result");
        assert_ne!(a, b);
        assert_eq!(names.len(), 2);
    }

    #[test]
    fn high_level_shadowed_names_resolve_correct_slots() {
        let source = "fn main(){let q=qubit();{let q=qubit();h(q);}x(q);}";
        let program = compile(source).unwrap();
        assert_eq!(program.qubits, 2);
        let qasm = sema::emit_qasm(&program);
        assert!(qasm.contains("h q[1];"), "{qasm}");
        assert!(qasm.contains("x q[0];"), "{qasm}");
    }

    #[test]
    fn numeric_function_ids_preserve_forward_declarations() {
        let source = "fn main(){let q=qubit();transform(&mut q);} fn transform(q:&mut Qubit){h(q);}";
        assert_eq!(compile(source).unwrap().instructions.len(), 1);
    }

    #[test]
    fn numeric_prepared_gate_templates_preserve_cx_vs_legacy_cx() {
        let source = "fn entangle(a:&mut Qubit,b:&mut Qubit){CX(a,b);cx(a,b);}fn main(){let a=qubit();let b=qubit();entangle(&mut a,&mut b);}";
        let qasm = sema::emit_qasm(&compile(source).unwrap());
        assert!(qasm.contains("CX q[0], q[1];"), "{qasm}");
        assert!(qasm.contains("cx q[0], q[1];"), "{qasm}");
    }

    #[test]
    fn prepared_nested_math_parameter_ids_equal_flat_circuit() {
        let source = "fn oscillate(q:&mut Qubit,t:Float){rz(sin(t)+pow(t,2)/3,q);rx(t/2,q);}fn main(){let q=qubit();oscillate(&mut q,pi/4);}";
        let flat = "let q=qubit();rz(sin(pi/4)+pow(pi/4,2)/3,q);rx(pi/8,q);";
        assert_eq!(sema::emit_qasm(&compile(source).unwrap()),
                   sema::emit_qasm(&compile(flat).unwrap()));
    }

    #[test]
    fn prepared_parameter_named_like_gate_has_no_capture() {
        let source = "fn shift(q:&mut Qubit,x:Float){rx(x,q);}fn main(){let q=qubit();shift(&mut q,pi/3);}";
        assert_eq!(compile(source).unwrap().instructions.len(), 1);
    }

    #[test]
    fn qubit_id_stays_distinct_across_mutable_parameters() {
        let source = "fn pair(a:&mut Qubit,b:&mut Qubit){cx(a,b);}fn main(){let a=qubit();let b=qubit();pair(&mut a,&mut b);}";
        assert_eq!(compile(source).unwrap().qubits, 2);
        let error_text = error("fn pair(a:&mut Qubit,b:&mut Qubit){cx(a,b);}fn main(){let a=qubit();let moved=a;pair(&mut moved,&mut moved);}");
        assert!(error_text.contains("alias"), "{error_text}");
    }

    #[test]
    fn numeric_scope_ids_reject_caller_capture() {
        let source = "fn inner(q:&mut Qubit){rz(angle,q);} fn main(){let angle=pi/4;let q=qubit();inner(&mut q);}";
        assert!(error(source).contains("explicit parameter"));
    }

    #[test]
    fn numeric_scope_ids_keep_register_index_bounds() {
        let source = "fn main(){let a=qubits(3);for i in 0..3 {h(a[i]);}}";
        assert_eq!(compile(source).unwrap().instructions.len(), 3);
        assert!(error("fn main(){let a=qubits(3);h(a[3]);}").contains("out of bounds"));
    }

    #[test]
    fn numeric_scopes_do_not_weaken_consumed_qubit_checks() {
        let source = "fn check(q:&mut Qubit){h(q);}fn main(){let q=qubit();let bit=measure(q);check(&mut q);}";
        assert!(error(source).contains("consumed"));
    }



    #[test]
    fn direct_leaf_generates_checked_numeric_ir_without_ast_argument_rebuild() {
        let source = "fn turn(q:&mut Qubit,theta:Float){h(q);rx(theta,q);rz(theta/2,q);}fn main(){let q=qubit();for i in 0..15 {turn(&mut q,i*pi/7);}}";
        let program=compile(source).unwrap();
        assert_eq!(program.instructions.len(),45);
        let mut flat=String::from("let q=qubit();");
        for i in 0..15 { flat.push_str(&format!("h(q);rx({}*pi/7,q);rz(({}*pi/7)/2,q);",i,i)); }
        assert_eq!(sema::emit_qasm(&program),sema::emit_qasm(&compile(&flat).unwrap()));
    }
    #[test]
    fn direct_leaf_preserves_cx_and_phase_sensitive_legacy_gate() {
        let src="fn both(a:&mut Qubit,b:&mut Qubit){CX(a,b);cx(a,b);}fn main(){let a=qubit();let b=qubit();both(&mut a,&mut b);}";
        let qasm=sema::emit_qasm(&compile(src).unwrap());
        assert!(qasm.contains("CX q[0], q[1];"));
        assert!(qasm.contains("cx q[0], q[1];"));
    }
    #[test]
    fn direct_leaf_rejects_wrong_arity_and_angle_types() {
        assert!(error("fn pulse(q:&mut Qubit){rx(q);}fn main(){let q=qubit();pulse(&mut q);}").contains("requires"));
        assert!(error("fn pulse(q:&mut Qubit,b:Bool){rx(b,q);}fn main(){let q=qubit();pulse(&mut q,true);}").contains("Float"));
    }
    #[test]
    fn direct_leaf_preserves_liveness_and_alias_checks() {
        let consumed = error("fn pulse(q:&mut Qubit){h(q);}fn main(){let q=qubit();let b=measure(q);pulse(&mut q);}");
        assert!(consumed.contains("consumed"),"{consumed}");
        let aliased=error("fn pair(a:&mut Qubit,b:&mut Qubit){cx(a,b);}fn main(){let q=qubit();pair(&mut q,&mut q);}");
        assert!(aliased.contains("alias"),"{aliased}");
    }
    #[test]
    fn while_loop_and_mutable_scalar_match_unrolled_gates() {
        let source="fn main(){let q=qubit();let mut i:Float=0;while i<10 {rz(i*pi/12,q);i=i+1;}}";
        let mut flat=String::from("let q=qubit();");
        for i in 0..10 { flat.push_str(&format!("rz({i}*pi/12,q);")); }
        assert_eq!(sema::emit_qasm(&compile(source).unwrap()),sema::emit_qasm(&compile(&flat).unwrap()));
    }
    #[test]
    fn while_loop_can_update_bool_and_scalar() {
        let src="fn main(){let q=qubit();let mut active=true;let mut i=0;while active {h(q);i=i+1;if i>=3 {active=false;}}}";
        assert_eq!(compile(src).unwrap().instructions.len(),3);
    }
    #[test]
    fn while_rejects_dynamic_measurement_feedback() {
        let msg=error("fn main(){let q=qubit();let b=measure_keep(q);while b {h(q);}}");
        assert!(msg.contains("every path"), "{msg}");
    }
    #[test]
    fn assignment_rejects_immutable_or_type_changes() {
        assert!(error("let x=0;x=1;").contains("immutable"));
        assert!(error("let mut x=0;x=true;").contains("mismatch"));
        assert!(error("const mut x=1;").contains("const cannot be mutable"));
    }
    #[test]
    fn while_respects_block_scope_and_lifetime() {
        let src="fn main(){let q=qubit();let mut i=0;while i<4 {{let theta=i*pi/4;rz(theta,q);}i=i+1;}}";
        assert_eq!(compile(src).unwrap().instructions.len(),4);
    }
    #[test]
    fn direct_leaf_nested_math_matches_flat() {
        let src="fn pulse(q:&mut Qubit,t:Float){rz(sin(t)+pow(t,2)/3,q);}fn main(){let q=qubit();pulse(&mut q,pi/5);}";
        let flat="let q=qubit();rz(sin(pi/5)+pow(pi/5,2)/3,q);";
        assert_eq!(sema::emit_qasm(&compile(src).unwrap()),sema::emit_qasm(&compile(flat).unwrap()));
    }

    #[test]
    fn runtime_if_emits_openqasm_branches() {
        let source = "fn main(){let q=qubit();let b=measure_keep(q);if b {x(q);} else {z(q);}h(q);}";
        let program = compile(source).unwrap();
        let qasm = sema::emit_qasm(&program);
        assert!(qasm.contains("if (c[0] == 1) {\nx q[0];\n} else {\nz q[0];\n}"), "{qasm}");
        assert!(qasm.contains("}\nh q[0];"), "{qasm}");
    }
    #[test]
    fn runtime_if_supports_negated_measurement_bit() {
        let source = "let q=qubit();let b=measure_keep(q);if !b {h(q);}";
        let qasm = sema::emit_qasm(&compile(source).unwrap());
        assert!(qasm.contains("if (c[0] == 0) {"), "{qasm}");
    }
    #[test]
    fn runtime_if_checks_both_branches() {
        let e = error("let q=qubit();let b=measure_keep(q);if b {h(q);} else {cx(q,q);}");
        assert!(e.contains("distinct"), "{e}");
        let e = error("let q=qubit();let b=measure(q);if b {h(q);}");
        assert!(e.contains("consumed"), "{e}");
    }
    #[test]
    fn runtime_if_rejects_ownership_changes_and_assignments() {
        let e = error("let q=qubit();let b=measure_keep(q);if b {let x=measure(q);}");
        assert!(e.contains("only gates"), "{e}");
        let e = error("let q=qubit();let b=measure_keep(q);let mut a=0;if b {a=1;}");
        assert!(e.contains("only gates"), "{e}");
    }
    #[test]
    fn runtime_if_does_not_change_static_if() {
        let static_src = "let q=qubit();if true {h(q);} else {x(q);}";
        let qasm = sema::emit_qasm(&compile(static_src).unwrap());
        assert!(!qasm.contains("if ("), "{qasm}");
        assert!(qasm.contains("h q[0];"));
        assert!(!qasm.contains("x q[0];"));
    }
    #[test]
    fn runtime_if_alias_bit_and_reset_barrier() {
        let src="let q=qubit();let b=measure_keep(q);let alias=b;if alias {reset(q);barrier(q);} else {x(q);}";
        let qasm=sema::emit_qasm(&compile(src).unwrap());
        assert!(qasm.contains("reset q[0];"));
        assert!(qasm.contains("barrier q[0];"));
    }
    #[test]
    fn runtime_if_rejects_wrong_classical_type() {
        let err=error("let q=qubit();let value=1;if value {h(q);}");
        assert!(err.contains("compile-time Bool") || err.contains("Bool"), "{err}");
    }
    #[test]
    fn runtime_if_supports_nested_dynamic_control() {
        let source="let q=qubit();let b=measure_keep(q);if b {if b {h(q);}else{x(q);}}";
        let qasm=sema::emit_qasm(&compile(source).unwrap());
        assert_eq!(qasm.matches("if (c[0] == 1)").count(), 2, "{qasm}");
    }

    #[test]
    fn runtime_while_emits_openqasm_feedback() {
        let src="let q=qubit();let mut b=measure_keep(q);while b {reset(q);h(q);measure_into(b,q);}x(q);";
        let program=compile(src).unwrap();
        let qasm=sema::emit_qasm(&program);
        assert!(qasm.contains("while (c[0] == 1) {"), "{qasm}");
        assert!(qasm.contains("c[0] = measure q[0];\n}\nx q[0];"), "{qasm}");
        assert_eq!(program.bits,1);
    }
    #[test]
    fn runtime_while_supports_negation() {
        let src="let q=qubit();let mut b=measure_keep(q);while !b {x(q);measure_into(b,q);}";
        let qasm=sema::emit_qasm(&compile(src).unwrap());
        assert!(qasm.contains("while (c[0] == 0) {"), "{qasm}");
    }
    #[test]
    fn runtime_while_checks_definite_remeasurement() {
        let e=error("let q=qubit();let mut b=measure_keep(q);while b {x(q);}");
        assert!(e.contains("every path"), "{e}");
        let e=error("let q=qubit();let mut b=measure_keep(q);while b {if b {measure_into(b,q);}}");
        assert!(e.contains("every path"), "{e}");
    }
    #[test]
    fn runtime_while_merges_nested_branches() {
        let src="let q=qubit();let r=qubit();let mut b=measure_keep(q);let c=measure_keep(r);while b {if c {x(q);measure_into(b,q);}else{z(q);measure_into(b,q);}}";
        let qasm=sema::emit_qasm(&compile(src).unwrap());
        assert!(qasm.contains("while (c[0] == 1) {"), "{qasm}");
        assert!(qasm.contains("if (c[1] == 1) {"), "{qasm}");
        assert_eq!(qasm.matches("c[0] = measure q[0];").count(), 3);
    }
    #[test]
    fn runtime_while_checks_each_branch_gate_safety() {
        let e=error("let q=qubit();let mut b=measure_keep(q);while b {if b {cx(q,q);}else{x(q);}measure_into(b,q);}");
        assert!(e.contains("distinct"), "{e}");
    }
    #[test]
    fn runtime_while_forbids_consuming_qubits() {
        let e=error("let q=qubit();let mut b=measure_keep(q);while b {let x=measure(q);measure_into(b,q);}");
        assert!(e.contains("ownership changes"), "{e}");
    }
    #[test]
    fn measure_into_requires_mutable_bit_and_live_qubit() {
        let e=error("let q=qubit();let b=measure_keep(q);measure_into(b,q);");
        assert!(e.contains("mutable Bit"), "{e}");
        let e=error("let q=qubit();let mut b=measure(q);measure_into(b,q);");
        assert!(e.contains("consumed or moved"), "{e}");
    }
    #[test]
    fn runtime_if_allows_safe_bit_refresh() {
        let src="let q=qubit();let mut b=measure_keep(q);if b {measure_into(b,q);}else{x(q);}";
        let qasm=sema::emit_qasm(&compile(src).unwrap());
        assert!(qasm.contains("if (c[0] == 1) {"), "{qasm}");
    }
    #[test]
    fn runtime_while_in_main_preserves_mutable_bit_and_qubit_identity() {
        let source = "fn main(){let q=qubit();h(q);let mut feedback=measure_keep(q);while feedback {reset(q);h(q);measure_into(feedback,q);}x(q);}";
        let qasm = sema::emit_qasm(&compile(source).unwrap());
        assert!(qasm.contains("while (c[0] == 1) {"), "{qasm}");
        assert!(qasm.contains("c[0] = measure q[0];"), "{qasm}");
        assert!(qasm.contains("x q[0];"), "{qasm}");
    }
    #[test]
    fn runtime_if_in_main_allows_bit_refresh() {
        let source = "fn main(){let q=qubit();let mut feedback=measure_keep(q);if feedback {measure_into(feedback,q);}else{reset(q);}h(q);}";
        let qasm = sema::emit_qasm(&compile(source).unwrap());
        assert!(qasm.contains("if (c[0] == 1) {"), "{qasm}");
        assert!(qasm.contains("c[0] = measure q[0];"), "{qasm}");
    }
    #[test]
    fn runtime_while_in_main_rejects_immutable_feedback() {
        let e = error("fn main(){let q=qubit();let feedback=measure_keep(q);while feedback {measure_into(feedback,q);}}");
        assert!(e.contains("mutable Bit"), "{e}");
    }
    #[test]
    fn runtime_while_in_main_rejects_consumed_qubit() {
        let e = error("fn main(){let q=qubit();let mut feedback=measure(q);while feedback {measure_into(feedback,q);}}");
        assert!(e.contains("live Qubit") || e.contains("consumed or moved"), "{e}");
    }
    #[test]
    fn runtime_while_in_main_requires_refresh_on_all_paths() {
        let e = error("fn main(){let q=qubit();let mut feedback=measure_keep(q);while feedback {if feedback {measure_into(feedback,q);}}}");
        assert!(e.contains("every path"), "{e}");
    }

    #[test]
    fn runtime_while_condition_must_be_bit() {
        let e=error("let q=qubit();while 1 {x(q);}");
        assert!(e.contains("compile-time Bool"), "{e}");
    }
    #[test]
    fn no_remeasurement_in_inactive_static_if_is_rejected() {
        let e=error("let q=qubit();let mut b=measure_keep(q);while b {if false {measure_into(b,q);} }");
        assert!(e.contains("every path"), "{e}");
    }

    #[test]
    fn gate_batch_matches_unrolled_direct_leaf_and_ir_angles() {
        let source = "fn pulse(q:&mut Qubit,t:Float){h(q);rx(t,q);rz(t/2,q);x(q);}".to_owned() +
            " fn main(){let q=qubit();for unused in 0..40 {pulse(&mut q,pi/7);}let b=measure(q);}";
        let parsed = syntax::Parser::new(syntax::lex(&source).unwrap()).parse().unwrap();
        let lowered = language::lower(&parsed.statements).unwrap();
        let batches: Vec<_> = lowered.iter().filter_map(|s| match s {
            syntax::Stmt::RepeatGates { template, repeats, .. } => Some((template, repeats)),
            _ => None,
        }).collect();
        assert_eq!(batches.len(), 1);
        assert_eq!(*batches[0].1, 40);
        assert_eq!(batches[0].0.len(), 4);
        assert!(batches[0].0.iter().all(|s| matches!(s, syntax::Stmt::DirectGate { .. })));
        let mut reference = String::from("let q=qubit();");
        for _ in 0..40 { reference.push_str("h(q);rx(pi/7,q);rz((pi/7)/2,q);x(q);"); }
        reference.push_str("let b=measure(q);");
        let compact = compile(&source).unwrap();
        let flat = compile(&reference).unwrap();
        assert_eq!(compact.instructions.len(), 161);
        assert_eq!(compact.angles, flat.angles);
        assert_eq!(sema::emit_qasm(&compact), sema::emit_qasm(&flat));
    }

    #[test]
    fn gate_batch_from_builtin_gates_matches_flat() {
        let source = "let a=qubit();let b=qubit();for unused in 0..20{cx(a,b);rx(pi/5,b);gphase(pi/3);}";
        let parsed = syntax::Parser::new(syntax::lex(source).unwrap()).parse().unwrap();
        let lowered = language::lower(&parsed.statements).unwrap();
        assert!(lowered.iter().any(|s| matches!(s, syntax::Stmt::RepeatGates { repeats:20, .. })));
        let mut flat = String::from("let a=qubit();let b=qubit();");
        for _ in 0..20 { flat.push_str("cx(a,b);rx(pi/5,b);gphase(pi/3);"); }
        assert_eq!(sema::emit_qasm(&compile(source).unwrap()), sema::emit_qasm(&compile(&flat).unwrap()));
    }

    #[test]
    fn gate_batch_preserves_alias_and_consumed_qubit_rejection() {
        let pair = "fn pair(a:&mut Qubit,b:&mut Qubit){cx(a,b);}";
        assert!(error(&format!("{pair} fn main(){{let q=qubit();for unused in 0..40{{pair(&mut q,&mut q);}}}}"))
            .contains("alias"));
        assert!(error("fn apply_x(q:&mut Qubit){x(q);} fn main(){let q=qubit();let b=measure(q);for i in 0..40{apply_x(&mut q);}}")
            .contains("consumed or moved"));
        assert!(error("let q=qubit();for pi in 0..40{x(q);}").contains("reserved"));
    }

    #[test]
    fn gate_batch_rejects_invalid_gates_and_keeps_ownership() {
        assert!(error("fn f(q:&mut Qubit){rx(true,q);}fn main(){let q=qubit();for i in 0..30{f(&mut q);}}")
            .contains("Float"));
        assert!(error("let q=qubit();for ignored in 0..30{cx(q,q);}").contains("distinct"));
        assert_eq!(compile("fn f(q:&mut Qubit){h(q);}fn main(){let q=qubit();for i in 0..40{f(&mut q);} let bit=measure(q);}").unwrap().bits, 1);
    }

    #[test]
    fn gate_batch_does_not_cache_measurements_or_indexed_args() {
        let source = "let q=qubit();for i in 0..3{let b=measure_keep(q);}";
        let parsed = syntax::Parser::new(syntax::lex(source).unwrap()).parse().unwrap();
        let lowered = language::lower(&parsed.statements).unwrap();
        assert!(!lowered.iter().any(|s| matches!(s, syntax::Stmt::RepeatGates { .. })));
        assert_eq!(compile(source).unwrap().bits, 3);
        let source = "let q=qubit();for i in 0..4{rz(i*pi/4,q);}";
        let parsed = syntax::Parser::new(syntax::lex(source).unwrap()).parse().unwrap();
        let lowered = language::lower(&parsed.statements).unwrap();
        assert!(!lowered.iter().any(|s| matches!(s, syntax::Stmt::RepeatGates { .. })));
        let qasm = sema::emit_qasm(&compile(source).unwrap());
        assert!(qasm.contains("rz(0.7853981633974483)"));
    }

    #[test]
    fn gate_batch_honors_five_hundred_thousand_gate_expansion_limit() {
        let source = "fn many(q:&mut Qubit){h(q);x(q);y(q);z(q);s(q);t(q);}".to_owned() +
            "fn main(){let q=qubit();for ignored in 0..100000{many(&mut q);}}";
        assert!(error(&source).contains("500,000"));
    }

    #[test]
    fn gate_batch_handles_shadowing_and_mixed_operations() {
        let source = "let ignored=qubit();let q=qubit();for ignored in 0..3{x(q);h(q);}h(ignored);";
        let mut flat = String::from("let ignored=qubit();let q=qubit();");
        for _ in 0..3 { flat.push_str("x(q);h(q);"); }
        flat.push_str("h(ignored);");
        assert_eq!(sema::emit_qasm(&compile(source).unwrap()),
                   sema::emit_qasm(&compile(&flat).unwrap()));
    }


    #[test]
    fn indexed_template_matches_unrolled_prepared_functions() {
        let code = "fn pulse(q:&mut Qubit,t:Float){rx(t,q);rz(t/2,q);} fn main(){let q=qubit();for i in 0..40{pulse(&mut q,i*pi/40);}let b=measure(q);}";
        let parsed = syntax::Parser::new(syntax::lex(code).unwrap()).parse().unwrap();
        let lowered = language::lower(&parsed.statements).unwrap();
        assert!(lowered.iter().any(|s| matches!(s,
            syntax::Stmt::RepeatIndexedGates { start:0, end:40, .. })));
        let mut unrolled = String::from("let q=qubit();");
        for i in 0..40 { unrolled.push_str(&format!("rx(({i})*pi/40,q);rz((({i})*pi/40)/2,q);")); }
        unrolled.push_str("let b=measure(q);");
        let a=compile(code).unwrap();let b=compile(&unrolled).unwrap();
        assert_eq!(a.angles,b.angles);
        assert_eq!(sema::emit_qasm(&a),sema::emit_qasm(&b));
    }

    #[test]
    fn indexed_template_accepts_native_gates_and_nonzero_ranges() {
        let source="let q=qubit();for i in 4..18{rx(i/100,q);h(q);rz(i*pi/8,q);}";
        let parsed=syntax::Parser::new(syntax::lex(source).unwrap()).parse().unwrap();
        let lowered=language::lower(&parsed.statements).unwrap();
        assert!(lowered.iter().any(|s| matches!(s,
            syntax::Stmt::RepeatIndexedGates { start:4, end:18, .. })));
        let mut flat=String::from("let q=qubit();");
        for i in 4..18{flat.push_str(&format!("rx(({i})/100,q);h(q);rz(({i})*pi/8,q);"));}
        let fast=compile(source).unwrap();
        let ordinary=compile(&flat).unwrap();
        assert_eq!(sema::emit_qasm(&fast),sema::emit_qasm(&ordinary));
    }

    #[test]
    fn indexed_template_preserves_function_borrow_alias_rejection() {
        let input="fn pair(a:&mut Qubit,b:&mut Qubit,t:Float){cx(a,b);rx(t,a);}fn main(){let q=qubit();for i in 0..100{pair(&mut q,&mut q,i/100);}}";
        assert!(error(input).contains("alias"));
    }

    #[test]
    fn indexed_template_rejects_consumed_and_wrong_type_operands() {
        let consumed="fn f(q:&mut Qubit,t:Float){rx(t,q);}fn main(){let q=qubit();let b=measure(q);for i in 0..10{f(&mut q,i/10);}}";
        assert!(error(consumed).contains("consumed or moved"));
        let wrong="fn f(q:&mut Qubit,t:Float){rx(t,q);}fn main(){let q=qubit();for i in 0..10{f(&mut q,true);}}";
        assert!(error(wrong).contains("wrong scalar type") || error(wrong).contains("Float"));
    }

    #[test]
    fn indexed_template_validates_every_iteration_arithmetic() {
        let code="let q=qubit();for i in 0..6{rx(1/(5-i),q);}";
        assert!(error(code).contains("division by zero"));
    }

    #[test]
    fn indexed_template_keeps_register_index_on_safe_fallback() {
        let source="let r=qubits(4);for i in 0..4{rx(i*pi/4,r[i]);}";
        let parsed=syntax::Parser::new(syntax::lex(source).unwrap()).parse().unwrap();
        let lowered=language::lower(&parsed.statements).unwrap();
        assert!(!lowered.iter().any(|s| matches!(s,
            syntax::Stmt::RepeatIndexedGates { .. })));
        assert_eq!(compile(source).unwrap().instructions.len(),4);
    }

    #[test]
    fn indexed_template_does_not_cache_mutations_or_measurements() {
        let src="let q=qubit();for i in 0..5{let b=measure_keep(q);rx(i/5,q);}";
        let p=compile(src).unwrap();
        assert_eq!(p.bits,5);
        assert_eq!(p.instructions.len(),10);
    }

    #[test]
    fn indexed_template_enforces_logical_size_limit() {
        let src="let q=qubit();for i in 0..100000{rx(i/100000,q);ry(i/100000,q);rz(i/100000,q);x(q);h(q);z(q);}";
        assert!(error(src).contains("500,000"));
    }

    #[test]
    fn static_while_allows_exactly_one_hundred_thousand_iterations() {
        let code="let mut i=0;while i<100000{i=i+1;}static_assert_eq(i,100000);";
        compile(code).unwrap();
    }

    #[test]
    fn static_while_rejects_one_hundred_thousand_and_one_iterations() {
        let code="let mut i=0;while i<=100000{i=i+1;}";
        assert!(error(code).contains("exceeds 100000"));
    }

    #[test]
    fn emitter_matches_independent_complete_expected_qasm() {
        let code="let q=qubit();let r=qubit();h(q);cx(q,r);rx(pi/2,q);let mut b=measure_keep(q);if b {x(r);} else {z(r);}measure_into(b,q);reset(q);barrier(q,r);";
        let output=sema::emit_qasm(&compile(code).unwrap());
        let expected="OPENQASM 3.0;\ninclude \"stdgates.inc\";\n\nqubit[2] q;\nbit[1] c;\n\nh q[0];\ncx q[0], q[1];\nrx(1.5707963267948966) q[0];\nc[0] = measure q[0];\nif (c[0] == 1) {\nx q[1];\n} else {\nz q[1];\n}\nc[0] = measure q[0];\nreset q[0];\nbarrier q[0], q[1];\n";
        assert_eq!(output,expected);
    }

    #[test]
    fn emitter_preserves_repeated_and_distinct_angles() {
        let code="let q=qubit();for i in 0..32{rx(pi/8,q);rz(i/100,q);}";
        let emitted=sema::emit_qasm(&compile(code).unwrap());
        assert_eq!(emitted.matches("rx(0.39269908169872414) q[0];").count(),32);
        assert_eq!(emitted.matches("rz(").count(),32);
    }


    #[test]
    fn indexed_template_validates_even_unused_scalar_arguments_every_iteration() {
        let code="fn ignore(q:&mut Qubit,t:Float){h(q);}fn main(){let q=qubit();for i in 0..8{ignore(&mut q,1/(5-i));}}";
        assert!(error(code).contains("division by zero"));
    }


    #[test]
    fn sema_prepared_indexed_math_matches_unrolled_program() {
        let source = "let q=qubit();for i in 3..38{rx(sin(i*pi/17),q);rz((i*i)/200,q);}";
        let mut flat = String::from("let q=qubit();");
        for i in 3..38 {
            flat.push_str(&format!("rx(sin(({i})*pi/17),q);rz((({i})*({i}))/200,q);"));
        }
        let compiled = compile(source).unwrap();
        let reference = compile(&flat).unwrap();
        assert_eq!(compiled.angles, reference.angles);
        assert_eq!(sema::emit_qasm(&compiled), sema::emit_qasm(&reference));
    }

    #[test]
    fn sema_prepared_scalar_checks_unused_bool_parameter() {
        let src = "fn pass(q:&mut Qubit, b:Bool, t:Float){rx(t,q);}".to_owned() +
            "fn main(){let q=qubit();for i in 0..12{pass(&mut q,i<6,i*pi/12);}}";
        let actual = compile(&src).unwrap();
        let mut flat = String::from("let q=qubit();");
        for i in 0..12 { flat.push_str(&format!("rx(({i})*pi/12,q);")); }
        assert_eq!(sema::emit_qasm(&actual),
                   sema::emit_qasm(&compile(&flat).unwrap()));
    }

    #[test]
    fn sema_prepared_preserves_lazy_false_and_dynamic_division() {
        let src = "fn pass(q:&mut Qubit, flag:Bool, theta:Float){rx(theta,q);}".to_owned() +
            "fn main(){let q=qubit();for i in 0..9{pass(&mut q,false && (1/(5-i)>0),i/9);}}";
        assert_eq!(compile(&src).unwrap().instructions.len(), 9);
    }

    #[test]
    fn sema_prepared_preserves_lazy_true_or_dynamic_division() {
        let src = "fn pass(q:&mut Qubit, flag:Bool, theta:Float){rx(theta,q);}".to_owned() +
            "fn main(){let q=qubit();for i in 0..9{pass(&mut q,true || (1/(5-i)>0),i/9);}}";
        assert_eq!(compile(&src).unwrap().instructions.len(), 9);
    }

    #[test]
    fn sema_prepared_reports_late_error_in_used_bool_argument() {
        let src = "fn pass(q:&mut Qubit, flag:Bool, theta:Float){rx(theta,q);}".to_owned() +
            "fn main(){let q=qubit();for i in 0..9{pass(&mut q,true && (1/(5-i)>0),i/9);}}";
        assert!(error(&src).contains("division by zero"));
    }

    #[test]
    fn sema_prepared_preserves_late_gate_angle_error() {
        let src = "let q=qubit();for i in 2..8{rx(1/(5-i),q);}";
        assert!(error(src).contains("division by zero"));
    }

    #[test]
    fn sema_prepared_rejects_bool_instead_of_angle() {
        assert!(error("let q=qubit();for i in 0..5{rx(i<3,q);}")
            .contains("expected Float"));
    }

    #[test]
    fn sema_prepared_keeps_math_arity_diagnostics() {
        assert!(error("let q=qubit();for i in 0..6{rx(sin(i,2),q);}")
            .contains("requires 1"));
    }

    #[test]
    fn sema_prepared_keeps_math_domain_diagnostics() {
        assert!(error("let q=qubit();for i in 0..6{rx(i+sqrt(-1),q);}")
            .contains("non-finite"));
    }

    #[test]
    fn sema_prepared_preserves_late_nonfinite_math_result() {
        assert!(error("let q=qubit();for i in 0..715{rx(exp(i),q);}")
            .contains("non-finite"));
    }

    #[test]
    fn sema_prepared_defers_invalid_constant_in_short_circuit() {
        let src = "fn test(q:&mut Qubit,b:Bool){h(q);}".to_owned() +
            "fn main(){let q=qubit();for i in 0..9{test(&mut q,false && (sqrt(-1)>i));}}";
        assert_eq!(compile(&src).unwrap().instructions.len(), 9);
    }

    #[test]
    fn sema_prepared_resolves_immutable_constants_once() {
        let src = "let t=pi/7;let q=qubit();for i in 0..32{rx(i+t,q);}";
        let mut flat = String::from("let t=pi/7;let q=qubit();");
        for i in 0..32 { flat.push_str(&format!("rx(({i})+t,q);")); }
        assert_eq!(sema::emit_qasm(&compile(src).unwrap()),
                   sema::emit_qasm(&compile(&flat).unwrap()));
    }

    #[test]
    fn sema_prepared_does_not_change_nonindexed_control_flow() {
        let input = "let q=qubit();let mut b=measure_keep(q);while b{h(q);measure_into(b,q);}x(q);";
        assert!(sema::emit_qasm(&compile(input).unwrap()).contains("while (c[0] == 1)"));
    }

    #[test]
    fn fast_float_loop_matches_unrolled_arithmetic_bit_for_bit() {
        let source = "let q=qubit();for i in 3..37{rx((i*pi)/17,q);ry((i*i+1)/200,q);rz(-(i-3),q);}";
        let mut flat = String::from("let q=qubit();");
        for i in 3..37 {
            flat.push_str(&format!("rx((({i})*pi)/17,q);ry((({i})*({i})+1)/200,q);rz(-(({i})-3),q);"));
        }
        let compiled = compile(source).unwrap();
        let reference = compile(&flat).unwrap();
        assert_eq!(compiled.angles, reference.angles);
        assert_eq!(sema::emit_qasm(&compiled), sema::emit_qasm(&reference));
    }

    #[test]
    fn fast_float_loop_handles_negative_zero_and_remainder() {
        let source = "let q=qubit();for i in 0..15{rx(-(i*0),q);rz((i+3)%4,q);}";
        let mut flat = String::from("let q=qubit();");
        for i in 0..15 {
            flat.push_str(&format!("rx(-(({i})*0),q);rz((({i})+3)%4,q);"));
        }
        let a = compile(source).unwrap();
        let b = compile(&flat).unwrap();
        assert_eq!(a.angles.iter().map(|n| n.to_bits()).collect::<Vec<_>>(),
                   b.angles.iter().map(|n| n.to_bits()).collect::<Vec<_>>());
    }

    #[test]
    fn fast_float_loop_rejects_late_division_by_zero() {
        assert!(error("let q=qubit();for i in 0..17{rx((i+1)/(12-i),q);}")
            .contains("division by zero"));
    }

    #[test]
    fn fast_float_loop_rejects_late_remainder_by_zero() {
        assert!(error("let q=qubit();for i in 0..17{rx((i+1)%(12-i),q);}")
            .contains("remainder by zero"));
    }

    #[test]
    fn fast_float_loop_preserves_short_circuit_and_math_fallback() {
        let source = "fn pass(q:&mut Qubit,flag:Bool,t:Float){rx(t,q);}".to_owned()
            + "fn main(){let q=qubit();for i in 0..9{pass(&mut q,false && (1/(5-i)>0),sin(i*pi/9));}}";
        assert_eq!(compile(&source).unwrap().instructions.len(), 9);
    }

    #[test]
    fn emitter_instrumentation_is_byte_identical_to_normal_output() {
        let source = "let a=qubit();let b=qubit();let mut v=measure_keep(a);".to_owned()
            + "while v { h(a); cx(a,b); measure_into(v,a); }"
            + "rx(pi/4,b); rz(pi/4,b); rxx(pi/3,a,b); barrier(a,b);";
        let program = compile(&source).unwrap();
        let ordinary = sema::emit_qasm(&program);
        let (profiled, stats) = sema::emit_qasm_profiled(&program);
        assert_eq!(ordinary, profiled);
        assert_eq!(stats.output_bytes, ordinary.len());
        assert!(stats.buffer_capacity >= stats.output_bytes);
    }

    #[test]
    fn emitter_cached_qubit_ids_preserve_large_operand_numbers() {
        let mut program = ir::Program::with_capacity(2);
        program.qubits = 5_000; //exceeds the deliberate emitter cache bound
        program.gate(sema::GateId::H, [ids::QubitId(4_999); 3], &[]);
        program.bits = 5_000;
        program.measure_into(ids::BitId(4_999), ids::QubitId(4_999));
        let qasm = sema::emit_qasm(&program);
        assert!(qasm.contains("h q[4999];"));
        assert!(qasm.contains("c[4999] = measure q[4999];"));
        assert_eq!(sema::emit_qasm_profiled(&program).0, qasm);
    }

    #[test]
    fn prechecked_ir_gate_matches_regular_ir_gate() {
        let mut normal = ir::Program::with_capacity(5);
        let mut checked = ir::Program::with_capacity(5);
        let qubits = [ids::QubitId(3), ids::QubitId(2), ids::QubitId(0)];
        for (gate, angles) in [
            (sema::GateId::H, vec![]),
            (sema::GateId::RZ, vec![1.25]),
            (sema::GateId::U, vec![1., 2., 3.]),
            (sema::GateId::CU, vec![1., 2., 3., 4.]),
        ] {
            normal.gate(gate, qubits, &angles);
            checked.gate_prechecked(gate, qubits, &angles);
        }
        normal.qubits = 4;
        checked.qubits = 4;
        assert_eq!(normal.angles, checked.angles);
        assert_eq!(sema::emit_qasm(&normal), sema::emit_qasm(&checked));
    }

    #[test]
    fn stress_generator_exactly_ten_thousand_ir_instructions() {
        let p = compile(&stress_source(10_000)).unwrap();
        assert_eq!(p.instructions.len(), 10_000);
        assert_eq!(p.angles.len(), 10_000);
        assert!(sema::emit_qasm(&p).contains("gphase("));
    }

    #[test]
    fn emitter_float_values_remain_byte_exact() {
        let src = "let q=qubit();rx(-0.0,q);ry(pi,q);rz(1e-8,q);";
        let p = compile(src).unwrap();
        let old = sema::emit_qasm(&p);
        assert_eq!(old, sema::emit_qasm_profiled(&p).0);
        assert!(old.contains("rx(0") || old.contains("rx(-0"));
    }

    #[test]
    fn fast_float_loop_preserves_borrow_and_qubit_liveness_checks() {
        let bad = "fn rotate(q:&mut Qubit,t:Float){rx(t,q);}".to_owned()
            + "fn main(){let q=qubit();let b=measure(q);for i in 0..7{rotate(&mut q,i*pi/7);}}";
        assert!(error(&bad).contains("consumed") || error(&bad).contains("moved"));
    }


    #[test]
    fn qasm_writer_exact_for_all_language_paths() {
        for src in [
            "let q=qubit();h(q);let b=measure(q);",
            "let a=qubit();let b=qubit();rxx(pi/3,a,b);ryy(pi/4,a,b);rzz(pi/5,a,b);",
            "let r=qubits(3);barrier(r[0],r[1],r[2]);reset(r[1]);",
            "let q=qubit();let mut bit=measure_keep(q);while bit{reset(q);measure_into(bit,q);}",
            "let q=qubit();for i in 0..40{rx(i*pi/40,q);}let b=measure(q);",
        ] {
            let program = compile(src).unwrap();
            let expected = sema::emit_qasm(&program);
            let mut bytes = Vec::new();
            let size = sema::emit_qasm_to_writer(&program, &mut bytes).unwrap();
            assert_eq!(size, expected.len());
            assert_eq!(bytes, expected.as_bytes());
        }
    }

    #[test]
    fn qasm_writer_preserves_errors() {
        struct Fail;
        impl std::io::Write for Fail {
            fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
                Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "test error"))
            }
            fn flush(&mut self) -> std::io::Result<()> { Ok(()) }
        }
        let program = compile("let q=qubit();h(q);").unwrap();
        let error = sema::emit_qasm_to_writer(&program, &mut Fail).unwrap_err();
        assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
    }

    #[test]
    fn streamed_qasm_file_byte_equal() {
        let program = compile("let q=qubit();for i in 0..50{rz(i*pi/50,q);}let b=measure(q);").unwrap();
        let target = TemporaryQasm::new();
        let bytes = stream_qasm_file(&program, &target.0).unwrap();
        let expected = sema::emit_qasm(&program);
        assert_eq!(bytes, expected.len());
        assert_eq!(fs::read(&target.0).unwrap(), expected.as_bytes());
    }
    #[test]
    fn rust_static_integer_compilation_and_overflow() {
        let src = "fn main(){let n: i64 = 4 + 3 * 2; let q=qubit(); rz(n,q);}";
        let expected = "fn main(){let q=qubit(); rz(10,q);}";
        let a = compile(src).unwrap();
        let b = compile(expected).unwrap();
        assert_eq!(sema::emit_qasm(&a), sema::emit_qasm(&b));
        assert_eq!(qcu::encode(&a).unwrap(), qcu::encode(&b).unwrap());
        assert!(compile("fn main(){let a: i64 = 9223372036854775807 + 1;}").is_err());
        assert!(compile("fn main(){let a: u64 = 0 - 1;}").is_err());
    }
    #[test]
    fn rust_static_struct_and_enum_compilation() {
        let src = "struct Pulse { angle: i64, active: bool } enum Axis { X, Y }             fn main(){let p: Pulse = Pulse { angle: 4, active: true };             let a: Axis = Axis::Y; let q=qubit();rz(p.angle,q);             match a {Axis::Y => {h(q);}, _ => {x(q);} }}";
        let expected = "fn main(){let q=qubit();rz(4,q);h(q);}";
        let a=compile(src).unwrap();
        let b=compile(expected).unwrap();
        assert_eq!(sema::emit_qasm(&a), sema::emit_qasm(&b));
        assert_eq!(qcu::encode(&a).unwrap(), qcu::encode(&b).unwrap());
    }
    #[test]
    fn rust_enum_match_exhaustiveness_integration() {
        let src = "enum Direction { N, S } fn main() {let d: Direction = Direction::S; let q=qubit();match d{Direction::N=>{x(q);},Direction::S=>{h(q);}}}";
        let expected = "fn main(){let q=qubit();h(q);}";
        assert_eq!(sema::emit_qasm(&compile(src).unwrap()),
                   sema::emit_qasm(&compile(expected).unwrap()));
        assert!(compile("enum A{X} enum B{X} fn main(){let a:A=A::X; match a {B::X=>{}}}").is_err());
    }
    #[test]
    fn rust_static_exactness_not_truncated_to_f64() {
        let source="fn main(){let n: i64 = 9007199254740993; let q=qubit();h(q);}";
        assert!(compile(source).is_ok());
        assert!(compile("fn main(){let n: i64 = 9007199254740993; let q=qubit();rz(n,q);}").is_err());
    }
}
