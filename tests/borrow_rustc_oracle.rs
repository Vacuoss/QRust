use std::{collections::{HashMap,HashSet}, env, fs, path::PathBuf, process::Command};

const MANIFEST: &str = include_str!("rustc_borrow_cases/manifest.tsv");

#[derive(Debug)]
struct Case<'a> {
    id:&'a str,
    category:&'a str,
    rust_accept:bool,
    paired:bool,
    diagnostic:&'a str,
    interpretation:&'a str,
}
fn cases() -> Vec<Case<'static>> {
    MANIFEST.lines().filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let fields:Vec<_> = line.split('\t').collect();
            assert_eq!(fields.len(),6,"audit manifest has malformed line: {line}");
            let rust_accept = match fields[2]{"accept"=>true,"reject"=>false,_=>panic!("unknown rustc verdict: {line}")};
            let paired = match fields[3]{"paired"=>true,"rustc_only"=>false,_=>panic!("unknown comparison mode: {line}")};
            Case{id:fields[0],category:fields[1],rust_accept,paired,
                 diagnostic:fields[4],interpretation:fields[5]}
        }).collect()
}
fn requires_symbolic_branch(id:&str)->bool {
    matches!(id,"cfg_diamond_last_use"|"cfg_future_shared_use"|
        "return_shared_phi_owner_move")
}
fn fixtures() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/rustc_borrow_cases")
}

#[test]
fn manifest_covers_distinct_rust_borrow_rules() {
    let cases=cases();
    assert!(cases.len()>=25,"audit needs both positive and negative cases");
    let mut ids=HashSet::new();
    let mut modes=HashMap::<&str,(usize,usize)>::new();
    for case in &cases {
        assert!(ids.insert(case.id),"duplicate audit case {}",case.id);
        assert!(case.id.bytes().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c==b'_'));
        assert!(!case.interpretation.trim().is_empty());
        assert!(fixtures().join(format!("{}.rs",case.id)).is_file(),"missing rustc fixture: {}",case.id);
        assert_eq!(fixtures().join(format!("{}.qr",case.id)).is_file(),case.paired,
            "QRust fixtures must exist exactly for paired cases: {}",case.id);
        let tally=modes.entry(case.category).or_default();
        if case.rust_accept{tally.0+=1;}else{tally.1+=1;}
        if !case.rust_accept {assert_ne!(case.diagnostic,"-","negative rustc fixture needs a diagnostic witness: {}",case.id);}
        if case.paired {
            let qr_source=fs::read_to_string(fixtures().join(format!("{}.qr",case.id)))
                .expect("missing paired QRust fixture");
            let before_main=qr_source.split("fn main(").next().unwrap_or("");
            for builtin in ["qubit(","rx(","ry(","rz(","h(","cx("] {
                assert!(!before_main.contains(builtin),
                    "paired fixture {} invokes quantum builtin {} inside a typed helper",case.id,builtin);
            }
        }
        if requires_symbolic_branch(case.id) {
            let rust=fs::read_to_string(fixtures().join(format!("{}.rs",case.id)))
                .expect("missing Rust symbolic branch fixture");
            let qrust=fs::read_to_string(fixtures().join(format!("{}.qr",case.id)))
                .expect("missing QRust symbolic branch fixture");
            assert!(case.paired && rust.contains("if flag") &&
                qrust.contains("if flag") && qrust.contains("flag:bool") &&
                !qrust.contains("if true") && !qrust.contains("if false"),
                "CFG comparator {} must preserve a symbolic function parameter",case.id);
        }
    }
    for category in ["nll","reborrow","move_path","cfg","region","return_phi"] {
        let (accept,reject)=modes.get(category).copied().expect("missing audit category");
        assert!(accept>0 && reject>0,"category {category} needs positive and negative evidence");
    }
    assert!(cases.iter().any(|case| !case.paired),"unsupported surface gaps must be explicit");
}

#[test]
fn rustc_oracle_and_qrust_typed_frontend_agree_on_paired_cases() {
    let root=fixtures();
    let rustc=env::var_os("RUSTC").unwrap_or_else(||"rustc".into());
    let qrust=env!("CARGO_BIN_EXE_qrust");
    let temp=env::temp_dir().join(format!("qrust-rustc-oracle-{}",std::process::id()));
    fs::create_dir_all(&temp).expect("cannot create temporary rustc output directory");
    let mut paired=0usize;
    let mut unsupported=0usize;
    let mut mismatches=Vec::<String>::new();
    for case in cases() {
        let rust_output=Command::new(&rustc)
            .args(["--edition=2024","--crate-type=lib","--crate-name=borrow_oracle",
                   "--emit=metadata","-A","warnings"])
            .arg("-o").arg(temp.join("oracle.rmeta"))
            .arg(root.join(format!("{}.rs",case.id)))
            .output().unwrap_or_else(|e|panic!("could not run rustc for {}: {e}",case.id));
        let rust_ok=rust_output.status.success();
        let rust_err=String::from_utf8_lossy(&rust_output.stderr);
        assert_eq!(rust_ok,case.rust_accept,
            "rustc oracle changed for {} ({}): {}",case.id,case.category,rust_err);
        if !rust_ok {
            assert!(case.diagnostic.split('|').any(|hint|rust_err.contains(hint)),
                "rustc rejected {} for an unexpected reason: {}",case.id,rust_err);
        }
        if !case.paired {
            unsupported+=1;
            continue; //Not a semantic mismatch: QRust does not expose this Rust feature
        }
        let result=Command::new(qrust).arg("check")
            .arg(root.join(format!("{}.qr",case.id)))
            .output().unwrap_or_else(|e|panic!("could not run QRust for {}: {e}",case.id));
        let qrust_ok=result.status.success();
        let diagnostic=String::from_utf8_lossy(&result.stderr);
        if qrust_ok != rust_ok {
            mismatches.push(format!(
                "BORROW DIFFERENTIAL {} {}: rustc={}, qrust={}; QRust stderr: {}",
                case.category,case.id,rust_ok,qrust_ok,diagnostic));
        } else if !qrust_ok {
            let lowered=diagnostic.to_ascii_lowercase();
            let borrow_markers=["borrow","loan","reborrow","suspend","conflict",
                                "move","moved","lifetime","reference escapes","consumed"];
            let surface_markers=["unexpected token","unsupported syntax","not yet supported",
                "unknown function","unknown typed function","unknown type",
                "expected expression","parse error","unsupported construct"];
            if surface_markers.iter().any(|word|lowered.contains(word)) {
                mismatches.push(format!(
                    "QRust fixture {} was rejected by the language surface instead of the borrow rule: {}",
                    case.id,diagnostic));
            } else if !borrow_markers.iter().any(|word|lowered.contains(word)) {
                mismatches.push(format!(
                    "QRust rejection for {} has no causal borrow/region evidence: {}",
                    case.id,diagnostic));
            }
        }
        paired+=1;
    }
    println!("rustc differential audit: {paired} paired cases; {unsupported} rustc-only gaps");
    let _=fs::remove_dir_all(temp);
    assert!(mismatches.is_empty(),"{} borrow-audit discrepancies found:\n{}",
        mismatches.len(),mismatches.join("\n\n"));
}
