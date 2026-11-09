//Central registry of QRust language surface features

pub const SURFACE_REVISION: u32 = 5;

pub fn reserved_identifier(name: &str) -> bool {
    name.starts_with("__qrust_") || reserved_keyword(name)
}

pub fn reserved_keyword(name: &str) -> bool {
    matches!(name,
        "struct" | "enum" | "impl" | "trait" |
        "pi" | "tau" | "e" | "true" | "false" |
        "let" | "const" | "mut" | "fn" | "if" | "else" | "for" | "in" |
        "while" | "return" | "match" | "loop" | "break" | "continue" |
        "async" | "await" | "move")
}

pub const CAPABILITIES: &[(&str, &str)] = &[
    ("edition", "Rust 2024-inspired subset; QRust is not a rustc replacement"),
    ("static-scalars", "Float/f64, Bool/bool, mutable and const scalars"),
    ("static-match", "compile-time match with bool/integer patterns and wildcard"),
    ("inclusive-range", "for i in a..=b with compile-time bounds"),
    ("compound-assign", "+= -= *= /= %= for mutable compile-time floats"),
    ("static-loop-control", "loop/break/continue statically expanded; not hardware QPU jumps"),
    ("auto-inference", "let x = expr or let x: _ = expr infers Float/Bool/Qubit/Bit, no runtime tagging"),
    ("quantum-ownership", "linear Qubit handles and explicit &mut Qubit borrowing"),
    ("runtime-feedback", "measurement-Bit if/while with safety checks"),
    ("qasm3", "OpenQASM 3 emitter with atomic streamed output"),
    ("qcu-interchange", "device-neutral QCU interchange v1"),
    ("expr-arena-fast", "topological scalar evaluation without task stack when no &&/||"),
    ("async-ir-preview", "validated host-side future plans; async/await source execution remains unsupported"),
    ("exact-integer-ct", "exact checked i64/u64 compile-time values, with f64 boundary checks"),
    ("struct-enum-ct", "compile-time scalar structs and fieldless enums; no runtime layout/ABI"),
];

pub fn declaration_type(name: &str) -> Option<crate::syntax::Type> {
    use crate::syntax::Type;
    match name {
        "Float" | "f64" => Some(Type::Float),
        "Bool" | "bool" => Some(Type::Bool),
        "Qubit" => Some(Type::Qubit),
        "Bit" => Some(Type::Bit),
        _ => None,
    }
}

pub fn scalar_parameter_type(name: &str) -> Option<crate::syntax::ParamType> {
    use crate::syntax::ParamType;
    match name {
        "Float" | "f64" => Some(ParamType::Float),
        "Bool" | "bool" => Some(ParamType::Bool),
        _ => None,
    }
}
