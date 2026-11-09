//QRust 0.5 static semantics: canonical gate registry, typed constant
use std::collections::{HashMap, HashSet};
use std::io;
use std::time::{Duration, Instant};
use crate::syntax::{BinaryOp, Diagnostic, Expr, ExprArena, ExprNode, Position, Stmt, Type, UnaryOp};
use crate::math;
use crate::ids::{SymbolTable, QubitId};
use crate::ir::{OpCode, Program};

#[repr(u8)]
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GateId { ID, H, X, Y, Z, S, SDG, T, TDG, SX, P, RX, RY, RZ, U, U2, U3,
    CX, LEGACY_CX, CY, CZ, CH, SWAP, CP, CRX, CRY, CRZ, CU, CCX, CSWAP, GPHASE,
    RXX, RYY, RZZ }

#[derive(Clone, Copy, Debug)]
pub struct GateSpec {
    pub id: GateId,
    pub name: &'static str,
    pub qasm: &'static str,
    pub parameters: usize,
    pub qubits: usize,
}
macro_rules! gate {
    ($id:ident, $name:literal, $qasm:literal, $params:expr, $qubits:expr) => {
        static $id: GateSpec = GateSpec { id: GateId::$id, name: $name, qasm: $qasm, parameters: $params, qubits: $qubits };
    };
}
gate!(ID,"id","id",0,1); gate!(H,"h","h",0,1);
gate!(X,"x","x",0,1); gate!(Y,"y","y",0,1); gate!(Z,"z","z",0,1);
gate!(S,"s","s",0,1); gate!(SDG,"sdg","sdg",0,1);
gate!(T,"t","t",0,1); gate!(TDG,"tdg","tdg",0,1); gate!(SX,"sx","sx",0,1);
gate!(P,"p","p",1,1); gate!(RX,"rx","rx",1,1);
gate!(RY,"ry","ry",1,1); gate!(RZ,"rz","rz",1,1);
gate!(U,"u","U",3,1); gate!(U2,"u2","u2",2,1); gate!(U3,"u3","u3",3,1);
gate!(CX,"cx","cx",0,2); gate!(LEGACY_CX,"CX","CX",0,2);
gate!(CY,"cy","cy",0,2); gate!(CZ,"cz","cz",0,2);
gate!(CH,"ch","ch",0,2); gate!(SWAP,"swap","swap",0,2);
gate!(CP,"cp","cp",1,2); gate!(CRX,"crx","crx",1,2);
gate!(CRY,"cry","cry",1,2); gate!(CRZ,"crz","crz",1,2);
gate!(CU,"cu","cu",4,2); gate!(CCX,"ccx","ccx",0,3);
gate!(CSWAP,"cswap","cswap",0,3); gate!(GPHASE,"gphase","gphase",1,0);
gate!(RXX,"rxx","rxx",1,2); gate!(RYY,"ryy","ryy",1,2); gate!(RZZ,"rzz","rzz",1,2);

pub static STANDARD_GATES: &[&GateSpec] = &[
    &ID,&H,&X,&Y,&Z,&S,&SDG,&T,&TDG,&SX,&P,&RX,&RY,&RZ,
    &U,&U2,&U3,&CX,&LEGACY_CX,&CY,&CZ,&CH,&SWAP,&CP,&CRX,&CRY,
    &CRZ,&CU,&CCX,&CSWAP,&GPHASE,
];
pub static EXTENDED_GATES: &[&GateSpec] = &[&RXX,&RYY,&RZZ];
static GATE_SPECS: &[&GateSpec] = &[
    &ID,&H,&X,&Y,&Z,&S,&SDG,&T,&TDG,&SX,&P,&RX,&RY,&RZ,
    &U,&U2,&U3,&CX,&LEGACY_CX,&CY,&CZ,&CH,&SWAP,&CP,&CRX,&CRY,
    &CRZ,&CU,&CCX,&CSWAP,&GPHASE,&RXX,&RYY,&RZZ,
];
pub fn gate_spec(id: GateId) -> &'static GateSpec { GATE_SPECS[id as usize] }
pub fn gate_id_from_raw(raw: u8) -> Option<GateId> { GATE_SPECS.get(raw as usize).map(|s| s.id) }


fn gate_by_name(name: &str) -> Option<&'static GateSpec> {
    Some(match name {
        "id" | "i" => &ID,
        "h" | "H" => &H, "x" | "X" => &X, "y" | "Y" => &Y,
        "z" | "Z" => &Z, "s" | "S" => &S, "sdg" => &SDG,
        "t" | "T" => &T, "tdg" => &TDG, "sx" => &SX,
        "p" | "phase" | "u1" => &P,
        "rx" => &RX, "ry" => &RY, "rz" => &RZ,
        "u" | "U" => &U, "u2" => &U2, "u3" => &U3,
        "cx" | "cnot" => &CX, "CX" => &LEGACY_CX,
        "cy" => &CY, "cz" => &CZ, "ch" => &CH,
        "swap" => &SWAP, "cp" | "cphase" => &CP,
        "crx" => &CRX, "cry" => &CRY, "crz" => &CRZ,
        "cu" => &CU, "ccx" | "toffoli" => &CCX,
        "cswap" | "fredkin" => &CSWAP,
        "gphase" => &GPHASE,
        "rxx" => &RXX, "ryy" => &RYY, "rzz" => &RZZ,
        _ => return None,
    })
}

pub(crate) fn is_gate(name: &str) -> bool { gate_by_name(name).is_some() }
pub(crate) fn gate_id(name: &str) -> Option<GateId> { gate_by_name(name).map(|spec| spec.id) }

#[derive(Clone, Copy, Debug)]
enum Symbol { Qubit(QubitId), Bit(crate::ids::BitId), Number(f64), Bool(bool), Moved }

#[derive(Clone, Copy, Debug)]
pub(crate) enum Scalar { Float(f64), Bool(bool) }
impl Scalar {
    fn numeric(self, at: Position) -> Result<f64, Diagnostic> {
        match self { Self::Float(v) => Ok(v), Self::Bool(_) => Err(err(at, "expected Float, got Bool")) }
    }
    fn boolean(self, at: Position) -> Result<bool, Diagnostic> {
        match self { Self::Bool(v) => Ok(v), Self::Float(_) => Err(err(at, "expected Bool, got Float")) }
    }
}

fn err(at: Position, message: impl Into<String>) -> Diagnostic { Diagnostic { at, message: message.into() } }

fn check_name(symbols: &SymbolTable<Symbol>, name: &str, at: Position) -> Result<(), Diagnostic> {
    if crate::surface::reserved_keyword(name) {
        return Err(err(at, format!("'{name}' is a reserved constant or keyword")));
    }
    if symbols.contains_key(name) {
        Err(err(at, format!("name '{name}' is already declared (shadowing is not supported yet)")))
    } else { Ok(()) }
}

fn live_qubit(symbols: &SymbolTable<Symbol>, name: &str, at: Position) -> Result<QubitId, Diagnostic> {
    match symbols.get(name) {
        Some(Symbol::Qubit(id)) => Ok(id),
        Some(Symbol::Bit(_)) => Err(err(at, format!("'{name}' is a classical bit, not a qubit"))),
        Some(Symbol::Number(_)) => Err(err(at, format!("'{name}' is a number, not a qubit"))),
        Some(Symbol::Bool(_)) => Err(err(at, format!("'{name}' is a boolean, not a qubit"))),
        Some(Symbol::Moved) => Err(err(at, format!("use of consumed or moved qubit '{name}'"))),
        None => Err(err(at, format!("unknown variable '{name}'"))),
    }
}
fn qubit_arg(expr: &Expr, symbols: &SymbolTable<Symbol>, at: Position) -> Result<QubitId, Diagnostic> {
    if let Expr::Var(name) = expr { live_qubit(symbols, name, at) }
    else { Err(err(at, "a qubit argument must be a named live qubit")) }
}

fn checked_float(result: Scalar, at: Position) -> Result<Scalar, Diagnostic> {
    match result {
        Scalar::Float(n) if !n.is_finite() => Err(err(at, "non-finite result in numeric expression")),
        _ => Ok(result),
    }
}

fn scalar_binary(lhs: Scalar, op: BinaryOp, rhs: Scalar, at: Position) -> Result<Scalar, Diagnostic> {
    let value = match op {
        BinaryOp::Eq | BinaryOp::Ne => {
            let same = match (lhs, rhs) {
                (Scalar::Float(x), Scalar::Float(y)) => x == y,
                (Scalar::Bool(x), Scalar::Bool(y)) => x == y,
                _ => return Err(err(at, "comparison requires operands of the same type")),
            };
            Scalar::Bool(if matches!(op, BinaryOp::Eq) { same } else { !same })
        }
        BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
            let x = lhs.numeric(at)?; let y = rhs.numeric(at)?;
            Scalar::Bool(match op {
                BinaryOp::Lt => x < y, BinaryOp::Le => x <= y,
                BinaryOp::Gt => x > y, BinaryOp::Ge => x >= y, _ => unreachable!(),
            })
        }
        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem => {
            let x = lhs.numeric(at)?; let y = rhs.numeric(at)?;
            Scalar::Float(match op {
                BinaryOp::Add => x + y, BinaryOp::Sub => x - y,
                BinaryOp::Mul => x * y,
                BinaryOp::Div => {
                    if y == 0.0 { return Err(err(at, "division by zero in constant expression")); }
                    x / y
                }
                BinaryOp::Rem => {
                    if y == 0.0 { return Err(err(at, "remainder by zero in constant expression")); }
                    x % y
                }
                _ => unreachable!(),
            })
        }
        BinaryOp::And | BinaryOp::Or => unreachable!("lazy boolean operators are dispatched separately"),
    };
    checked_float(value, at)
}

fn scalar_arena_with(arena: &ExprArena, get: &impl Fn(&str) -> Option<Symbol>, at: Position)
    -> Result<Scalar, Diagnostic> {
    if !arena.has_short_circuit {
        let mut values = Vec::<Scalar>::with_capacity(arena.nodes.len());
        for node in &arena.nodes {
            let value = match node {
                ExprNode::Atom(expr) => scalar_with(expr, get, at)?,
                ExprNode::Binary { left, op, right } => {
                    scalar_binary(values[*left as usize], *op, values[*right as usize], at)?
                }
            };
            values.push(value);
        }
        return Ok(values[arena.root as usize]);
    }
    enum Task { Visit(u32), Apply(BinaryOp), ShortCircuit(BinaryOp, u32) }
    let mut tasks = Vec::with_capacity(32);
    let mut values = Vec::<Scalar>::with_capacity(16);
    tasks.push(Task::Visit(arena.root));
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(id) => match &arena.nodes[id as usize] {
                ExprNode::Atom(expr) => values.push(scalar_with(expr, get, at)?),
                ExprNode::Binary { left, op, right } => {
                    if matches!(*op, BinaryOp::And | BinaryOp::Or) {
                        tasks.push(Task::ShortCircuit(*op, *right));
                        tasks.push(Task::Visit(*left));
                    } else {
                        tasks.push(Task::Apply(*op));
                        tasks.push(Task::Visit(*right));
                        tasks.push(Task::Visit(*left));
                    }
                }
            },
            Task::ShortCircuit(op, right) => {
                let lhs = values.pop().unwrap().boolean(at)?;
                if matches!(op, BinaryOp::And) && !lhs {
                    values.push(Scalar::Bool(false));
                } else if matches!(op, BinaryOp::Or) && lhs {
                    values.push(Scalar::Bool(true));
                } else {
                    values.push(Scalar::Bool(lhs));
                    tasks.push(Task::Apply(op));
                    tasks.push(Task::Visit(right));
                }
            }
            Task::Apply(op) => {
                let rhs = values.pop().unwrap();
                let lhs = values.pop().unwrap();
                let result = match op {
                    BinaryOp::And => Scalar::Bool(lhs.boolean(at)? && rhs.boolean(at)?),
                    BinaryOp::Or => Scalar::Bool(lhs.boolean(at)? || rhs.boolean(at)?),
                    _ => scalar_binary(lhs, op, rhs, at)?,
                };
                values.push(checked_float(result, at)?);
            }
        }
    }
    debug_assert_eq!(values.len(), 1);
    Ok(values.pop().unwrap())
}

fn scalar_with(expr: &Expr, get: &impl Fn(&str) -> Option<Symbol>, at: Position) -> Result<Scalar, Diagnostic> {
    let output = match expr {
        Expr::Arena(arena) => scalar_arena_with(arena, get, at)?,
        Expr::Number(v) => Scalar::Float(*v),
        Expr::Bool(v) => Scalar::Bool(*v),
        Expr::Var(name) => match name.as_str() {
            "pi" => Scalar::Float(std::f64::consts::PI),
            "tau" => Scalar::Float(std::f64::consts::TAU),
            "e" => Scalar::Float(std::f64::consts::E),
            _ => match get(name) {
                Some(Symbol::Number(v)) => Scalar::Float(v),
                Some(Symbol::Bool(v)) => Scalar::Bool(v),
                Some(Symbol::Qubit(_)) => return Err(err(at, format!("'{name}' is a qubit, not a scalar"))),
                Some(Symbol::Bit(_)) => return Err(err(at, format!("'{name}' is a bit, not a compile-time scalar"))),
                Some(Symbol::Moved) => return Err(err(at, format!("'{name}' was moved"))),
                None => return Err(err(at, format!("unknown numeric constant or bool '{name}'"))),
            },
        },
        Expr::Unary(op, inner) => match op {
            UnaryOp::Neg => Scalar::Float(-scalar_with(inner, get, at)?.numeric(at)?),
            UnaryOp::Not => Scalar::Bool(!scalar_with(inner, get, at)?.boolean(at)?),
        },
        Expr::Binary(a, BinaryOp::And, b) => {
            let lhs = scalar_with(a, get, at)?.boolean(at)?;
            Scalar::Bool(lhs && scalar_with(b, get, at)?.boolean(at)?)
        }
        Expr::Binary(a, BinaryOp::Or, b) => {
            let lhs = scalar_with(a, get, at)?.boolean(at)?;
            Scalar::Bool(lhs || scalar_with(b, get, at)?.boolean(at)?)
        }
        Expr::Binary(a, op, b) => {
            let lhs = scalar_with(a, get, at)?;
            let rhs = scalar_with(b, get, at)?;
            scalar_binary(lhs, *op, rhs, at)?
        }
        Expr::Index { .. } => return Err(err(at, "register indexes must be resolved before semantic checking")),
        Expr::BorrowMut(_) => return Err(err(at, "'&mut' is only valid as a function argument")),
        Expr::Call { name, args } => {
            let arity = math::arity(name).ok_or_else(|| err(at, format!("unknown numeric function '{name}'")))?;
            if args.len() != arity {
                return Err(err(at, format!("'{name}' requires {arity} numeric argument(s), got {}", args.len())));
            }
            let mut values = [0.0_f64; 3];
            for (index, arg) in args.iter().enumerate() {
                values[index] = scalar_with(arg, get, at)?.numeric(at)?;
            }
            Scalar::Float(math::evaluate(name, &values[..arity]).map_err(|message| err(at, message))?)
        }
    };
    match output {
        Scalar::Float(n) if !n.is_finite() => Err(err(at, "non-finite result in numeric expression")),
        _ => Ok(output),
    }
}

fn scalar(expr: &Expr, symbols: &SymbolTable<Symbol>, at: Position) -> Result<Scalar, Diagnostic> {
    scalar_with(expr, &|name| symbols.get(name), at)
}

pub(crate) fn eval_constant(expr: &Expr, constants: &HashMap<String, Scalar>, at: Position)
    -> Result<Scalar, Diagnostic> {
    scalar_with(expr, &|name| constants.get(name).map(|v| match v {
        Scalar::Float(n) => Symbol::Number(*n), Scalar::Bool(b) => Symbol::Bool(*b)
    }), at)
}

fn numeric(expr: &Expr, symbols: &SymbolTable<Symbol>, at: Position) -> Result<f64, Diagnostic> {
    scalar(expr, symbols, at)?.numeric(at)
}

fn distinct(ids: &[QubitId], name: &str, at: Position) -> Result<(), Diagnostic> {
    if ids.len() < 8 {
        for (index, &id) in ids.iter().enumerate() {
            if ids[..index].contains(&id) {
                return Err(err(at, if name == "cx" || name == "CX" {
                    "CX control and target must be distinct qubits".to_owned()
                } else { format!("'{name}' requires distinct qubit operands") }));
            }
        }
    } else {
        let mut seen = HashSet::with_capacity(ids.len());
        for id in ids {
            if !seen.insert(*id) { return Err(err(at, format!("'{name}' requires distinct qubit operands"))); }
        }
    }
    Ok(())
}
fn check_arguments(name: &str, actual: usize, expected: usize, at: Position) -> Result<(), Diagnostic> {
    if actual == expected { Ok(()) }
    else { Err(err(at, format!("'{name}' requires {expected} argument(s), got {actual}"))) }
}
fn emit_measure(args: &[Expr], retain: bool, symbols: &mut SymbolTable<Symbol>,
    output: &mut Program, at: Position) -> Result<crate::ids::BitId, Diagnostic> {
    check_arguments(if retain { "measure_keep" } else { "measure" }, args.len(), 1, at)?;
    let qubit = qubit_arg(&args[0], symbols, at)?;
    if !retain {
        if let Expr::Var(name) = &args[0] { symbols.insert(name, Symbol::Moved); }
    }
    Ok(output.measure(qubit))
}
fn statement_call(name: &str, args: &[Expr], symbols: &mut SymbolTable<Symbol>,
    mutable_bits: &HashSet<crate::ids::SymbolId>, output: &mut Program, at: Position) -> Result<(), Diagnostic> {
    match name {
        "measure" | "measure_keep" => {
            emit_measure(args, name == "measure_keep", symbols, output, at)?; Ok(())
        }
        "measure_into" => {
            check_arguments(name, args.len(), 2, at)?;
            let Expr::Var(bit_name) = &args[0] else {
                return Err(err(at, "measure_into expects a named mutable Bit"));
            };
            let bit = match symbols.get(bit_name) {
                Some(Symbol::Bit(id)) if symbols.id(bit_name).is_some_and(|key| mutable_bits.contains(&key)) => id,
                _ => return Err(err(at, "measure_into expects a mutable Bit declared with let mut")),
            };
            let qubit = qubit_arg(&args[1], symbols, at)?;
            output.measure_into(bit, qubit);
            Ok(())
        }
        "reset" => {
            check_arguments(name, args.len(), 1, at)?;
            output.reset(qubit_arg(&args[0], symbols, at)?); Ok(())
        }
        "barrier" => {
            if args.is_empty() { return Err(err(at, "'barrier' requires at least one qubit")); }
            let mut ids = Vec::with_capacity(args.len());
            for arg in args { ids.push(qubit_arg(arg, symbols, at)?); }
            distinct(&ids, name, at)?;
            output.barrier(&ids); Ok(())
        }
        _ => {
            let spec = gate_by_name(name).ok_or_else(|| err(at, format!("unknown operation '{name}'")))?;
            check_arguments(name, args.len(), spec.parameters + spec.qubits, at)?;
            let mut parameters = [0.0; 4];
            let mut qubits = [QubitId(0); 3];
            for (i, param) in parameters.iter_mut().take(spec.parameters).enumerate() {
                *param = numeric(&args[i], symbols, at)?;
            }
            for (i, q) in qubits.iter_mut().take(spec.qubits).enumerate() {
                *q = qubit_arg(&args[spec.parameters + i], symbols, at)?;
            }
            distinct(&qubits[..spec.qubits], spec.name, at)?;
            output.gate(spec.id, qubits, &parameters[..spec.parameters]); Ok(())
        }
    }
}
fn symbol_type(s: Symbol) -> Option<Type> {
    Some(match s {
        Symbol::Number(_) => Type::Float, Symbol::Bool(_) => Type::Bool,
        Symbol::Qubit(_) => Type::Qubit, Symbol::Bit(_) => Type::Bit,
        Symbol::Moved => return None,
    })
}

//Runtime CFG validation: branch inputs/outputs have the same qubit ownership environment, and a loop's
//controlling Bit must be definitely refreshed
fn runtime_bit(expr: &Expr, symbols: &SymbolTable<Symbol>, at: Position)
    -> Result<crate::ids::BitId, Diagnostic> {
    let Expr::Var(name) = expr else { return Err(err(at, "runtime control expects a named measurement Bit")); };
    match symbols.get(name) {
        Some(Symbol::Bit(id)) => Ok(id),
        _ => Err(err(at, "runtime control condition must be a measurement Bit")),
    }
}

fn arm_definitely_writes(arm: &[Stmt], bit: crate::ids::BitId,
    symbols: &SymbolTable<Symbol>) -> bool {
    arm.iter().any(|stmt| match stmt {
        Stmt::Call { name, args, .. } if name == "measure_into" => {
            if let Some(Expr::Var(name)) = args.first() {
                matches!(symbols.get(name), Some(Symbol::Bit(found)) if found == bit)
            } else { false }
        }
        Stmt::RuntimeIf { then_branch, else_branch, .. } =>
            arm_definitely_writes(then_branch, bit, symbols) &&
            arm_definitely_writes(else_branch, bit, symbols),
        _ => false,
    })
}

fn check_runtime_arm(arm: &[Stmt], symbols: &mut SymbolTable<Symbol>,
    mutable_bits: &HashSet<crate::ids::SymbolId>, output: &mut Program,
    at: Position) -> Result<(), Diagnostic> {
    for stmt in arm {
        match stmt {
            Stmt::Call { name, args, at: call_at }
                if is_gate(name) || matches!(name.as_str(), "reset" | "barrier" | "measure_into") =>
                statement_call(name, args, symbols, mutable_bits, output, *call_at)?,
            Stmt::RuntimeIf { bit, expected, then_branch, else_branch, at: if_at } => {
                let bit_id = runtime_bit(bit, symbols, *if_at)?;
                output.begin_if(bit_id, *expected);
                check_runtime_arm(then_branch, symbols, mutable_bits, output, *if_at)?;
                if !else_branch.is_empty() {
                    output.else_branch();
                    check_runtime_arm(else_branch, symbols, mutable_bits, output, *if_at)?;
                }
                output.end_if();
            }
            _ => return Err(err(at,
                "runtime branches must preserve Qubit ownership and use only gates, reset, barrier, measure_into or nested if")),
        }
    }
    Ok(())
}

enum LoopScalar<'a> {
    FastNumeric(Box<[FastFloatOp]>),
    Known(Scalar),
    Rejected(Diagnostic),
    Index,
    Arena { arena: &'a ExprArena, index_name: String, known: HashMap<String, Symbol> },
    Unary(UnaryOp, Box<LoopScalar<'a>>),
    Binary(Box<LoopScalar<'a>>, BinaryOp, Box<LoopScalar<'a>>),
    Call { name: &'a str, arity: Option<usize>, args: Box<[LoopScalar<'a>]> },
}


#[derive(Clone, Copy)]
enum FastFloatOp {
    Number(f64), Index, Neg, Add, Sub, Mul, Div, Rem,
}

const FAST_FLOAT_STACK: usize = 16;
const FAST_FLOAT_MAX_OPS: usize = 96;

fn compile_fast_float(expr: &Expr, index: &str, symbols: &SymbolTable<Symbol>,
    at: Position, ops: &mut Vec<FastFloatOp>, depth: &mut usize, peak: &mut usize) -> bool {
    if ops.len() >= FAST_FLOAT_MAX_OPS { return false; }
    //Resolve constant subtrees with the existing evaluator. Rejected values must fall back: their
    //diagnostics may be protected by && or ||
    if !loop_uses_index(expr, index) {
        if let Ok(Scalar::Float(value)) = scalar(expr, symbols, at) {
            if value.is_finite() {
                ops.push(FastFloatOp::Number(value));
                *depth += 1;
                *peak = (*peak).max(*depth);
                return *peak <= FAST_FLOAT_STACK;
            }
        }
        return false;
    }
    match expr {
        Expr::Var(name) if name == index => {
            ops.push(FastFloatOp::Index);
            *depth += 1;
            *peak = (*peak).max(*depth);
            *peak <= FAST_FLOAT_STACK
        }
        Expr::Unary(UnaryOp::Neg, inner) => {
            if !compile_fast_float(inner, index, symbols, at, ops, depth, peak) { return false; }
            ops.push(FastFloatOp::Neg);
            true
        }
        Expr::Binary(lhs, op, rhs) if matches!(op,
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem) => {
            if !compile_fast_float(lhs, index, symbols, at, ops, depth, peak) { return false; }
            if !compile_fast_float(rhs, index, symbols, at, ops, depth, peak) { return false; }
            ops.push(match op {
                BinaryOp::Add => FastFloatOp::Add,
                BinaryOp::Sub => FastFloatOp::Sub,
                BinaryOp::Mul => FastFloatOp::Mul,
                BinaryOp::Div => FastFloatOp::Div,
                BinaryOp::Rem => FastFloatOp::Rem,
                _ => unreachable!(),
            });
            *depth -= 1;
            true
        }
        _ => false,
    }
}

fn fast_float_program(expr: &Expr, index: &str,
    symbols: &SymbolTable<Symbol>, at: Position) -> Option<Box<[FastFloatOp]>> {
    if !loop_uses_index(expr, index) { return None; }
    let mut ops = Vec::with_capacity(12);
    let mut depth = 0;
    let mut peak = 0;
    if compile_fast_float(expr, index, symbols, at, &mut ops, &mut depth, &mut peak)
        && depth == 1 && ops.len() <= FAST_FLOAT_MAX_OPS {
        Some(ops.into_boxed_slice())
    } else { None }
}

fn eval_fast_float(ops: &[FastFloatOp], index: f64, at: Position)
    -> Result<f64, Diagnostic> {
    let mut stack = [0.0_f64; FAST_FLOAT_STACK];
    let mut len = 0usize;
    for operation in ops {
        let value = match *operation {
            FastFloatOp::Number(value) => { stack[len] = value; len += 1; continue; }
            FastFloatOp::Index => { stack[len] = index; len += 1; continue; }
            FastFloatOp::Neg => -stack[len - 1],
            kind => {
                let a = stack[len - 2];
                let b = stack[len - 1];
                let result = match kind {
                    FastFloatOp::Add => a + b,
                    FastFloatOp::Sub => a - b,
                    FastFloatOp::Mul => a * b,
                    FastFloatOp::Div => {
                        if b == 0.0 { return Err(err(at, "division by zero in constant expression")); }
                        a / b
                    }
                    FastFloatOp::Rem => {
                        if b == 0.0 { return Err(err(at, "remainder by zero in constant expression")); }
                        a % b
                    }
                    _ => unreachable!(),
                };
                len -= 1;
                result
            }
        };
        if !value.is_finite() {
            return Err(err(at, "non-finite result in numeric expression"));
        }
        stack[len - 1] = value;
    }
    debug_assert_eq!(len, 1);
    Ok(stack[0])
}

fn loop_uses_index(expr: &Expr, index: &str) -> bool {
    match expr {
        Expr::Arena(arena) => arena.atoms().any(|expr| loop_uses_index(expr, index)),
        Expr::Var(name) => name.as_str() == index,
        Expr::Number(_) | Expr::Bool(_) => false,
        Expr::Unary(_, x) | Expr::BorrowMut(x) => loop_uses_index(x, index),
        Expr::Binary(a, _, b) => loop_uses_index(a, index) || loop_uses_index(b, index),
        Expr::Call { args, .. } => args.iter().any(|x| loop_uses_index(x, index)),
        Expr::Index { name, index: expr } => name.as_str() == index || loop_uses_index(expr, index),
    }
}

fn collect_arena_symbols(expr: &Expr, index: &str, symbols: &SymbolTable<Symbol>,
    known: &mut HashMap<String, Symbol>) {
    match expr {
        Expr::Var(name) if name.as_str() != index => {
            if let Some(symbol) = symbols.get(name) { known.insert(name.as_str().to_owned(), symbol); }
        }
        Expr::Arena(arena) => for atom in arena.atoms() {
            collect_arena_symbols(atom, index, symbols, known);
        },
        Expr::Unary(_, inner) | Expr::BorrowMut(inner) =>
            collect_arena_symbols(inner, index, symbols, known),
        Expr::Binary(a, _, b) => {
            collect_arena_symbols(a, index, symbols, known);
            collect_arena_symbols(b, index, symbols, known);
        }
        Expr::Call { args, .. } => for arg in args {
            collect_arena_symbols(arg, index, symbols, known);
        },
        Expr::Index { index: nested, .. } => collect_arena_symbols(nested, index, symbols, known),
        Expr::Number(_) | Expr::Bool(_) | Expr::Var(_) => {},
    }
}

fn prepare_loop_scalar<'a>(expr: &'a Expr, index: &str,
    symbols: &SymbolTable<Symbol>, at: Position) -> LoopScalar<'a> {
    if let Some(program) = fast_float_program(expr, index, symbols, at) {
        return LoopScalar::FastNumeric(program);
    }
    if !loop_uses_index(expr, index) {
        //Do not eagerly REPORT failure: a boolean short-circuit may skip it
        return match scalar(expr, symbols, at) {
            Ok(value) => LoopScalar::Known(value),
            Err(problem) => LoopScalar::Rejected(problem),
        };
    }
    match expr {
        Expr::Arena(arena) => {
            let mut known = HashMap::new();
            for atom in arena.atoms() { collect_arena_symbols(atom, index, symbols, &mut known); }
            LoopScalar::Arena { arena, index_name: index.to_owned(), known }
        }
        Expr::Var(name) if name.as_str() == index => LoopScalar::Index,
        Expr::Unary(op, inner) => LoopScalar::Unary(*op,
            Box::new(prepare_loop_scalar(inner, index, symbols, at))),
        Expr::Binary(a, op, b) => LoopScalar::Binary(
            Box::new(prepare_loop_scalar(a, index, symbols, at)), *op,
            Box::new(prepare_loop_scalar(b, index, symbols, at))),
        Expr::Call { name, args } => LoopScalar::Call {
            name, arity: math::arity(name),
            args: args.iter().map(|x| prepare_loop_scalar(x, index, symbols, at))
                .collect::<Vec<_>>().into_boxed_slice(),
        },
        _ => LoopScalar::Rejected(err(at, "invalid index-dependent scalar expression")),
    }
}

fn eval_loop_scalar(expr: &LoopScalar<'_>, index: f64, at: Position)
    -> Result<Scalar, Diagnostic> {
    let result = match expr {
        LoopScalar::FastNumeric(program) =>
            Scalar::Float(eval_fast_float(program, index, at)?),
        LoopScalar::Known(value) => *value,
        LoopScalar::Rejected(problem) => return Err(problem.clone()),
        LoopScalar::Index => Scalar::Float(index),
        LoopScalar::Arena { arena, index_name, known } =>
            scalar_arena_with(arena, &|name| {
                if name == index_name.as_str() { Some(Symbol::Number(index)) }
                else { known.get(name).copied() }
            }, at)?,
        LoopScalar::Unary(UnaryOp::Neg, inner) =>
            Scalar::Float(-eval_loop_scalar(inner, index, at)?.numeric(at)?),
        LoopScalar::Unary(UnaryOp::Not, inner) =>
            Scalar::Bool(!eval_loop_scalar(inner, index, at)?.boolean(at)?),
        LoopScalar::Binary(a, BinaryOp::And, b) => {
            let lhs = eval_loop_scalar(a, index, at)?.boolean(at)?;
            Scalar::Bool(lhs && eval_loop_scalar(b, index, at)?.boolean(at)?)
        }
        LoopScalar::Binary(a, BinaryOp::Or, b) => {
            let lhs = eval_loop_scalar(a, index, at)?.boolean(at)?;
            Scalar::Bool(lhs || eval_loop_scalar(b, index, at)?.boolean(at)?)
        }
        LoopScalar::Binary(a, op, b) => {
            let lhs = eval_loop_scalar(a, index, at)?;
            let rhs = eval_loop_scalar(b, index, at)?;
            match op {
                BinaryOp::Eq | BinaryOp::Ne => {
                    let equal = match (lhs, rhs) {
                        (Scalar::Float(x), Scalar::Float(y)) => x == y,
                        (Scalar::Bool(x), Scalar::Bool(y)) => x == y,
                        _ => return Err(err(at, "comparison requires operands of the same type")),
                    };
                    Scalar::Bool(if matches!(op, BinaryOp::Eq) { equal } else { !equal })
                }
                BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                    let x = lhs.numeric(at)?; let y = rhs.numeric(at)?;
                    Scalar::Bool(match op {
                        BinaryOp::Lt => x < y, BinaryOp::Le => x <= y,
                        BinaryOp::Gt => x > y, BinaryOp::Ge => x >= y,
                        _ => unreachable!(),
                    })
                }
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem => {
                    let x = lhs.numeric(at)?; let y = rhs.numeric(at)?;
                    Scalar::Float(match op {
                        BinaryOp::Add => x + y,
                        BinaryOp::Sub => x - y,
                        BinaryOp::Mul => x * y,
                        BinaryOp::Div => {
                            if y == 0.0 { return Err(err(at, "division by zero in constant expression")); }
                            x / y
                        }
                        BinaryOp::Rem => {
                            if y == 0.0 { return Err(err(at, "remainder by zero in constant expression")); }
                            x % y
                        }
                        _ => unreachable!(),
                    })
                }
                BinaryOp::And | BinaryOp::Or => unreachable!(),
            }
        }
        LoopScalar::Call { name, arity, args } => {
            let expected = (*arity).ok_or_else(|| err(at, format!("unknown numeric function '{name}'")))?;
            if args.len() != expected {
                return Err(err(at, format!("'{name}' requires {expected} numeric argument(s), got {}", args.len())));
            }
            let mut values = [0.0; 3];
            for (slot, arg) in values.iter_mut().zip(args.iter()) {
                *slot = eval_loop_scalar(arg, index, at)?.numeric(at)?;
            }
            Scalar::Float(math::evaluate(name, &values[..expected])
                .map_err(|message| err(at, message))?)
        }
    };
    if matches!(result, Scalar::Float(v) if !v.is_finite()) {
        return Err(err(at, "non-finite result in numeric expression"));
    }
    Ok(result)
}

fn check_direct_gate(gate: GateId, qubits: &[QubitId; 3], angles: &[f64; 4],
    at: Position, output: &mut Program) -> Result<(), Diagnostic> {
    let spec = gate_spec(gate);
    for &id in qubits.iter().take(spec.qubits) {
        if id.0 as usize >= output.qubits {
            return Err(err(at, "direct gate refers to an undeclared QubitId"));
        }
    }
    distinct(&qubits[..spec.qubits], spec.name, at)?;
    if !angles[..spec.parameters].iter().all(|n| n.is_finite()) {
        return Err(err(at, "non-finite gate angle"));
    }
    output.gate(gate, *qubits, &angles[..spec.parameters]);
    Ok(())
}

pub fn check(statements: &[Stmt]) -> Result<Program, Diagnostic> {
    let bindings = statements.iter().filter(|stmt|matches!(stmt,Stmt::Let{..})).count();
    let mut symbols: SymbolTable<Symbol> = SymbolTable::with_capacity(bindings);
    let mut output = Program::with_capacity(statements.len());
    let angle_hint: usize = statements.iter().map(|stmt|match stmt {
        Stmt::Call{name,..}=>gate_by_name(name).map_or(0,|g|g.parameters),
        Stmt::DirectGate{angles,..}=>angles.len(),
        _=>0,
    }).sum();
    output.angles.reserve_exact(angle_hint);
    let mut mutable_bits = HashSet::new();
    for stmt in statements {
        match stmt {
            Stmt::Let { name, expected, value, is_const, mutable, at } => {
                check_name(&symbols, name, *at)?;
                let symbol = match value {
                    Expr::Call { name: f, args } if f == "qubit" => {
                        check_arguments("qubit", args.len(), 0, *at)?;
                        let id = QubitId(u32::try_from(output.qubits).expect("qubit count exceeds u32"));
                        output.qubits += 1;
                        Symbol::Qubit(id)
                    }
                    Expr::Call { name: f, args } if f == "measure" || f == "measure_keep" => {
                        Symbol::Bit(emit_measure(args, f == "measure_keep", &mut symbols, &mut output, *at)?)
                    }
                    Expr::Var(source) if !matches!(source.as_str(), "pi" | "tau" | "e") => {
                        match symbols.get(source) {
                            Some(Symbol::Qubit(id)) => {
                                symbols.insert(source, Symbol::Moved); Symbol::Qubit(id)
                            }
                            Some(Symbol::Bit(id)) => Symbol::Bit(id),
                            Some(Symbol::Number(n)) => Symbol::Number(n),
                            Some(Symbol::Bool(v)) => Symbol::Bool(v),
                            Some(Symbol::Moved) => return Err(err(*at, format!("cannot move '{source}' again"))),
                            None => return Err(err(*at, format!("unknown variable '{source}'"))),
                        }
                    }
                    expr => match scalar(expr, &symbols, *at)? {
                        Scalar::Float(v) => Symbol::Number(v), Scalar::Bool(v) => Symbol::Bool(v),
                    },
                };
                if *is_const && matches!(symbol, Symbol::Qubit(_) | Symbol::Bit(_)) {
                    return Err(err(*at, "const declarations require compile-time Float or Bool; use let for Qubit/Bit"));
                }
                if let Some(expected) = expected {
                    if symbol_type(symbol) != Some(*expected) {
                        return Err(err(*at, format!("type mismatch: declared {expected:?}, got {:?}", symbol_type(symbol))));
                    }
                }
                let symbol_id = symbols.insert(name, symbol);
                if *mutable && matches!(symbol, Symbol::Bit(_)) {
                    mutable_bits.insert(symbol_id);
                }
            }
            Stmt::Call { name, args, at } =>
                statement_call(name, args, &mut symbols, &mutable_bits, &mut output, *at)?,
            Stmt::RuntimeIf { bit, expected, then_branch, else_branch, at } => {
                let bit_id = runtime_bit(bit, &symbols, *at)?;
                output.begin_if(bit_id, *expected);
                check_runtime_arm(then_branch, &mut symbols, &mutable_bits, &mut output, *at)?;
                if !else_branch.is_empty() {
                    output.else_branch();
                    check_runtime_arm(else_branch, &mut symbols, &mutable_bits, &mut output, *at)?;
                }
                output.end_if();
            }
            Stmt::RuntimeWhile { bit, expected, body, at } => {
                let bit_id = runtime_bit(bit, &symbols, *at)?;
                if !arm_definitely_writes(body, bit_id, &symbols) {
                    return Err(err(*at, "runtime while condition Bit is not refreshed on every path"));
                }
                output.begin_while(bit_id, *expected);
                check_runtime_arm(body, &mut symbols, &mutable_bits, &mut output, *at)?;
                output.end_while();
            }
            Stmt::DirectGate { gate, qubits, angles, at } =>
                check_direct_gate(*gate, qubits, angles, *at, &mut output)?,
            Stmt::RepeatGates { template, repeats, at } => {
                if *repeats < 2 || template.is_empty() {
                    return Err(err(*at, "invalid internal gate batch size"));
                }
                let first_instruction = output.instructions.len();
                let first_angle = output.angles.len();
                for op in template {
                    match op {
                        Stmt::DirectGate { gate, qubits, angles, at: gate_at } =>
                            check_direct_gate(*gate, qubits, angles, *gate_at, &mut output)?,
                        Stmt::Call { name, args, at: gate_at } if is_gate(name) =>
                            statement_call(name, args, &mut symbols, &mutable_bits, &mut output, *gate_at)?,
                        _ => return Err(err(*at, "internal gate batch contains a state-changing operation")),
                    }
                }
                output.repeat_recent_gates(first_instruction, first_angle, *repeats);
            }
            Stmt::RepeatIndexedGates { index, start, end, template, checks, at } => {
                if start >= end || template.is_empty() || symbols.contains_key(index) {
                    return Err(err(*at, "invalid internal parameterized gate loop"));
                }
                let mut prepared = Vec::with_capacity(template.len());
                let mut angles_per_loop = 0usize;
                for op in template {
                    let Stmt::Call { name, args, at: gate_at } = op else {
                        return Err(err(*at, "parameterized loop contains a non-gate operation"));
                    };
                    let spec = gate_by_name(name).ok_or_else(||
                        err(*gate_at, format!("unknown quantum gate '{name}'")))?;
                    check_arguments(name, args.len(), spec.parameters + spec.qubits, *gate_at)?;
                    let mut qubits = [QubitId(0); 3];
                    for (target, arg) in qubits.iter_mut().zip(args.iter().skip(spec.parameters))
                        .take(spec.qubits) {
                        *target = qubit_arg(arg, &symbols, *gate_at)?;
                    }
                    distinct(&qubits[..spec.qubits], spec.name, *gate_at)?;
                    let prepared_angles = args[..spec.parameters].iter().map(|expr|
                        prepare_loop_scalar(expr, index, &symbols, *gate_at)).collect::<Vec<_>>();
                    angles_per_loop += spec.parameters;
                    prepared.push((spec.id, qubits, prepared_angles, *gate_at));
                }
                let prepared_checks = checks.iter().map(|(expr, ty)|
                    (prepare_loop_scalar(expr, index, &symbols, *at), *ty))
                    .collect::<Vec<_>>();
                let repetitions = *end - *start;
                let additional_gates = template.len().checked_mul(repetitions)
                    .ok_or_else(|| err(*at, "parameterized loop expansion overflow"))?;
                let additional_angles = angles_per_loop.checked_mul(repetitions)
                    .ok_or_else(|| err(*at, "parameterized loop angle pool overflow"))?;
                output.instructions.reserve(additional_gates);
                output.angles.reserve(additional_angles);
                for i in *start..*end {
                    let index_value = i as f64;
                    for (expr, expected) in &prepared_checks {
                        let actual = eval_loop_scalar(expr, index_value, *at)?;
                        if !matches!((*expected, actual),
                            (Type::Float, Scalar::Float(_)) | (Type::Bool, Scalar::Bool(_))) {
                            return Err(err(*at, "parameterized loop scalar argument type mismatch"));
                        }
                    }
                    for (gate, qubits, angles, gate_at) in &prepared {
                        let mut values = [0.0; 4];
                        for (slot, expr) in values.iter_mut().zip(angles.iter()) {
                            *slot = eval_loop_scalar(expr, index_value, *gate_at)?.numeric(*gate_at)?;
                        }
                        output.gate_prechecked(*gate, *qubits, &values[..angles.len()]);
                    }
                }
            }
            _ => return Err(err(Position { line: 1, column: 1 }, "internal error: high-level syntax was not lowered")),
        }
    }
    Ok(output)
}

trait QasmText: std::fmt::Write {
    fn push_str(&mut self, text: &str) { let _ = self.write_str(text); }
    fn push(&mut self, ch: char) { let _ = self.write_char(ch); }
}
impl<T: std::fmt::Write> QasmText for T {}

struct IoTextSink<'a, W: io::Write> {
    writer: &'a mut W,
    bytes: usize,
    error: Option<io::Error>,
}
impl<W: io::Write> std::fmt::Write for IoTextSink<'_, W> {
    fn write_str(&mut self, value: &str) -> std::fmt::Result {
        if self.error.is_some() { return Err(std::fmt::Error); }
        match self.writer.write_all(value.as_bytes()) {
            Ok(()) => { self.bytes += value.len(); Ok(()) }
            Err(error) => { self.error = Some(error); Err(std::fmt::Error) }
        }
    }
}

pub fn emit_qasm_to_writer<W: io::Write>(program: &Program, writer: &mut W) -> io::Result<usize> {
    let mut sink = IoTextSink { writer, bytes: 0, error: None };
    let mut profile = EmitProfile::default();
    emit_qasm_internal::<false, _>(program, &mut profile, &mut sink);
    match sink.error {
        Some(error) => Err(error),
        None => Ok(sink.bytes),
    }
}

fn emit_zz<W: QasmText>(out: &mut W, a: QubitId, b: QubitId, theta: f64) {
    let _ = writeln!(out, "cx q[{}], q[{}];\nrz({theta}) q[{}];\ncx q[{}], q[{}];",
        a.0, b.0, b.0, a.0, b.0);
}
fn emit_pauli_rotation<W: QasmText>(out: &mut W, spec: &GateSpec, ids: &[QubitId; 3], theta: f64) {
    let a = ids[0].0; let b = ids[1].0;
    if spec.name == "ryy" {
        let _ = writeln!(out, "sdg q[{a}];\nsdg q[{b}];");
    }
    if spec.name != "rzz" {
        let _ = writeln!(out, "h q[{a}];\nh q[{b}];");
    }
    emit_zz(out, ids[0], ids[1], theta);
    if spec.name != "rzz" {
        let _ = writeln!(out, "h q[{a}];\nh q[{b}];");
    }
    if spec.name == "ryy" {
        let _ = writeln!(out, "s q[{a}];\ns q[{b}];");
    }
}

fn push_uint<W: QasmText>(out: &mut W, mut number: u32) {
    let mut buffer = [0u8; 10];
    let mut cursor = buffer.len();
    loop {
        cursor -= 1;
        buffer[cursor] = b'0' + (number % 10) as u8;
        number /= 10;
        if number == 0 { break; }
    }
    out.push_str(std::str::from_utf8(&buffer[cursor..]).expect("ASCII digits"));
}
fn push_qubit<W: QasmText>(out: &mut W, id: QubitId) {
    out.push_str("q["); push_uint(out, id.0); out.push(']');
}
fn push_bit<W: QasmText>(out: &mut W, id: crate::ids::BitId) {
    out.push_str("c["); push_uint(out, id.0); out.push(']');
}

#[derive(Default, Debug, Clone, Copy)]
pub struct EmitProfile {
    pub float_format: Duration,
    pub operand_append: Duration,
    pub total: Duration,
    pub output_bytes: usize,
    pub buffer_capacity: usize,
}

fn qasm_capacity(program: &Program) -> usize {
    100usize.saturating_add(program.instructions.len().saturating_mul(42))
}

pub fn emit_qasm(program: &Program) -> String {
    let mut out = String::with_capacity(qasm_capacity(program));
    let mut unused = EmitProfile::default();
    emit_qasm_internal::<false, _>(program, &mut unused, &mut out);
    out
}

pub fn emit_qasm_profiled(program: &Program) -> (String, EmitProfile) {
    let mut out = String::with_capacity(qasm_capacity(program));
    let mut stats = EmitProfile::default();
    emit_qasm_internal::<true, _>(program, &mut stats, &mut out);
    stats.output_bytes = out.len();
    stats.buffer_capacity = out.capacity();
    (out, stats)
}

fn append_qubit<W: QasmText>(out: &mut W, id: QubitId, cache: &[String]) {
    match cache.get(id.0 as usize) {
        Some(text) => out.push_str(text),
        None => push_qubit(out, id),
    }
}
fn append_bit<W: QasmText>(out: &mut W, id: crate::ids::BitId, cache: &[String]) {
    match cache.get(id.0 as usize) {
        Some(text) => out.push_str(text),
        None => push_bit(out, id),
    }
}

fn emit_qasm_internal<const PROFILE: bool, W: QasmText>(program: &Program, stats: &mut EmitProfile, out: &mut W) {
    let all_started = if PROFILE { Some(Instant::now()) } else { None };
    let mut q_cache = Vec::with_capacity(program.qubits.min(4096));
    for id in 0..program.qubits.min(4096) {
        q_cache.push(format!("q[{id}]"));
    }
    let mut b_cache = Vec::with_capacity(program.bits.min(4096));
    for id in 0..program.bits.min(4096) {
        b_cache.push(format!("c[{id}]"));
    }
    out.push_str("OPENQASM 3.0;\ninclude \"stdgates.inc\";\n\n");
    if program.qubits > 0 {
        out.push_str("qubit[");
        let _ = write!(out, "{}", program.qubits);
        out.push_str("] q;\n");
    }
    if program.bits > 0 {
        out.push_str("bit[");
        let _ = write!(out, "{}", program.bits);
        out.push_str("] c;\n");
    }
    out.push('\n');
    let cache_angles = if program.angles.len() >= 48 {
        let sample = &program.angles[..program.angles.len().min(48)];
        let mut distinct = HashSet::new();
        for angle in sample { distinct.insert(angle.to_bits()); }
        distinct.len() <= 12
    } else { false };
    let mut angle_cache: HashMap<u64, String> = HashMap::new();
    for inst in &program.instructions {
        match inst.opcode {
            OpCode::Gate(opcode) => {
                let spec = gate_spec(opcode);
                let start = inst.offset as usize;
                let params = &program.angles[start..start + inst.count as usize];
                if matches!(spec.name, "rxx" | "ryy" | "rzz") {
                    emit_pauli_rotation(out, spec, &inst.qubits, params[0]);
                    continue;
                }
                out.push_str(spec.qasm);
                if spec.parameters > 0 {
                    out.push('(');
                    for (i, val) in params.iter().enumerate() {
                        if i != 0 { out.push_str(", "); }
                        let started = if PROFILE { Some(Instant::now()) } else { None };
                        if cache_angles {
                            //Prevent adversarially many unique cached values
                            let key = val.to_bits();
                            if let Some(text) = angle_cache.get(&key) {
                                out.push_str(text);
                            } else {
                                if angle_cache.len() >= 64 { angle_cache.clear(); }
                                let text = val.to_string();
                                out.push_str(&text);
                                angle_cache.insert(key, text);
                            }
                        } else {
                            let _ = write!(out, "{val}");
                        }
                        if let Some(started) = started { stats.float_format += started.elapsed(); }
                    }
                    out.push(')');
                }
                if spec.qubits > 0 {
                    out.push(' ');
                    for (i, id) in inst.qubits[..spec.qubits].iter().enumerate() {
                        if i != 0 { out.push_str(", "); }
                        let started = if PROFILE { Some(Instant::now()) } else { None };
                        append_qubit(out, *id, &q_cache);
                        if let Some(started) = started { stats.operand_append += started.elapsed(); }
                    }
                }
                out.push_str(";\n");
            }
            OpCode::Measure | OpCode::MeasureInto => {
                append_bit(out, inst.bit, &b_cache);
                out.push_str(" = measure ");
                append_qubit(out, inst.qubits[0], &q_cache);
                out.push_str(";\n");
            }
            OpCode::Reset => {
                out.push_str("reset "); append_qubit(out, inst.qubits[0], &q_cache); out.push_str(";\n");
            }
            OpCode::IfBit | OpCode::WhileBit => {
                out.push_str(if matches!(inst.opcode, OpCode::IfBit) { "if (" } else { "while (" });
                append_bit(out, inst.bit, &b_cache);
                out.push_str(" == "); push_uint(out, inst.count);
                out.push_str(") {\n");
            }
            OpCode::Else => out.push_str("} else {\n"),
            OpCode::EndIf | OpCode::EndWhile => out.push_str("}\n"),
            OpCode::Barrier => {
                out.push_str("barrier ");
                let start = inst.offset as usize;
                let end = start + inst.count as usize;
                for (i, id) in program.barrier_qubits[start..end].iter().enumerate() {
                    if i != 0 { out.push_str(", "); }
                    append_qubit(out, *id, &q_cache);
                }
                out.push_str(";\n");
            }
        }
    }
    if let Some(started) = all_started {
        stats.total = started.elapsed();
    }
}
