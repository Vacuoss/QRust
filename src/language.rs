//QRust 0.5 source-level lowering: bounded static control flow, lexical
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use crate::sema::{self, Scalar};
use crate::ids::{NameInterner, SymbolId, QubitId};
use crate::math;
use crate::syntax::{Diagnostic, Expr, MatchPattern, Name, Param, ParamType, Position, Stmt, Type, UnaryOp};

fn fail(at: Position, msg: impl Into<String>) -> Diagnostic {
    Diagnostic { at, message: msg.into() }
}

#[derive(Clone)]
enum Binding {
    One(SymbolId),
    Register(Vec<SymbolId>),
    Constant(Scalar),
    Mutable(Scalar),
}

//A static loop whose body contains only calls that do not reference the loop index has no per-iteration
//lexical declarations to preserve
fn references_name(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Arena(arena) => arena.atoms().any(|x| references_name(x, name)),
        Expr::Var(found) => found.as_str() == name,
        Expr::Index { name: register, index } => register.as_str() == name || references_name(index, name),
        Expr::Unary(_, value) | Expr::BorrowMut(value) => references_name(value, name),
        Expr::Binary(left, _, right) => references_name(left, name) || references_name(right, name),
        Expr::Call { args, .. } => args.iter().any(|arg| references_name(arg, name)),
        Expr::Number(_) | Expr::Bool(_) => false,
    }
}

fn loop_without_local_bindings(body: &[Stmt], variable: &str) -> bool {
    body.iter().all(|statement| match statement {
        Stmt::Call { args, .. } => !args.iter().any(|arg| references_name(arg, variable)),
        //Let, block, conditional, nested loop and function definitions must retain the original scope machinery
        //even when their index is unused
        _ => false,
    })
}

fn contains_register_index(expr: &Expr) -> bool {
    match expr {
        Expr::Arena(arena) => arena.atoms().any(contains_register_index),
        Expr::Index { .. } => true,
        Expr::Unary(_, x) | Expr::BorrowMut(x) => contains_register_index(x),
        Expr::Binary(a, _, b) => contains_register_index(a) || contains_register_index(b),
        Expr::Call { args, .. } => args.iter().any(contains_register_index),
        Expr::Number(_) | Expr::Bool(_) | Expr::Var(_) => false,
    }
}

fn instantiate_prepared(expr: &PreparedExpr, args: &[Expr]) -> Expr {
    match expr {
        PreparedExpr::Parameter(i) => match &args[*i as usize] {
            Expr::BorrowMut(inner) => (**inner).clone(),
            value => value.clone(),
        },
        PreparedExpr::Number(x) => Expr::Number(*x),
        PreparedExpr::Bool(x) => Expr::Bool(*x),
        PreparedExpr::Intrinsic(name) => Expr::Var((*name).into()),
        PreparedExpr::Unary(op, x) => Expr::Unary(*op, Box::new(instantiate_prepared(x, args))),
        PreparedExpr::Binary(a, op, b) => Expr::Binary(
            Box::new(instantiate_prepared(a, args)), *op,
            Box::new(instantiate_prepared(b, args))),
        PreparedExpr::MathCall(name, params) => Expr::Call {
            name: name.clone(), args: params.iter().map(|a| instantiate_prepared(a, args)).collect(),
        },
    }
}

fn at_iteration(expr: &Expr, index: &str, value: usize) -> Expr {
    match expr {
        Expr::Arena(arena) => Expr::Arena(Box::new(arena.try_map_atoms(|x| Ok::<_, ()>(at_iteration(x, index, value))).unwrap())),
        Expr::Var(name) if name == index => Expr::Number(value as f64),
        Expr::Var(name) => Expr::Var(name.clone()),
        Expr::Number(x) => Expr::Number(*x),
        Expr::Bool(x) => Expr::Bool(*x),
        Expr::Unary(op, x) => Expr::Unary(*op, Box::new(at_iteration(x, index, value))),
        Expr::Binary(a, op, b) => Expr::Binary(
            Box::new(at_iteration(a, index, value)), *op,
            Box::new(at_iteration(b, index, value))),
        Expr::Call { name, args } => Expr::Call { name: name.clone(),
            args: args.iter().map(|a| at_iteration(a, index, value)).collect() },
        Expr::Index { name, index: at } => Expr::Index { name: name.clone(),
            index: Box::new(at_iteration(at, index, value)) },
        Expr::BorrowMut(x) => Expr::BorrowMut(Box::new(at_iteration(x, index, value))),
    }
}

//Gate-only leaf functions cannot allocate, measure, borrow further resources, branch, or capture outer
//variables
fn leaf_expr_is_closed(expr: &Expr, params: &[Param]) -> bool {
    match expr {
        Expr::Arena(_) => false, //checked general path; no prepared subtree recursion
        Expr::Number(_) | Expr::Bool(_) => true,
        Expr::Var(name) => matches!(name.as_str(), "pi" | "tau" | "e") ||
            params.iter().any(|param| param.name.as_str() == name.as_str()),
        Expr::Unary(_, child) => leaf_expr_is_closed(child, params),
        Expr::Binary(left, _, right) =>
            leaf_expr_is_closed(left, params) && leaf_expr_is_closed(right, params),
        Expr::Call { name, args } => math::arity(name).is_some() &&
            args.iter().all(|arg| leaf_expr_is_closed(arg, params)),
        Expr::Index { .. } | Expr::BorrowMut(_) => false,
    }
}

fn gate_only_leaf(params: &[Param], body: &[Stmt]) -> bool {
    if params.len() > 8 { return false; }
    let mut names = HashSet::with_capacity(params.len());
    //Do not skip the normal signature diagnostics (duplicates or reserved parameter names); the slow path
    //is responsible for those errors
    if !params.iter().all(|param| {
        !crate::surface::reserved_identifier(&param.name) && names.insert(param.name.as_str())
    }) { return false; }
    !body.is_empty() && body.iter().all(|stmt| match stmt {
        Stmt::Call { name, args, .. } if sema::is_gate(name) =>
            args.iter().all(|expr| leaf_expr_is_closed(expr, params)),
        _ => false,
    })
}

#[derive(Clone)]
enum PreparedExpr {
    Parameter(u8),
    Number(f64),
    Bool(bool),
    Intrinsic(&'static str),
    Unary(crate::syntax::UnaryOp, Box<PreparedExpr>),
    Binary(Box<PreparedExpr>, crate::syntax::BinaryOp, Box<PreparedExpr>),
    MathCall(Name, Box<[PreparedExpr]>),
}

#[derive(Clone)]
struct PreparedGate {
    gate: sema::GateId,
    args: Box<[PreparedExpr]>,
    at: Position,
}

fn prepare_expr(expr: &Expr, params: &[Param]) -> PreparedExpr {
    match expr {
        Expr::Arena(_) => unreachable!("arena expressions deliberately use the general checked path"),
        Expr::Var(name) => {
            if let Some(index) = params.iter().position(|p| p.name == *name) {
                PreparedExpr::Parameter(index as u8) //leaf signatures have <=8 params
            } else {
                let constant = match name.as_str() {
                    "pi" => "pi", "tau" => "tau", "e" => "e",
                    _ => unreachable!("only explicit parameters and built-in constants are allowed"),
                };
                PreparedExpr::Intrinsic(constant)
            }
        }
        Expr::Number(value) => PreparedExpr::Number(*value),
        Expr::Bool(value) => PreparedExpr::Bool(*value),
        Expr::Unary(op, inner) => PreparedExpr::Unary(*op, Box::new(prepare_expr(inner, params))),
        Expr::Binary(left, op, right) => PreparedExpr::Binary(
            Box::new(prepare_expr(left, params)), *op, Box::new(prepare_expr(right, params))),
        Expr::Call { name, args } => PreparedExpr::MathCall(name.clone(),
            args.iter().map(|arg| prepare_expr(arg, params)).collect::<Vec<_>>().into_boxed_slice()),
        Expr::Index { .. } | Expr::BorrowMut(_) => unreachable!("prepared leaf must be closed"),
    }
}

fn prepare_leaf(params: &[Param], body: &[Stmt]) -> Option<Rc<[PreparedGate]>> {
    if !gate_only_leaf(params, body) { return None; }
    let mut prepared = Vec::with_capacity(body.len());
    for statement in body {
        let Stmt::Call { name, args, at } = statement else {
            unreachable!("validated leaf body contains only gate calls");
        };
        let gate = sema::gate_id(name).expect("validated leaf has a known gate");
        let args = args.iter().map(|arg| prepare_expr(arg, params))
            .collect::<Vec<_>>().into_boxed_slice();
        prepared.push(PreparedGate { gate, args, at: *at });
    }
    Some(Rc::from(prepared))
}

fn prepared_scalar(expr: &PreparedExpr, bindings: &[Binding], at: Position) -> Result<Scalar, Diagnostic> {
    use crate::syntax::{BinaryOp as B, UnaryOp as U};
    let value = match expr {
        PreparedExpr::Parameter(i) => match &bindings[*i as usize] {
            Binding::Constant(v) | Binding::Mutable(v) => *v,
            Binding::One(_) | Binding::Register(_) => return Err(fail(at, "expected numeric parameter, got Qubit")),
        },
        PreparedExpr::Number(v) => Scalar::Float(*v),
        PreparedExpr::Bool(v) => Scalar::Bool(*v),
        PreparedExpr::Intrinsic("pi") => Scalar::Float(std::f64::consts::PI),
        PreparedExpr::Intrinsic("tau") => Scalar::Float(std::f64::consts::TAU),
        PreparedExpr::Intrinsic("e") => Scalar::Float(std::f64::consts::E),
        PreparedExpr::Intrinsic(_) => unreachable!(),
        PreparedExpr::Unary(U::Neg, inner) => Scalar::Float(-prepared_float(inner, bindings, at)?),
        PreparedExpr::Unary(U::Not, inner) => Scalar::Bool(!prepared_bool(inner, bindings, at)?),
        PreparedExpr::Binary(lhs, B::And, rhs) => {
            Scalar::Bool(prepared_bool(lhs, bindings, at)? && prepared_bool(rhs, bindings, at)?)
        }
        PreparedExpr::Binary(lhs, B::Or, rhs) => {
            Scalar::Bool(prepared_bool(lhs, bindings, at)? || prepared_bool(rhs, bindings, at)?)
        }
        PreparedExpr::Binary(lhs, op, rhs) => {
            let left = prepared_scalar(lhs, bindings, at)?;
            let right = prepared_scalar(rhs, bindings, at)?;
            match op {
                B::Eq | B::Ne => {
                    let equal = match (left, right) {
                        (Scalar::Float(x), Scalar::Float(y)) => x == y,
                        (Scalar::Bool(x), Scalar::Bool(y)) => x == y,
                        _ => return Err(fail(at, "comparison requires operands of the same type")),
                    };
                    Scalar::Bool(if matches!(op, B::Eq) { equal } else { !equal })
                }
                B::Lt | B::Le | B::Gt | B::Ge => {
                    let x = scalar_to_float(left, at)?; let y = scalar_to_float(right, at)?;
                    Scalar::Bool(match op { B::Lt => x < y, B::Le => x <= y, B::Gt => x > y, B::Ge => x >= y, _ => unreachable!() })
                }
                B::Add | B::Sub | B::Mul | B::Div | B::Rem => {
                    let x = scalar_to_float(left, at)?; let y = scalar_to_float(right, at)?;
                    if y == 0.0 && matches!(op, B::Div | B::Rem) { return Err(fail(at, "division by zero in constant expression")); }
                    Scalar::Float(match op { B::Add => x+y, B::Sub => x-y, B::Mul => x*y, B::Div => x/y, B::Rem => x%y, _=> unreachable!() })
                }
                B::And | B::Or => unreachable!(),
            }
        }
        PreparedExpr::MathCall(name, args) => {
            let expected = math::arity(name).ok_or_else(|| fail(at, format!("unknown math function '{name}'")))?;
            if args.len() != expected { return Err(fail(at, format!("'{name}' requires {expected} numeric argument(s), got {}", args.len()))); }
            let mut values = [0.0; 3];
            for (index, arg) in args.iter().enumerate() { values[index] = prepared_float(arg, bindings, at)?; }
            Scalar::Float(math::evaluate(name, &values[..expected]).map_err(|message| fail(at, message))?)
        }
    };
    if matches!(value, Scalar::Float(n) if !n.is_finite()) {
        return Err(fail(at, "non-finite result in numeric expression"));
    }
    Ok(value)
}
fn scalar_to_float(v: Scalar, at: Position) -> Result<f64, Diagnostic> {
    match v { Scalar::Float(x) => Ok(x), Scalar::Bool(_) => Err(fail(at, "expected Float, got Bool")) }
}
fn prepared_float(expr: &PreparedExpr, bindings: &[Binding], at: Position) -> Result<f64, Diagnostic> {
    scalar_to_float(prepared_scalar(expr, bindings, at)?, at)
}
fn prepared_bool(expr: &PreparedExpr, bindings: &[Binding], at: Position) -> Result<bool, Diagnostic> {
    match prepared_scalar(expr, bindings, at)? {
        Scalar::Bool(b) => Ok(b), Scalar::Float(_) => Err(fail(at, "expected Bool, got Float"))
    }
}

#[derive(Clone)]
//One immutable AST body per declared function. Expanding a function must not deep-clone its entire body
//on every invocation, especially in for loops
struct Function { params: Rc<[Param]>, body: Rc<[Stmt]>, at: Position, multiple_mut_qubits: bool, prepared_leaf: Option<Rc<[PreparedGate]>> }

#[derive(Clone, Copy, PartialEq, Eq)]
enum LoopSignal { Break, Continue }

pub fn lower(statements: &[Stmt]) -> Result<Vec<Stmt>, Diagnostic> {
    let mut functions = HashMap::new();
    let mut names = NameInterner::default();
    let mut executable_count = 0usize;
    for stmt in statements {
        if let Stmt::Function { name, params, body, at } = stmt {
            let function_id = names.intern(name);
            if functions.contains_key(&function_id) { return Err(fail(*at, format!("duplicate function '{name}'"))); }
            //Function names must not shadow keywords, internally generated symbols, or compile-time validation
            //builtins
            if crate::surface::reserved_identifier(name) {
                return Err(fail(*at, format!("'{name}' is a reserved constant or keyword")));
            }
            if matches!(name.as_str(), "qubit" | "qubits" | "measure" | "measure_keep" | "measure_into" | "reset" | "barrier" |
                "static_assert" | "static_assert_eq" | "static_assert_ne" | "static_assert_live" | "static_assert_distinct") ||
                sema::is_gate(name) || math::arity(name).is_some() {
                return Err(fail(*at, format!("function '{name}' conflicts with a quantum builtin")));
            }
            let multiple_mut_qubits = params.iter()
                .filter(|param| matches!(param.kind, ParamType::QubitMut))
                .nth(1).is_some();
            let prepared_leaf = prepare_leaf(params, body);
            functions.insert(function_id, Function { params: Rc::from(params.as_slice()),
                body: Rc::from(body.as_slice()), at: *at, multiple_mut_qubits, prepared_leaf });
        } else { executable_count += 1; }
    }
    let main_id = names.id("main");
    if main_id.is_some_and(|id| functions.contains_key(&id)) && executable_count != 0 {
        return Err(fail(Position { line: 1, column: 1 }, "top-level statements cannot be combined with fn main()"));
    }
    let mut context = Lower {
        functions, scopes: vec![HashMap::new()], scope_pool: Vec::new(), values: HashMap::new(),
        names, borrowed: HashSet::new(), mutable_bits: HashSet::new(),
        live: HashSet::new(), types: HashMap::new(),
        resource_ids: HashMap::new(), next_resource: 0,
        visited: HashSet::new(),
        emitted: Vec::new(), serial: 0, depth: 0, expanded_count: 0,
        loop_depth: 0, loop_signal: None,
    };
    if let Some(main) = main_id.and_then(|id| context.functions.get(&id)).cloned() {
        if !main.params.is_empty() { return Err(fail(main.at, "fn main() cannot accept parameters")); }
        context.call_user("main", &[], main.at)?;
    } else {
        for stmt in statements {
            if !matches!(stmt, Stmt::Function { .. }) { context.statement(stmt)?; }
        }
    }
    //Never report an unused function as "checked": it was not expanded
    for (id, function) in &context.functions {
        if !context.visited.contains(id) {
            let name = context.names.name(*id);
            return Err(fail(function.at, format!("function '{name}' is never called; QRust 0.4 cannot validate unused functions")));
        }
    }
    Ok(context.emitted)
}

struct Lower {
    functions: HashMap<SymbolId, Function>,
    scopes: Vec<HashMap<SymbolId, Binding>>,
    //Cleared scope maps retain their allocations across static loop iterations and repeated function calls
    //They never contain live names
    scope_pool: Vec<HashMap<SymbolId, Binding>>,
    values: HashMap<String, Scalar>,
    names: NameInterner,
    resource_ids: HashMap<SymbolId, QubitId>,
    next_resource: u32,
    borrowed: HashSet<SymbolId>,
    mutable_bits: HashSet<SymbolId>,
    visited: HashSet<SymbolId>,
    live: HashSet<SymbolId>,
    types: HashMap<SymbolId, Type>,
    emitted: Vec<Stmt>,
    serial: usize,
    depth: usize,
    expanded_count: usize,
    loop_depth: usize,
    loop_signal: Option<LoopSignal>,
}
impl Lower {
    fn generated(&mut self, hint: &str) -> SymbolId {
        self.serial += 1;
        self.names.intern(&format!("__qrust_{}_{}", self.serial, hint))
    }
    fn output_name(&self, id: SymbolId) -> Name { self.names.shared_name(id) }
    fn existing(&self, name: &str) -> Option<SymbolId> { self.names.id(name) }
    fn resolved_id(&self, name: &str) -> Option<SymbolId> {
        match self.binding(name) {
            Some(Binding::One(actual)) => Some(*actual),
            Some(Binding::Register(_) | Binding::Constant(_) | Binding::Mutable(_)) => None,
            None => self.existing(name), //already-lowered/generated identifier
        }
    }
    fn type_of(&self, name: &str) -> Option<Type> {
        match self.binding(name) {
            Some(Binding::Constant(Scalar::Float(_)) | Binding::Mutable(Scalar::Float(_))) => Some(Type::Float),
            Some(Binding::Constant(Scalar::Bool(_)) | Binding::Mutable(Scalar::Bool(_))) => Some(Type::Bool),
            Some(Binding::Register(_)) => None,
            _ => self.resolved_id(name).and_then(|id| self.types.get(&id).copied()),
        }
    }
    fn is_live_name(&self, name: &str) -> bool {
        self.resolved_id(name).is_some_and(|id| self.live.contains(&id))
    }
    fn mark_consumed(&mut self, name: &str) {
        if let Some(id) = self.resolved_id(name) { self.live.remove(&id); }
    }
    fn resource_of(&self, name: &str) -> Option<QubitId> {
        self.resolved_id(name).and_then(|id| self.resource_ids.get(&id).copied())
    }
    fn new_resource(&mut self, id: SymbolId) {
        let resource = QubitId(self.next_resource);
        self.next_resource = self.next_resource.checked_add(1).expect("too many QubitIds");
        self.resource_ids.insert(id, resource);
    }
    fn emit(&mut self, stmt: Stmt, at: Position) -> Result<(), Diagnostic> {
        if self.expanded_count >= 500_000 { return Err(fail(at, "expanded program exceeds 500,000 statements")); }
        self.emitted.push(stmt);
        self.expanded_count += 1;
        Ok(())
    }
    fn enter(&mut self) {
        let scope = self.scope_pool.pop().unwrap_or_default();
        debug_assert!(scope.is_empty());
        self.scopes.push(scope);
    }
    fn leave(&mut self) {
        if let Some(mut scope) = self.scopes.pop() {
            scope.clear();
            if self.scope_pool.len() < 64 { self.scope_pool.push(scope); }
        }
    }
    fn binding(&self, name: &str) -> Option<&Binding> {
        let id = self.names.id(name)?;
        self.scopes.iter().rev().find_map(|scope| scope.get(&id))
    }
    fn define(&mut self, name: &str, binding: Binding, at: Position) -> Result<(), Diagnostic> {
        if crate::surface::reserved_identifier(name) {
            return Err(fail(at, format!("'{name}' is a reserved constant or keyword")));
        }
        let id = self.names.intern(name);
        let scope = self.scopes.last_mut().expect("global scope always exists");
        if scope.contains_key(&id) { return Err(fail(at, format!("name '{name}' is already declared"))); }
        scope.insert(id, binding);
        Ok(())
    }
    fn static_value(&self, expr: &Expr, at: Position) -> Result<Scalar, Diagnostic> {
        sema::eval_constant(expr, &self.values, at)
    }
    fn count(&self, expr: &Expr, at: Position) -> Result<usize, Diagnostic> {
        match self.static_value(expr, at)? {
            Scalar::Float(n) if n >= 0.0 && n.fract() == 0.0 && n <= 100_000.0 => Ok(n as usize),
            _ => Err(fail(at, "expected compile-time integer between 0 and 100000")),
        }
    }
    fn rewrite(&self, expr: &Expr, at: Position) -> Result<Expr, Diagnostic> {
        Ok(match expr {
            Expr::Arena(arena) => Expr::Arena(Box::new(arena.try_map_atoms(|x| self.rewrite(x, at))?)),
            Expr::Var(name) => match self.binding(name) {
                Some(Binding::One(actual)) => Expr::Var(self.output_name(*actual)),
                Some(Binding::Constant(Scalar::Float(value))) | Some(Binding::Mutable(Scalar::Float(value))) => Expr::Number(*value),
                Some(Binding::Constant(Scalar::Bool(value))) | Some(Binding::Mutable(Scalar::Bool(value))) => Expr::Bool(*value),
                Some(Binding::Register(_)) => return Err(fail(at, format!("register '{name}' requires an index"))),
                None if self.depth > 0 && !matches!(name.as_str(), "pi" | "tau" | "e") => {
                    return Err(fail(at, format!("unknown variable '{name}' in function scope; pass it as an explicit parameter")));
                }
                None => Expr::Var(name.clone()),
            },
            Expr::Index { name, index } => {
                let index = self.rewrite(index, at)?;
                let pos = self.count(&index, at)?;
                match self.binding(name) {
                    Some(Binding::Register(items)) => Expr::Var(self.output_name(*items.get(pos)
                        .ok_or_else(|| fail(at, format!("register '{name}' index {pos} out of bounds (length {})", items.len())))?)),
                    Some(Binding::One(_) | Binding::Constant(_) | Binding::Mutable(_)) => return Err(fail(at, format!("'{name}' is not a register"))),
                    None => return Err(fail(at, format!("unknown register '{name}'"))),
                }
            }
            Expr::Number(n) => Expr::Number(*n),
            Expr::Bool(b) => Expr::Bool(*b),
            Expr::Unary(op, x) => Expr::Unary(*op, Box::new(self.rewrite(x, at)?)),
            Expr::Binary(l, op, r) => Expr::Binary(Box::new(self.rewrite(l, at)?), *op, Box::new(self.rewrite(r, at)?)),
            Expr::Call { name, args } => Expr::Call {
                name: name.clone(), args: args.iter().map(|a| self.rewrite(a, at)).collect::<Result<_, _>>()?
            },
            Expr::BorrowMut(x) => Expr::BorrowMut(Box::new(self.rewrite(x, at)?)),
        })
    }
    fn is_borrowed(&self, expr: &Expr) -> bool {
        matches!(expr, Expr::Var(name) if self.existing(name).is_some_and(|id| self.borrowed.contains(&id)))
    }
    //A repeated gate-only body cannot alter the ownership environment or scalar bindings
    fn pure_gate_loop(&self, body: &[Stmt]) -> bool {
        !body.is_empty() && body.iter().all(|stmt| match stmt {
            Stmt::Call { name, .. } => {
                match self.names.id(name).and_then(|id| self.functions.get(&id)) {
                    Some(function) => function.prepared_leaf.is_some(),
                    None => sema::is_gate(name),
                }
            }
            _ => false,
        })
    }

    fn emit_gate_batch(&mut self, begin: usize, repeats: usize, at: Position)
        -> Result<(), Diagnostic> {
        //The first iteration was fully type/borrow checked during lowering Repeating an immutable gate-only
        //body cannot change that result
        let template = self.emitted.split_off(begin);
        debug_assert!(!template.is_empty());
        debug_assert!(template.iter().all(|stmt| matches!(stmt,
            Stmt::DirectGate { .. } | Stmt::Call { .. })));
        self.expanded_count -= template.len();
        let total = template.len().checked_mul(repeats).unwrap_or(usize::MAX);
        if total > 500_000usize.saturating_sub(self.expanded_count) {
            return Err(fail(at, "expanded program exceeds 500,000 statements"));
        }
        self.expanded_count += total;
        self.emitted.push(Stmt::RepeatGates { template, repeats, at });
        Ok(())
    }

    fn parameterized_gate_loop(&mut self, variable: &str, body: &[Stmt],
        start: usize, end: usize, at: Position) -> Result<(), Diagnostic> {
        self.enter();
        let index_id = self.generated("loop_index");
        let index_name = self.output_name(index_id);
        let result = (|| -> Result<(Vec<Stmt>, Vec<(Expr, Type)>), Diagnostic> {
            self.define(variable, Binding::One(index_id), at)?;
            self.types.insert(index_id, Type::Float);
            let mut template = Vec::new();
            let mut checks = Vec::new();
            for statement in body {
                let Stmt::Call { name, args, at: call_at } = statement else { unreachable!() };
                let rewritten: Vec<Expr> = args.iter().map(|arg| self.rewrite(arg, *call_at))
                    .collect::<Result<_, _>>()?;
                if let Some(function_id) = self.names.id(name).filter(|id| self.functions.contains_key(id)) {
                    let function = self.functions.get(&function_id).expect("declared function").clone();
                    self.visited.insert(function_id);
                    if rewritten.len() != function.params.len() {
                        return Err(fail(*call_at, format!("function '{name}' expects {} argument(s), got {}",
                            function.params.len(), rewritten.len())));
                    }
                    let mut resources = HashSet::new();
                    for (param, arg) in function.params.iter().zip(rewritten.iter()) {
                        match param.kind {
                            ParamType::QubitMut => {
                                let Expr::BorrowMut(inner) = arg else {
                                    return Err(fail(*call_at, format!("'{}' requires '&mut Qubit'", param.name)));
                                };
                                let Expr::Var(qubit) = &**inner else {
                                    return Err(fail(*call_at, "borrow must reference a named Qubit"));
                                };
                                if self.type_of(qubit) != Some(Type::Qubit) {
                                    return Err(fail(*call_at, format!("'{}' expects a Qubit, not a classical value",param.name)));
                                }
                                if !self.is_live_name(qubit) {
                                    return Err(fail(*call_at, format!("cannot borrow consumed or moved qubit '{qubit}'")));
                                }
                                let resource = self.resource_of(qubit).ok_or_else(||
                                    fail(*call_at, "unknown quantum resource"))?;
                                if !resources.insert(resource) {
                                    return Err(fail(*call_at, "two mutable parameters cannot alias the same qubit"));
                                }
                            }
                            ParamType::Float | ParamType::Bool => {
                                let scalar = self.static_value(
                                    &at_iteration(arg, &index_name, start), *call_at)?;
                                let correct = matches!((param.kind, scalar),
                                    (ParamType::Float, Scalar::Float(_)) |
                                    (ParamType::Bool, Scalar::Bool(_)));
                                if !correct {
                                    return Err(fail(*call_at, format!("'{}' has the wrong scalar type", param.name)));
                                }
                                let ty = if matches!(param.kind, ParamType::Float) {
                                    Type::Float
                                } else { Type::Bool };
                                checks.push((arg.clone(), ty));
                            }
                        }
                    }
                    let gates = function.prepared_leaf.as_ref().expect("pure gate loop");
                    for gate in gates.iter() {
                        let spec = sema::gate_spec(gate.gate);
                        if gate.args.len() != spec.parameters + spec.qubits {
                            return Err(fail(gate.at, format!("'{}' requires {} argument(s), got {}",
                                spec.name, spec.parameters + spec.qubits, gate.args.len())));
                        }
                        template.push(Stmt::Call { name: spec.name.into(),
                            args: gate.args.iter().map(|arg| instantiate_prepared(arg, &rewritten)).collect(),
                            at: gate.at });
                    }
                } else {
                    template.push(Stmt::Call { name: name.clone(), args: rewritten, at: *call_at });
                }
            }
            Ok((template, checks))
        })();
        self.leave();
        let (template, checks) = result?;
        if template.is_empty() { return Err(fail(at, "empty parameterized gate template")); }
        let expanded = template.len().checked_mul(end-start).unwrap_or(usize::MAX);
        if expanded > 500_000usize.saturating_sub(self.expanded_count) {
            return Err(fail(at, "expanded program exceeds 500,000 statements"));
        }
        self.expanded_count += expanded;
        self.emitted.push(Stmt::RepeatIndexedGates { index: index_name,
            start, end, template, checks, at });
        Ok(())
    }

    fn reserve_flat_loop(&mut self, body: &[Stmt], repeats: usize) {
        let mut gates_per_iteration = 0usize;
        for stmt in body {
            let Stmt::Call { name, .. } = stmt else { return; };
            if let Some(function) = self.names.id(name).and_then(|id| self.functions.get(&id)) {
                let Some(prepared) = &function.prepared_leaf else { return; };
                gates_per_iteration = gates_per_iteration.saturating_add(prepared.len());
            } else if sema::is_gate(name) {
                gates_per_iteration = gates_per_iteration.saturating_add(1);
            } else { return; }
        }
        let total = gates_per_iteration.saturating_mul(repeats);
        if total <= 500_000usize.saturating_sub(self.expanded_count) {
            self.emitted.reserve(total);
        }
    }

    //A runtime control condition must be a live, already-measured Bit Static values remain in compile-time
    //branches, not runtime CFG edges
    fn runtime_condition(&self, condition: &Expr, at: Position) -> Result<(Expr, bool), Diagnostic> {
        let rewritten = self.rewrite(condition, at)?;
        match &rewritten {
            Expr::Var(name) if self.type_of(name) == Some(Type::Bit) => Ok((rewritten.clone(), true)),
            Expr::Unary(UnaryOp::Not, inner) => match &**inner {
                Expr::Var(name) if self.type_of(name) == Some(Type::Bit) =>
                    Ok((Expr::Var(name.clone()), false)),
                _ => Err(fail(at, "runtime control requires a measurement Bit or !Bit")),
            },
            _ => Err(fail(at, "runtime control requires a measurement Bit or !Bit")),
        }
    }

    fn validate_measure_into(&self, args: &[Expr], at: Position) -> Result<(), Diagnostic> {
        if args.len() != 2 { return Err(fail(at, "measure_into requires (mutable Bit, live Qubit)")); }
        let Expr::Var(bit) = &args[0] else { return Err(fail(at, "measure_into requires a named mutable Bit")); };
        let Some(Binding::One(id)) = self.binding(bit) else {
            return Err(fail(at, "measure_into requires a named mutable Bit"));
        };
        if !self.mutable_bits.contains(id) || self.type_of(bit) != Some(Type::Bit) {
            return Err(fail(at, "measure_into requires a mutable Bit declared with let mut"));
        }
        let qubit = self.rewrite(&args[1], at)?;
        let Expr::Var(name) = qubit else { return Err(fail(at, "measure_into expects a named Qubit")); };
        if self.type_of(&name) != Some(Type::Qubit) || !self.is_live_name(&name) {
            return Err(fail(at, "measure_into requires a live Qubit"));
        }
        if self.existing(&name).is_some_and(|id| self.borrowed.contains(&id)) {
            return Err(fail(at, "measure_into cannot measure a borrowed Qubit"));
        }
        Ok(())
    }

    fn runtime_arm(&self, stmts: &[Stmt], at: Position, required: Option<&str>)
        -> Result<(Vec<Stmt>, bool), Diagnostic> {
        let mut out = Vec::with_capacity(stmts.len());
        let mut definitely_refreshed = false;
        for stmt in stmts {
            match stmt {
                Stmt::Call { name, args, at: call_at }
                    if sema::is_gate(name) || matches!(name.as_str(), "reset" | "barrier") => {
                    let rewritten = args.iter().map(|arg| self.rewrite(arg, *call_at))
                        .collect::<Result<Vec<_>, _>>()?;
                    out.push(Stmt::Call { name: name.clone(), args: rewritten, at: *call_at });
                }
                Stmt::Call { name, args, at: call_at } if name == "measure_into" => {
                    self.validate_measure_into(args, *call_at)?;
                    let rewritten = args.iter().map(|arg| self.rewrite(arg, *call_at))
                        .collect::<Result<Vec<_>, _>>()?;
                    if required.is_some_and(|bit| matches!(&rewritten[0], Expr::Var(name) if name.as_str() == bit)) {
                        definitely_refreshed = true;
                    }
                    out.push(Stmt::Call { name: name.clone(), args: rewritten, at: *call_at });
                }
                Stmt::Block { statements, .. } => {
                    let (nested, writes) = self.runtime_arm(statements, at, required)?;
                    out.extend(nested);
                    definitely_refreshed |= writes;
                }
                Stmt::If { condition, then_branch, else_branch, at: if_at } => {
                    let rewritten = self.rewrite(condition, *if_at)?;
                    if let Ok(Scalar::Bool(value)) = self.static_value(&rewritten, *if_at) {
                        let (nested, writes) = self.runtime_arm(
                            if value { then_branch } else { else_branch }, *if_at, required)?;
                        out.extend(nested);
                        definitely_refreshed |= writes;
                    } else {
                        let (bit, expected) = self.runtime_condition(condition, *if_at)?;
                        let (then_arm, then_writes) = self.runtime_arm(then_branch, *if_at, required)?;
                        let (else_arm, else_writes) = self.runtime_arm(else_branch, *if_at, required)?;
                        out.push(Stmt::RuntimeIf { bit, expected, then_branch: then_arm,
                            else_branch: else_arm, at: *if_at });
                        definitely_refreshed |= then_writes && else_writes;
                    }
                }
                _ => return Err(fail(at,
                    "runtime control supports only gates, reset, barrier, measure_into and nested if; no ownership changes")),
            }
        }
        Ok((out, definitely_refreshed))
    }

    fn statements(&mut self, statements: &[Stmt]) -> Result<(), Diagnostic> {
        for stmt in statements {
            if self.loop_signal.is_some() { break; }
            self.statement(stmt)?;
        }
        Ok(())
    }
    fn static_iteration(&mut self, body: &[Stmt],
        binding: Option<(&str, usize, Position)>) -> Result<Option<LoopSignal>, Diagnostic> {
        self.enter();
        self.loop_depth += 1;
        let result = (|| -> Result<(), Diagnostic> {
            if let Some((name, index, at)) = binding {
                self.define(name, Binding::Constant(Scalar::Float(index as f64)), at)?;
            }
            self.statements(body)
        })();
        self.loop_depth -= 1;
        self.leave();
        result?;
        Ok(self.loop_signal.take())
    }
    fn statement(&mut self, stmt: &Stmt) -> Result<(), Diagnostic> {
        match stmt {
            Stmt::Break { at } => {
                if self.loop_depth == 0 { return Err(fail(*at, "'break' outside a static loop")); }
                self.loop_signal = Some(LoopSignal::Break);
                Ok(())
            }
            Stmt::Continue { at } => {
                if self.loop_depth == 0 { return Err(fail(*at, "'continue' outside a static loop")); }
                self.loop_signal = Some(LoopSignal::Continue);
                Ok(())
            }
            Stmt::Loop { body, at } => {
                for _ in 0..100_000usize {
                    match self.static_iteration(body, None)? {
                        Some(LoopSignal::Break) => return Ok(()),
                        Some(LoopSignal::Continue) | None => {}
                    }
                }
                Err(fail(*at, "static loop expansion exceeds 100000 iterations; add a reachable break"))
            }
            Stmt::Block { statements, at } => {
                if self.scopes.len() >= crate::syntax::MAX_LOWERING_SCOPE_DEPTH {
                    return Err(fail(*at, "nested lowering scope limit exceeded"));
                }
                self.enter(); let result = self.statements(statements); self.leave(); result
            }
            Stmt::If { condition, then_branch, else_branch, at } => {
                let condition = self.rewrite(condition, *at)?;
                let runtime = match &condition {
                    Expr::Var(name) if self.type_of(name) == Some(Type::Bit) =>
                        Some((Expr::Var(name.clone()), true)),
                    Expr::Unary(UnaryOp::Not, inner) => match &**inner {
                        Expr::Var(name) if self.type_of(name) == Some(Type::Bit) =>
                            Some((Expr::Var(name.clone()), false)),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((bit, expected)) = runtime {
                    let (then_branch, _) = self.runtime_arm(then_branch, *at, None)?;
                    let (else_branch, _) = self.runtime_arm(else_branch, *at, None)?;
                    return self.emit(Stmt::RuntimeIf { bit, expected, then_branch,
                        else_branch, at: *at }, *at);
                }
                let branch = match self.static_value(&condition, *at)? {
                    Scalar::Bool(true) => then_branch,
                    Scalar::Bool(false) => else_branch,
                    _ => return Err(fail(*at, "if condition must be a compile-time Bool")),
                };
                self.enter(); let result = self.statements(branch); self.leave(); result
            }
            Stmt::Match { value, arms, at } => {
                let rewritten = self.rewrite(value, *at)?;
                let subject = self.static_value(&rewritten, *at)
                    .map_err(|_| fail(*at, "match scrutinee must be compile-time Bool or integer Float"))?;
                if let Scalar::Float(value) = subject {
                    if value.fract() != 0.0 || value.abs() > 9_007_199_254_740_991.0 {
                        return Err(fail(*at, "match scrutinee must be an exactly represented compile-time integer"));
                    }
                }
                let mut seen_true = false;
                let mut seen_false = false;
                let mut seen_numbers = HashSet::new();
                let mut wildcard = false;
                let mut selected = None;
                for (index, (pattern, _)) in arms.iter().enumerate() {
                    if wildcard { return Err(fail(*at, "'_' match arm must be last")); }
                    let matches = match (subject, pattern) {
                        (Scalar::Bool(value), MatchPattern::Bool(pattern)) => {
                            if *pattern { if seen_true { return Err(fail(*at, "duplicate true match arm")); } seen_true = true; }
                            else { if seen_false { return Err(fail(*at, "duplicate false match arm")); } seen_false = true; }
                            value == *pattern
                        }
                        (Scalar::Float(value), MatchPattern::Integer(pattern)) => {
                            if !seen_numbers.insert(*pattern) { return Err(fail(*at, "duplicate integer match arm")); }
                            value == *pattern as f64
                        }
                        (_, MatchPattern::Wildcard) => { wildcard = true; true }
                        _ => return Err(fail(*at, "match pattern type does not match scrutinee")),
                    };
                    if matches && selected.is_none() { selected = Some(index); }
                }
                if !wildcard && !(matches!(subject, Scalar::Bool(_)) && seen_true && seen_false) {
                    return Err(fail(*at, "non-exhaustive match: add a final '_' arm"));
                }
                let Some(index) = selected else { return Err(fail(*at, "non-exhaustive match")); };
                self.enter();
                let result = self.statements(&arms[index].1);
                self.leave();
                result
            }
            Stmt::While { condition, body, at } => {
                let rewritten = self.rewrite(condition, *at)?;
                let dynamic = match &rewritten {
                    Expr::Var(name) if self.type_of(name) == Some(Type::Bit) => true,
                    Expr::Unary(UnaryOp::Not, expr) =>
                        matches!(&**expr, Expr::Var(name) if self.type_of(name) == Some(Type::Bit)),
                    _ => false,
                };
                if dynamic {
                    let (bit, expected) = self.runtime_condition(condition, *at)?;
                    let Expr::Var(ref name) = bit else { unreachable!() };
                    let (body, definitely_remeasured) = self.runtime_arm(body, *at, Some(name))?;
                    if !definitely_remeasured {
                        return Err(fail(*at,
                            "runtime while must refresh its condition Bit via measure_into on every path"));
                    }
                    return self.emit(Stmt::RuntimeWhile { bit, expected, body, at: *at }, *at);
                }
                for _ in 0..100_000usize {
                    let rewritten = self.rewrite(condition, *at)?;
                    if matches!(&rewritten, Expr::Var(name) if self.type_of(name) == Some(Type::Bit)) {
                        return Err(fail(*at, "while condition must be compile-time Bool; measurement Bit requires runtime control"));
                    }
                    let proceed = match self.static_value(&rewritten, *at)? {
                        Scalar::Bool(value) => value,
                        Scalar::Float(_) => return Err(fail(*at, "while condition must be compile-time Bool")),
                    };
                    if !proceed { return Ok(()); }
                    match self.static_iteration(body, None)? {
                        Some(LoopSignal::Break) => return Ok(()),
                        Some(LoopSignal::Continue) | None => {}
                    }
                }
                let rewritten = self.rewrite(condition, *at)?;
                match self.static_value(&rewritten, *at)? {
                    Scalar::Bool(false) => Ok(()),
                    Scalar::Bool(true) => Err(fail(*at, "while expansion exceeds 100000 iterations")),
                    Scalar::Float(_) => Err(fail(*at, "while condition must be compile-time Bool")),
                }
            }
            Stmt::Assign { name, value, at } => {
                let current = match self.binding(name) {
                    Some(Binding::Mutable(v)) => *v,
                    Some(_) => return Err(fail(*at, format!("cannot assign to immutable variable '{name}'"))),
                    None => return Err(fail(*at, format!("unknown variable '{name}'"))),
                };
                let rewritten = self.rewrite(value, *at)?;
                let replacement = self.static_value(&rewritten, *at)?;
                if !matches!((current, replacement),
                    (Scalar::Float(_), Scalar::Float(_)) | (Scalar::Bool(_), Scalar::Bool(_))) {
                    return Err(fail(*at, "assignment type mismatch"));
                }
                let id = self.names.id(name).expect("previously defined binding");
                for scope in self.scopes.iter_mut().rev() {
                    if let Some(Binding::Mutable(slot)) = scope.get_mut(&id) {
                        *slot = replacement;
                        return Ok(());
                    }
                }
                Err(fail(*at, "internal error: mutable binding not found"))
            }
            Stmt::RuntimeIf { at, .. } | Stmt::RuntimeWhile { at, .. } =>
                Err(fail(*at, "internal: runtime control cannot appear in user source")),
            Stmt::DirectGate { at, .. } | Stmt::RepeatGates { at, .. } |
                Stmt::RepeatIndexedGates { at, .. } =>
                Err(fail(*at, "internal: compiled gate batch cannot appear in user source")),
            Stmt::For { variable, start, end, inclusive, body, at } => {
                let start = self.rewrite(start, *at)?;
                let end = self.rewrite(end, *at)?;
                let a = self.count(&start, *at)?;
                let end_value = self.count(&end, *at)?;
                let b = if *inclusive && a <= end_value {
                    end_value + 1
                } else { end_value };
                if b.saturating_sub(a) > 100_000 {
                    return Err(fail(*at, "static for range exceeds 100000 iterations"));
                }
                if loop_without_local_bindings(body, variable) && a < b &&
                    b - a > 1 && self.pure_gate_loop(body) {
                    self.enter();
                    let validation = self.define(variable,
                        Binding::Constant(Scalar::Float(a as f64)), *at);
                    self.leave();
                    validation?;
                    let begin = self.emitted.len();
                    self.statements(body)?;
                    return self.emit_gate_batch(begin, b - a, *at);
                }
                if b.saturating_sub(a) > 1 && self.pure_gate_loop(body) &&
                    body.iter().all(|stmt| match stmt {
                        Stmt::Call { args, .. } => !args.iter().any(contains_register_index),
                        _ => false,
                    }) && body.iter().any(|stmt| match stmt {
                        Stmt::Call { args, .. } => args.iter().any(|expr| references_name(expr, variable)),
                        _ => false,
                    }) {
                    return self.parameterized_gate_loop(variable, body, a, b, *at);
                }
                self.reserve_flat_loop(body, b.saturating_sub(a));
                if loop_without_local_bindings(body, variable) {
                    if a < b {
                        self.enter();
                        let validation = self.define(variable,
                            Binding::Constant(Scalar::Float(a as f64)), *at);
                        self.leave();
                        validation?;
                    }
                    for _ in a..b { self.statements(body)?; }
                    return Ok(());
                }
                for i in a..b {
                    match self.static_iteration(body, Some((variable.as_str(), i, *at)))? {
                        Some(LoopSignal::Break) => break,
                        Some(LoopSignal::Continue) | None => {}
                    }
                }
                Ok(())
            }
            Stmt::Function { at, .. } => Err(fail(*at, "nested function declarations are unsupported")),
            Stmt::Let { name, expected, value, is_const, mutable, at } => {
                if let Expr::Call { name: f, args } = value {
                    if f == "qubits" {
                        if expected.is_some() || *is_const { return Err(fail(*at, "registers are inferred with 'let', not typed const declarations")); }
                        if args.len() != 1 { return Err(fail(*at, "qubits(n) requires one compile-time size")); }
                        let size = self.count(&self.rewrite(&args[0], *at)?, *at)?;
                        if size == 0 { return Err(fail(*at, "register size must be at least 1")); }
                        if self.existing(name).is_some_and(|id| self.scopes.last().is_some_and(|s| s.contains_key(&id))) { return Err(fail(*at, format!("name '{name}' is already declared"))); }
                        let mut entries = Vec::with_capacity(size);
                        for _ in 0..size {
                            let generated = self.generated("reg");
                            self.emit(Stmt::Let { name: self.output_name(generated), expected: Some(Type::Qubit),
                                value: Expr::Call { name: "qubit".into(), args: Vec::new() },
                                is_const: false, mutable: false, at: *at }, *at)?;
                            self.types.insert(generated, Type::Qubit);
                            self.live.insert(generated);
                            self.new_resource(generated);
                            entries.push(generated);
                        }
                        return self.define(name, Binding::Register(entries), *at);
                    }
                }
                let rewritten = self.rewrite(value, *at)?;
                if self.is_borrowed(&rewritten) {
                    return Err(fail(*at, "cannot move a borrowed Qubit into a new binding"));
                }
                if let Expr::Call { name: f, args } = &rewritten {
                    if f == "measure" && args.len() == 1 && self.is_borrowed(&args[0]) {
                        return Err(fail(*at, "cannot consume a borrowed Qubit; use measure_keep"));
                    }
                }
                let actual = if self.scopes.len() == 1 { self.names.intern(name) } else { self.generated(name) };
                let scalar_init = if *mutable { self.static_value(&rewritten, *at).ok() } else { None };
                self.define(name, match scalar_init {
                    Some(value) => Binding::Mutable(value),
                    None => Binding::One(actual),
                }, *at)?;
                let inferred = match &rewritten {
                    Expr::Call { name: f, .. } if f == "qubit" => Some(Type::Qubit),
                    Expr::Call { name: f, .. } if f == "measure" || f == "measure_keep" => Some(Type::Bit),
                    Expr::Var(source) => self.type_of(source),
                    _ => None,
                };
                if let Some(ty) = inferred {
                    self.types.insert(actual, ty);
                    if *mutable && ty == Type::Bit { self.mutable_bits.insert(actual); }
                }
                if inferred == Some(Type::Qubit) {
                    if let Expr::Var(source) = &rewritten {
                        if let Some(resource) = self.resource_of(source) {
                            self.resource_ids.insert(actual, resource);
                        } else { self.new_resource(actual); }
                        self.mark_consumed(source);
                    } else { self.new_resource(actual); }
                    self.live.insert(actual);
                }
                if let Expr::Call { name: f, args } = &rewritten {
                    if f == "measure" && args.len() == 1 {
                        if let Expr::Var(source) = &args[0] { self.mark_consumed(source); }
                    }
                }
                if let Ok(value) = self.static_value(&rewritten, *at) {
                    self.types.insert(actual, match value { Scalar::Float(_) => Type::Float, Scalar::Bool(_) => Type::Bool });
                    self.values.insert(self.names.name(actual).to_owned(), value);
                }
                self.emit(Stmt::Let { name: self.output_name(actual), expected: *expected, value: rewritten,
                    is_const: *is_const, mutable: *mutable, at: *at }, *at)
            }
            Stmt::Call { name, args, at } => {
                if matches!(name.as_str(), "static_assert" | "static_assert_eq" |
                    "static_assert_ne" | "static_assert_live" | "static_assert_distinct") {
                    let converted = args.iter().map(|arg| self.rewrite(arg, *at))
                        .collect::<Result<Vec<_>, _>>()?;
                    return self.static_assertion(name, &converted, *at);
                }
                if self.names.id(name).is_some_and(|id| self.functions.contains_key(&id)) {
                    self.call_user(name, args, *at)
                }
                else {
                    if name == "measure_into" { self.validate_measure_into(args, *at)?; }
                    let converted: Vec<Expr> = args.iter().map(|arg| self.rewrite(arg, *at))
                        .collect::<Result<_, _>>()?;
                    if name == "measure" && converted.len() == 1 {
                        if self.is_borrowed(&converted[0]) {
                            return Err(fail(*at, "cannot consume a borrowed Qubit; use measure_keep"));
                        }
                        if let Expr::Var(source) = &converted[0] { self.mark_consumed(source); }
                    }
                    self.emit(Stmt::Call { name: name.clone(), args: converted, at: *at }, *at)
                }
            }
        }
    }
    fn static_assertion(&self, name: &str, args: &[Expr], at: Position) -> Result<(), Diagnostic> {
        let arity = if matches!(name, "static_assert" | "static_assert_live") { 1 } else { 2 };
        if args.len() != arity {
            return Err(fail(at, format!("'{name}' requires {arity} argument(s), got {}", args.len())));
        }
        if matches!(name, "static_assert_live" | "static_assert_distinct") {
            let mut first = None;
            for expression in args {
                let Expr::Var(id) = expression else {
                    return Err(fail(at, format!("{name} expects named or indexed Qubit arguments")));
                };
                if self.type_of(id) != Some(Type::Qubit) {
                    return Err(fail(at, format!("{name} expects Qubit arguments")));
                }
                if !self.is_live_name(id) {
                    return Err(fail(at, format!("cannot assert on consumed or moved Qubit '{id}'")));
                }
                if name == "static_assert_distinct" {
                    if let Some(previous) = first {
                        if previous == id { return Err(fail(at, "static_assert_distinct failed: both arguments refer to the same Qubit")); }
                    } else { first = Some(id); }
                }
            }
            return Ok(());
        }
        let lhs = self.static_value(&args[0], at)?;
        if name == "static_assert" {
            return match lhs {
                Scalar::Bool(true) => Ok(()),
                Scalar::Bool(false) => Err(fail(at, "static_assert failed: condition is false")),
                Scalar::Float(_) => Err(fail(at, "static_assert requires compile-time Bool")),
            };
        }
        let rhs = self.static_value(&args[1], at)?;
        let equal = match (lhs, rhs) {
            (Scalar::Float(x), Scalar::Float(y)) => x == y,
            (Scalar::Bool(x), Scalar::Bool(y)) => x == y,
            _ => return Err(fail(at, "static assertions require operands of the same type")),
        };
        if equal == (name == "static_assert_eq") { Ok(()) }
        else { Err(fail(at, format!("{name} failed"))) }
    }

    fn call_user(&mut self, name: &str, args: &[Expr], at: Position) -> Result<(), Diagnostic> {
        let function_id = self.names.id(name).ok_or_else(|| fail(at,
            format!("unknown function '{name}'")))?;
        let function = self.functions.get(&function_id).cloned().ok_or_else(|| fail(at,
            format!("unknown function '{name}'")))?;
        if args.len() != function.params.len() {
            return Err(fail(at, format!("function '{name}' expects {} argument(s), got {}", function.params.len(), args.len())));
        }
        if self.depth >= 32 { return Err(fail(at, "maximum function expansion depth (32) reached; recursion is unsupported")); }
        self.visited.insert(function_id);
        let mut bindings = Vec::with_capacity(args.len());
        let mut qubit_ids = function.multiple_mut_qubits
            .then(|| HashSet::with_capacity(args.len()));
        for (param, expression) in function.params.iter().zip(args.iter()) {
            let argument = self.rewrite(expression, at)?;
            let binding = match param.kind {
                ParamType::QubitMut => {
                    let Expr::BorrowMut(inner) = argument else {
                        return Err(fail(at, format!("'{}' requires '&mut Qubit'", param.name)));
                    };
                    let Expr::Var(id) = *inner else {
                        return Err(fail(at, "borrow must reference an indexed or named Qubit"));
                    };
                    if self.type_of(&id) != Some(Type::Qubit) {
                        return Err(fail(at, format!("'{}' expects a Qubit, not a classical value", param.name)));
                    }
                    if !self.is_live_name(&id) {
                        return Err(fail(at, format!("cannot borrow consumed or moved qubit '{id}'")));
                    }
                    let physical = self.resource_of(&id).ok_or_else(|| fail(at,
                        format!("unknown quantum resource backing '{id}'")))?;
                    if qubit_ids.as_mut().is_some_and(|ids| !ids.insert(physical)) {
                        return Err(fail(at, "two mutable parameters cannot alias the same qubit"));
                    }
                    Binding::One(self.existing(&id).expect("rewritten names are interned"))
                }
                ParamType::Float => {
                    let constant = self.static_value(&argument, at)?;
                    if !matches!(constant, Scalar::Float(_)) {
                        return Err(fail(at, format!("'{}' expects Float", param.name)));
                    }
                    Binding::Constant(constant)
                }
                ParamType::Bool => {
                    let constant = self.static_value(&argument, at)?;
                    if !matches!(constant, Scalar::Bool(_)) {
                        return Err(fail(at, format!("'{}' expects Bool", param.name)));
                    }
                    Binding::Constant(constant)
                }
            };
            bindings.push(binding);
        }
        if let Some(gates) = &function.prepared_leaf {
            for gate in gates.iter() {
                let spec = sema::gate_spec(gate.gate);
                if gate.args.len() != spec.parameters + spec.qubits {
                    return Err(fail(gate.at, format!("'{}' requires {} argument(s), got {}",
                        spec.name, spec.parameters + spec.qubits, gate.args.len())));
                }
                let mut angles = [0.0_f64; 4];
                let mut qubits = [QubitId(0); 3];
                for (i, angle) in angles.iter_mut().take(spec.parameters).enumerate() {
                    *angle = prepared_float(&gate.args[i], &bindings, gate.at)?;
                }
                for (i, target) in qubits.iter_mut().take(spec.qubits).enumerate() {
                    let PreparedExpr::Parameter(index) = &gate.args[spec.parameters + i] else {
                        return Err(fail(gate.at, "a qubit argument must be a named live qubit"));
                    };
                    let Binding::One(id) = &bindings[*index as usize] else {
                        return Err(fail(gate.at, "expected Qubit argument"));
                    };
                    if self.types.get(id) != Some(&Type::Qubit) || !self.live.contains(id) {
                        return Err(fail(gate.at, "cannot use consumed or moved qubit"));
                    }
                    *target = *self.resource_ids.get(id).ok_or_else(|| fail(gate.at, "unknown QubitId"))?;
                }
                for i in 0..spec.qubits {
                    if qubits[..i].contains(&qubits[i]) {
                        return Err(fail(gate.at, if matches!(spec.name, "cx" | "CX") {
                            "CX control and target must be distinct qubits".to_owned()
                        } else { format!("'{}' requires distinct qubit operands", spec.name) }));
                    }
                }
                self.emit(Stmt::DirectGate { gate: gate.gate, qubits, angles, at: gate.at }, gate.at)?;
            }
            return Ok(());
        }
        //Do not allow functions to capture arbitrary caller locals by accident Only explicitly passed
        //parameters enter a function's lexical scope
        let caller_scopes = std::mem::take(&mut self.scopes);
        self.enter();
        self.enter();
        self.depth += 1;
        let caller_loop_depth = std::mem::replace(&mut self.loop_depth, 0);
        let result = (|| -> Result<(), Diagnostic> {
            let mut inserted_borrows = Vec::new();
            for (param, binding) in function.params.iter().zip(bindings) {
                if let Binding::One(ref id) = binding {
                    if self.borrowed.insert(*id) {
                        inserted_borrows.push(*id);
                    }
                }
                self.define(&param.name, binding, param.at)?;
            }
            let body_result = self.statements(&function.body);
            for id in inserted_borrows { self.borrowed.remove(&id); }
            body_result
        })();
        self.depth -= 1;
        self.loop_depth = caller_loop_depth;
        self.leave();
        self.leave();
        self.scopes = caller_scopes;
        result
    }
}
