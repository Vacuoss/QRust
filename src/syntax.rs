//QRust syntax v0.5

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Position { pub line: usize, pub column: usize }

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenKind<'a> {
    Ident(&'a str), Number(&'a str), StringLit(&'a str), Lifetime(&'a str),
    LParen, RParen, LBrace, RBrace, LBracket, RBracket, Comma, Colon, Equal, Semi, Dot, DotDot, DotDotEq, FatArrow, Amp,
    Plus, Minus, Star, Slash, Percent, Bang,
    PlusEq, MinusEq, StarEq, SlashEq, PercentEq,
    EqEq, NotEq, Less, LessEq, Greater, GreaterEq, AndAnd, OrOr,
}

#[derive(Clone, Copy, Debug)]
pub struct Token<'a> { pub kind: TokenKind<'a>, pub at: Position }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic { pub at: Position, pub message: String }

impl std::fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}: {}", self.at.line, self.at.column, self.message)
    }
}

fn error(at: Position, message: impl Into<String>) -> Diagnostic {
    Diagnostic { at, message: message.into() }
}

pub fn lex(input: &str) -> Result<Vec<Token<'_>>, Diagnostic> {
    let bytes = input.as_bytes();
    let capacity = if bytes.len() <= 2048 { bytes.len() / 3 + 1 }
        else { bytes.len() / 5 + 1 };
    let mut tokens = Vec::with_capacity(capacity);
    let (mut index, mut line, mut column) = (0, 1, 1);
    while index < bytes.len() {
        let byte = bytes[index];
        match byte {
            b'\n' => { index += 1; line += 1; column = 1; continue; }
            b' ' | b'\t' | b'\r' => { index += 1; column += 1; continue; }
            b'/' if bytes.get(index + 1) == Some(&b'/') => {
                while index < bytes.len() && bytes[index] != b'\n' {
                    index += 1; column += 1;
                }
                continue;
            }
            b'/' if bytes.get(index + 1) == Some(&b'*') => {
                let at = Position { line, column };
                index += 2; column += 2;
                let mut depth = 1usize;
                while index < bytes.len() && depth > 0 {
                    if bytes[index] == b'/' && bytes.get(index + 1) == Some(&b'*') {
                        depth += 1; index += 2; column += 2;
                    } else if bytes[index] == b'*' && bytes.get(index + 1) == Some(&b'/') {
                        depth -= 1; index += 2; column += 2;
                    } else if bytes[index] == b'\n' {
                        index += 1; line += 1; column = 1;
                    } else { index += 1; column += 1; }
                }
                if depth != 0 { return Err(error(at, "unterminated block comment")); }
                continue;
            }
            _ => {}
        }
        let at = Position { line, column };
        let start = index;
        if byte == b'"' {
            index += 1;
            let string_start = index;
            let mut closed = false;
            while index < bytes.len() {
                if bytes[index] == b'\\' {
                    index += 1;
                    if index >= bytes.len() || bytes[index] == b'\n' {
                        return Err(error(at, "invalid string escape"));
                    }
                    index += 1;
                } else if bytes[index] == b'"' {
                    closed = true; break;
                } else if bytes[index] == b'\n' {
                    return Err(error(at, "string literal may not contain a newline"));
                } else { index += 1; }
            }
            if !closed { return Err(error(at, "unterminated string literal")); }
            let lit = &input[string_start..index];
            index += 1;
            column += index - start;
            tokens.push(Token { kind: TokenKind::StringLit(lit), at });
            continue;
        }
        if byte == b'\'' {
            index += 1;
            if !bytes.get(index).is_some_and(|b|b.is_ascii_alphabetic() || *b==b'_') {
                return Err(error(at,"expected lifetime name after apostrophe"));
            }
            let name_start=index;
            index+=1;
            while bytes.get(index).is_some_and(|b|b.is_ascii_alphanumeric() || *b==b'_') {index+=1;}
            column+=index-start;
            tokens.push(Token{kind:TokenKind::Lifetime(&input[name_start..index]),at});
            continue;
        }
        if byte.is_ascii_alphabetic() || byte == b'_' {
            index += 1;
            while index < bytes.len() && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_') {
                index += 1;
            }
            column += index - start;
            //Enforce the compiler-private namespace at the *source* boundary After lowering, synthetic names must
            //be accepted by sema
            if input[start..index].starts_with("__qrust_") {
                return Err(error(at, "'__qrust_' is a reserved compiler identifier prefix"));
            }
            tokens.push(Token { kind: TokenKind::Ident(&input[start..index]), at });
            continue;
        }
        if byte.is_ascii_digit() || (byte == b'.' && bytes.get(index + 1).is_some_and(u8::is_ascii_digit)) {
            if byte != b'.' {
                index += 1;
                while bytes.get(index).is_some_and(|b| b.is_ascii_digit() || *b == b'_') { index += 1; }
            }
            if bytes.get(index) == Some(&b'.') && bytes.get(index + 1) != Some(&b'.') {
                index += 1;
                while bytes.get(index).is_some_and(|b| b.is_ascii_digit() || *b == b'_') { index += 1; }
            }
            if matches!(bytes.get(index).copied(), Some(b'e' | b'E')) {
                index += 1;
                if matches!(bytes.get(index).copied(), Some(b'+' | b'-')) { index += 1; }
                let digit_start = index;
                while bytes.get(index).is_some_and(|b| b.is_ascii_digit() || *b == b'_') { index += 1; }
                if index == digit_start { return Err(error(at, "expected exponent digits")); }
            }
            let raw = &input[start..index];
            if raw.as_bytes().windows(2).any(|w| w[0] == b'_' && w[1] == b'_') ||
                raw.as_bytes().iter().enumerate().any(|(i, &b)| b == b'_' &&
                    (i == 0 || i + 1 == raw.len() || !raw.as_bytes()[i-1].is_ascii_digit() || !raw.as_bytes()[i+1].is_ascii_digit())) {
                return Err(error(at, "numeric separators '_' must occur between digits"));
            }
            column += index - start;
            tokens.push(Token { kind: TokenKind::Number(raw), at });
            continue;
        }
        let pair = bytes.get(index + 1).copied();
        let two = match (byte, pair) {
            (b'=', Some(b'=')) => Some(TokenKind::EqEq),
            (b'!', Some(b'=')) => Some(TokenKind::NotEq),
            (b'<', Some(b'=')) => Some(TokenKind::LessEq),
            (b'>', Some(b'=')) => Some(TokenKind::GreaterEq),
            (b'&', Some(b'&')) => Some(TokenKind::AndAnd),
            (b'|', Some(b'|')) => Some(TokenKind::OrOr),
            (b'.', Some(b'.')) if bytes.get(index + 2) == Some(&b'=') => {
                tokens.push(Token { kind: TokenKind::DotDotEq, at });
                index += 3; column += 3; continue;
            }
            (b'.', Some(b'.')) => Some(TokenKind::DotDot),
            (b'=', Some(b'>')) => Some(TokenKind::FatArrow),
            (b'+', Some(b'=')) => Some(TokenKind::PlusEq),
            (b'-', Some(b'=')) => Some(TokenKind::MinusEq),
            (b'*', Some(b'=')) => Some(TokenKind::StarEq),
            (b'/', Some(b'=')) => Some(TokenKind::SlashEq),
            (b'%', Some(b'=')) => Some(TokenKind::PercentEq),
            _ => None,
        };
        if let Some(kind) = two {
            tokens.push(Token { kind, at }); index += 2; column += 2; continue;
        }
        let kind = match byte {
            b'(' => TokenKind::LParen, b')' => TokenKind::RParen,
            b'{' => TokenKind::LBrace, b'}' => TokenKind::RBrace,
            b'[' => TokenKind::LBracket, b']' => TokenKind::RBracket,
            b'&' => TokenKind::Amp,
            b',' => TokenKind::Comma, b':' => TokenKind::Colon,
            b'=' => TokenKind::Equal, b';' => TokenKind::Semi, b'.' => TokenKind::Dot,
            b'+' => TokenKind::Plus, b'-' => TokenKind::Minus,
            b'*' => TokenKind::Star, b'/' => TokenKind::Slash,
            b'%' => TokenKind::Percent, b'!' => TokenKind::Bang,
            b'<' => TokenKind::Less, b'>' => TokenKind::Greater,
            _ => return Err(error(at, format!("unexpected character '{}'; QRust uses ASCII operators", input[index..].chars().next().unwrap_or('?')))),
        };
        tokens.push(Token { kind, at }); index += 1; column += 1;
    }
    Ok(tokens)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(std::rc::Rc<str>);

impl Name {
    pub fn as_str(&self) -> &str { &self.0 }
    #[cfg(test)]
    pub fn shares_storage_with(&self, other: &Self) -> bool {
        std::rc::Rc::ptr_eq(&self.0, &other.0)
    }
}
impl std::ops::Deref for Name {
    type Target = str;
    fn deref(&self) -> &str { self.as_str() }
}
impl std::borrow::Borrow<str> for Name {
    fn borrow(&self) -> &str { self.as_str() }
}
impl AsRef<str> for Name {
    fn as_ref(&self) -> &str { self.as_str() }
}
impl From<std::rc::Rc<str>> for Name {
    fn from(value: std::rc::Rc<str>) -> Self { Self(value) }
}
impl From<&str> for Name {
    fn from(value: &str) -> Self { Self(std::rc::Rc::from(value)) }
}
impl From<String> for Name {
    fn from(value: String) -> Self { Self(std::rc::Rc::from(value.as_str())) }
}
impl From<Name> for String {
    fn from(value: Name) -> Self { value.as_str().to_owned() }
}
impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}
impl PartialEq<str> for Name {
    fn eq(&self, other: &str) -> bool { self.as_str() == other }
}
impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool { self.as_str() == *other }
}
impl PartialEq<String> for Name {
    fn eq(&self, other: &String) -> bool { self.as_str() == other.as_str() }
}
impl PartialEq<Name> for str {
    fn eq(&self, other: &Name) -> bool { self == other.as_str() }
}
impl PartialEq<Name> for String {
    fn eq(&self, other: &Name) -> bool { self.as_str() == other.as_str() }
}

#[derive(Clone, Copy, Debug)]
pub enum BinaryOp { Add, Sub, Mul, Div, Rem, Eq, Ne, Lt, Le, Gt, Ge, And, Or }

#[derive(Clone, Copy, Debug)]
pub enum UnaryOp { Neg, Not }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type { Float, Bool, Qubit, Bit }

#[derive(Clone, Debug)]
pub enum MatchPattern { Bool(bool), Integer(i64), Wildcard }

#[derive(Clone, Debug)]
pub struct ExprArena {
    pub nodes: Vec<ExprNode>,
    pub root: u32,
    pub has_short_circuit: bool,
}

#[derive(Clone, Debug)]
pub enum ExprNode {
    Atom(Expr),
    Binary { left: u32, op: BinaryOp, right: u32 },
}

impl ExprArena {
    pub fn try_map_atoms<E>(&self, mut map: impl FnMut(&Expr) -> Result<Expr, E>) -> Result<Self, E> {
        let mut nodes = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            nodes.push(match node {
                ExprNode::Atom(expr) => ExprNode::Atom(map(expr)?),
                ExprNode::Binary { left, op, right } => ExprNode::Binary {
                    left: *left, op: *op, right: *right,
                },
            });
        }
        Ok(Self { nodes, root: self.root, has_short_circuit: self.has_short_circuit })
    }
    pub fn atoms(&self) -> impl Iterator<Item=&Expr> {
        self.nodes.iter().filter_map(|node| match node {
            ExprNode::Atom(expr) => Some(expr),
            ExprNode::Binary { .. } => None,
        })
    }
}

#[derive(Clone, Debug)]
pub enum Expr {
    Number(f64), Bool(bool), Var(Name),
    Unary(UnaryOp, Box<Expr>),
    Binary(Box<Expr>, BinaryOp, Box<Expr>),
    Call { name: Name, args: Vec<Expr> },
    Index { name: Name, index: Box<Expr> },
    BorrowMut(Box<Expr>),
    Arena(Box<ExprArena>),
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Block { statements: Vec<Stmt>, at: Position },
    If { condition: Expr, then_branch: Vec<Stmt>, else_branch: Vec<Stmt>, at: Position },
    For { variable: Name, start: Expr, end: Expr, inclusive: bool, body: Vec<Stmt>, at: Position },
    Match { value: Expr, arms: Vec<(MatchPattern, Vec<Stmt>)>, at: Position },
    While { condition: Expr, body: Vec<Stmt>, at: Position },
    //Rust-inspired loop control is statically lowered. Dynamic Bit loops deliberately do not permit
    //break/continue until hardware semantics exist
    Loop { body: Vec<Stmt>, at: Position },
    Break { at: Position },
    Continue { at: Position },
    //Lowering-only: measurement-controlled branches contain only non-consuming quantum calls and cannot
    //modify the ownership environment
    RuntimeIf { bit: Expr, expected: bool, then_branch: Vec<Stmt>,
        else_branch: Vec<Stmt>, at: Position },
    //Lowering-only runtime loop. Every execution path must refresh its classical condition bit without
    //consuming any qubit handle
    RuntimeWhile { bit: Expr, expected: bool, body: Vec<Stmt>, at: Position },
    Assign { name: Name, value: Expr, at: Position },
    DirectGate { gate: crate::sema::GateId, qubits: [crate::ids::QubitId; 3],
        angles: [f64; 4], at: Position },
    RepeatGates { template: Vec<Stmt>, repeats: usize, at: Position },
    RepeatIndexedGates { index: Name, start: usize, end: usize,
        template: Vec<Stmt>, checks: Vec<(Expr, Type)>, at: Position },
    Function { name: Name, params: Vec<Param>, body: Vec<Stmt>, at: Position },
    Let { name: Name, expected: Option<Type>, value: Expr, is_const: bool, mutable: bool, at: Position },
    Call { name: Name, args: Vec<Expr>, at: Position },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamType { Float, Bool, QubitMut }

#[derive(Clone, Debug)]
pub struct Param { pub name: Name, pub kind: ParamType, pub at: Position }

fn infix_rule(kind: TokenKind<'_>) -> Option<(BinaryOp, u8, u8)> {
    let (op, bp) = match kind {
        TokenKind::OrOr => (BinaryOp::Or, 1),
        TokenKind::AndAnd => (BinaryOp::And, 3),
        TokenKind::EqEq => (BinaryOp::Eq, 5),
        TokenKind::NotEq => (BinaryOp::Ne, 5),
        TokenKind::Less => (BinaryOp::Lt, 7),
        TokenKind::LessEq => (BinaryOp::Le, 7),
        TokenKind::Greater => (BinaryOp::Gt, 7),
        TokenKind::GreaterEq => (BinaryOp::Ge, 7),
        TokenKind::Plus => (BinaryOp::Add, 9),
        TokenKind::Minus => (BinaryOp::Sub, 9),
        TokenKind::Star => (BinaryOp::Mul, 11),
        TokenKind::Slash => (BinaryOp::Div, 11),
        TokenKind::Percent => (BinaryOp::Rem, 11),
        _ => return None,
    };
    Some((op, bp, bp + 1))
}

pub const MAX_SOURCE_BLOCK_DEPTH: usize = 32;
pub const MAX_LOWERING_SCOPE_DEPTH: usize = MAX_SOURCE_BLOCK_DEPTH + 16;
pub const MAX_PARSER_CALL_DEPTH: usize = 96;
pub const MAX_BINARY_CHAIN_DEPTH: usize = 96; //legacy Box AST compatibility threshold
pub const MAX_ARENA_EXPR_NODES: usize = 1_000_000;

pub struct Parsed { pub statements: Vec<Stmt>, pub needs_lowering: bool }

pub struct Parser<'a, 't> { tokens: std::borrow::Cow<'t, [Token<'a>]>, index: usize, needs_lowering: bool, block_depth: usize, recursive_depth: usize, names: std::collections::HashMap<&'a str, Name> }

impl<'a, 't> Parser<'a, 't> {
    pub fn new(tokens: Vec<Token<'a>>) -> Self {
        let estimate = (tokens.len() / 7).min(128);
        Self { tokens: std::borrow::Cow::Owned(tokens), index: 0, needs_lowering: false,
            block_depth: 0, recursive_depth: 0, names: std::collections::HashMap::with_capacity(estimate) }
    }
    pub fn from_slice(tokens: &'t [Token<'a>]) -> Self {
        let estimate = (tokens.len() / 7).min(128);
        Self { tokens: std::borrow::Cow::Borrowed(tokens), index: 0, needs_lowering: false,
            block_depth: 0, recursive_depth: 0, names: std::collections::HashMap::with_capacity(estimate) }
    }
    fn at(&self) -> Position {
        self.tokens.get(self.index).or_else(|| self.tokens.last())
            .map(|token| token.at).unwrap_or(Position { line: 1, column: 1 })
    }
    fn peek(&self) -> Option<TokenKind<'a>> { self.tokens.get(self.index).map(|token| token.kind) }
    fn consume(&mut self, kind: TokenKind<'a>) -> bool {
        if self.peek() == Some(kind) { self.index += 1; true } else { false }
    }
    fn expect(&mut self, kind: TokenKind<'a>, name: &str) -> Result<(), Diagnostic> {
        if self.consume(kind) { Ok(()) } else { Err(error(self.at(), format!("expected '{name}'"))) }
    }
    fn intern(&mut self, text: &'a str) -> Name {
        if let Some(name) = self.names.get(text) { return name.clone(); }
        let name = Name::from(text);
        self.names.insert(text, name.clone());
        name
    }
    fn ident(&mut self) -> Result<(Name, Position), Diagnostic> {
        let at = self.at();
        match self.peek() {
            Some(TokenKind::Ident(name)) => { self.index += 1; Ok((self.intern(name), at)) }
            _ => Err(error(at, "expected identifier")),
        }
    }
    fn guarded<T>(&mut self, parse: impl FnOnce(&mut Self) -> Result<T, Diagnostic>) -> Result<T, Diagnostic> {
        if self.recursive_depth >= MAX_PARSER_CALL_DEPTH {
            return Err(error(self.at(), format!(
                "parser recursion limit ({MAX_PARSER_CALL_DEPTH}) exceeded")));
        }
        self.recursive_depth += 1;
        let result = parse(self);
        self.recursive_depth -= 1;
        result
    }
    //Parse those without entering the Pratt expression loop, but only when the following token terminates
    //the argument
    fn argument(&mut self) -> Result<Expr, Diagnostic> {
        let one_token = matches!(
            self.tokens.get(self.index + 1).map(|token| token.kind),
            Some(TokenKind::Comma | TokenKind::RParen)
        );
        if one_token {
            match self.peek() {
                Some(TokenKind::Ident("true")) => {
                    self.index += 1;
                    return Ok(Expr::Bool(true));
                }
                Some(TokenKind::Ident("false")) => {
                    self.index += 1;
                    return Ok(Expr::Bool(false));
                }
                Some(TokenKind::Ident(name)) => {
                    self.index += 1;
                    return Ok(Expr::Var(self.intern(name)));
                }
                Some(TokenKind::Number(raw)) => {
                    let at = self.at();
                    self.index += 1;
                    return Self::number_expr(raw, at);
                }
                _ => {}
            }
        }
        self.expression(0)
    }
    fn number_expr(number: &str, at: Position) -> Result<Expr, Diagnostic> {
        let mut stack_digits = [0u8; 128];
        let heap_digits;
        let text = if !number.contains('_') { number }
            else if number.len() <= stack_digits.len() {
                let mut n = 0;
                for &b in number.as_bytes() {
                    if b != b'_' { stack_digits[n] = b; n += 1; }
                }
                std::str::from_utf8(&stack_digits[..n]).expect("ASCII numeric literal")
            } else {
                heap_digits = number.replace('_', "");
                heap_digits.as_str()
            };
        let value = text.parse::<f64>().map_err(|_| error(at, "invalid numeric literal"))?;
        if !value.is_finite() { return Err(error(at, "numeric literal must be finite")); }
        Ok(Expr::Number(value))
    }
    fn arguments(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        self.guarded(|this| this.arguments_inner())
    }
    fn arguments_inner(&mut self) -> Result<Vec<Expr>, Diagnostic> {
        self.expect(TokenKind::LParen, "(")?;
        if self.consume(TokenKind::RParen) { return Ok(Vec::new()); }
        let mut args = Vec::with_capacity(4);
        loop {
            args.push(self.argument()?);
            if self.consume(TokenKind::RParen) { break; }
            self.expect(TokenKind::Comma, ",")?;
            if self.consume(TokenKind::RParen) { break; } //Rust-like trailing comma
        }
        Ok(args)
    }
    fn primary(&mut self) -> Result<Expr, Diagnostic> {
        self.guarded(|this| this.primary_inner())
    }
    fn primary_inner(&mut self) -> Result<Expr, Diagnostic> {
        match self.peek() {
            Some(TokenKind::Minus) => { self.index += 1; Ok(Expr::Unary(UnaryOp::Neg, Box::new(self.expression(13)?))) }
            Some(TokenKind::Plus) => { self.index += 1; self.expression(13) }
            Some(TokenKind::Bang) => { self.index += 1; Ok(Expr::Unary(UnaryOp::Not, Box::new(self.expression(13)?))) }
            Some(TokenKind::Amp) => {
                self.needs_lowering = true;
                self.index += 1;
                let (keyword, at) = self.ident()?;
                if keyword != "mut" { return Err(error(at, "only '&mut' borrows are supported")); }
                Ok(Expr::BorrowMut(Box::new(self.primary()?)))
            }
            Some(TokenKind::Number(number)) => {
                let at = self.at(); self.index += 1;
                Self::number_expr(number, at)
            }
            Some(TokenKind::Ident("true")) => { self.index += 1; Ok(Expr::Bool(true)) }
            Some(TokenKind::Ident("false")) => { self.index += 1; Ok(Expr::Bool(false)) }
            Some(TokenKind::Ident("async" | "await")) => {
                Err(error(self.at(), crate::async_ir::ASYNC_UNSUPPORTED))
            }
            Some(TokenKind::Ident(_)) => {
                let (name, _) = self.ident()?;
                if self.peek() == Some(TokenKind::LParen) {
                    if name == "qubits" { self.needs_lowering = true; }
                    let args = self.arguments()?; Ok(Expr::Call { name, args })
                } else if self.consume(TokenKind::LBracket) {
                    self.needs_lowering = true;
                    let index = self.expression(0)?;
                    self.expect(TokenKind::RBracket, "]")?;
                    Ok(Expr::Index { name, index: Box::new(index) })
                } else { Ok(Expr::Var(name)) }
            }
            Some(TokenKind::LParen) => {
                self.index += 1;
                let expr = self.expression(0)?; self.expect(TokenKind::RParen, ")")?; Ok(expr)
            }
            _ => Err(error(self.at(), "expected expression")),
        }
    }
    fn expression(&mut self, min_bp: u8) -> Result<Expr, Diagnostic> {
        let expression = self.guarded(|this| this.expression_inner(min_bp))?;
        //Recognize Rust's postfix await explicitly. Do not silently accept it as ordinary indexing or a method:
        //suspension needs a borrow checker
        if self.peek() == Some(TokenKind::Dot) &&
            matches!(self.tokens.get(self.index + 1).map(|t| t.kind),
                Some(TokenKind::Ident("await"))) {
            return Err(error(self.at(), crate::async_ir::AWAIT_UNSUPPORTED));
        }
        Ok(expression)
    }
    fn expression_inner(&mut self, min_bp: u8) -> Result<Expr, Diagnostic> {
        let first = self.primary()?;
        //Zero-allocation common case: identifiers, literals and gate angles without an infix operator never
        //construct a temporary arena
        let Some((first_op, first_bp, _)) = self.peek().and_then(infix_rule)
            .filter(|(_, bp, _)| *bp >= min_bp) else { return Ok(first); };
        self.index += 1;
        let second = self.primary()?;
        if !self.peek().and_then(infix_rule).is_some_and(|(_, bp, _)| bp >= min_bp) {
            return Ok(Expr::Binary(Box::new(first), first_op, Box::new(second)));
        }
        let mut nodes = Vec::<ExprNode>::with_capacity(8);
        let mut values = Vec::<u32>::with_capacity(8);
        let mut operators = Vec::<(BinaryOp, u8)>::with_capacity(8);
        nodes.push(ExprNode::Atom(first));
        nodes.push(ExprNode::Atom(second));
        values.push(0);
        values.push(1);
        operators.push((first_op, first_bp));
        let mut has_short_circuit = matches!(first_op, BinaryOp::And | BinaryOp::Or);
        while let Some((op, left_bp, _right_bp)) = self.peek().and_then(infix_rule) {
            if left_bp < min_bp { break; }
            while operators.last().is_some_and(|(_, bp)| *bp >= left_bp) {
                let (previous, _) = operators.pop().unwrap();
                let right = values.pop().unwrap();
                let left = values.pop().unwrap();
                let id = nodes.len() as u32;
                nodes.push(ExprNode::Binary { left, op: previous, right });
                values.push(id);
            }
            if nodes.len() + operators.len() + 2 > MAX_ARENA_EXPR_NODES {
                return Err(error(self.at(), "expression exceeds arena node limit"));
            }
            self.index += 1;
            has_short_circuit |= matches!(op, BinaryOp::And | BinaryOp::Or);
            operators.push((op, left_bp));
            let right = nodes.len() as u32;
            nodes.push(ExprNode::Atom(self.primary()?));
            values.push(right);
        }
        while let Some((op, _)) = operators.pop() {
            let right = values.pop().unwrap();
            let left = values.pop().unwrap();
            let id = nodes.len() as u32;
            nodes.push(ExprNode::Binary { left, op, right });
            values.push(id);
        }
        let root = values.pop().unwrap();
        if nodes.len() <= MAX_BINARY_CHAIN_DEPTH * 2 + 1 {
            fn take_atom(nodes: &mut [ExprNode], index: u32) -> Expr {
                let old = std::mem::replace(&mut nodes[index as usize],
                    ExprNode::Atom(Expr::Bool(false)));
                match old {
                    ExprNode::Atom(expr) => expr,
                    ExprNode::Binary { .. } => unreachable!("child was not reduced"),
                }
            }
            for index in 0..nodes.len() {
                let binary = match &nodes[index] {
                    ExprNode::Binary { left, op, right } => Some((*left, *op, *right)),
                    ExprNode::Atom(_) => None,
                };
                if let Some((left, op, right)) = binary {
                    let left = take_atom(&mut nodes, left);
                    let right = take_atom(&mut nodes, right);
                    nodes[index] = ExprNode::Atom(Expr::Binary(
                        Box::new(left), op, Box::new(right)));
                }
            }
            Ok(take_atom(&mut nodes, root))
        } else {
            Ok(Expr::Arena(Box::new(ExprArena { nodes, root, has_short_circuit })))
        }
    }
    fn block(&mut self) -> Result<Vec<Stmt>, Diagnostic> {
        if self.block_depth >= MAX_SOURCE_BLOCK_DEPTH {
            return Err(error(self.at(), format!(
                "nested block scope limit ({MAX_SOURCE_BLOCK_DEPTH}) exceeded")));
        }
        self.expect(TokenKind::LBrace, "{")?;
        self.block_depth += 1;
        let result = (|| -> Result<Vec<Stmt>, Diagnostic> {
            let mut out = Vec::new();
            while self.peek() != Some(TokenKind::RBrace) {
                if self.peek().is_none() {
                    return Err(error(self.at(), "unclosed block: expected '}'"));
                }
                out.push(self.statement()?);
            }
            self.expect(TokenKind::RBrace, "}")?;
            Ok(out)
        })();
        self.block_depth -= 1;
        result
    }
    fn statement(&mut self) -> Result<Stmt, Diagnostic> {
        self.guarded(|this| this.statement_inner())
    }
    fn statement_inner(&mut self) -> Result<Stmt, Diagnostic> {
        let at = self.at();
        if self.peek() == Some(TokenKind::LBrace) {
            self.needs_lowering = true;
            return Ok(Stmt::Block { statements: self.block()?, at });
        }
        //Keywords do not need an owned String; keep the borrowed token until we know this statement is a
        //user-named operation call
        let head = match self.peek() {
            Some(TokenKind::Ident(word)) => { self.index += 1; word }
            _ => return Err(error(at, "expected identifier")),
        };
        match head {
            "async" | "await" => Err(error(at, crate::async_ir::ASYNC_UNSUPPORTED)),
            "fn" => {
                self.needs_lowering = true;
                let (name, _) = self.ident()?;
                self.expect(TokenKind::LParen, "(")?;
                let mut params = Vec::new();
                if !self.consume(TokenKind::RParen) {
                    loop {
                        let (param_name, param_at) = self.ident()?;
                        self.expect(TokenKind::Colon, ":")?;
                        let kind = if self.consume(TokenKind::Amp) {
                            let (mut_name, mut_at) = self.ident()?;
                            if mut_name != "mut" { return Err(error(mut_at, "expected 'mut' after '&'")); }
                            let (type_name, type_at) = self.ident()?;
                            if type_name != "Qubit" { return Err(error(type_at, "only '&mut Qubit' borrows are supported")); }
                            ParamType::QubitMut
                        } else {
                            let (type_name, type_at) = self.ident()?;
                            crate::surface::scalar_parameter_type(&type_name)
                                .ok_or_else(|| error(type_at, "function parameter type must be Float, Bool or &mut Qubit"))?
                        };
                        params.push(Param { name: param_name, kind, at: param_at });
                        if self.consume(TokenKind::RParen) { break; }
                        self.expect(TokenKind::Comma, ",")?;
                        if self.consume(TokenKind::RParen) { break; }
                    }
                }
                Ok(Stmt::Function { name, params, body: self.block()?, at })
            }
            "if" => {
                self.needs_lowering = true;
                let condition = self.expression(0)?;
                let then_branch = self.block()?;
                let else_branch = if let Some(TokenKind::Ident("else")) = self.peek() {
                    self.index += 1;
                    if let Some(TokenKind::Ident("if")) = self.peek() {
                        vec![self.statement()?]
                    } else { self.block()? }
                } else { Vec::new() };
                Ok(Stmt::If { condition, then_branch, else_branch, at })
            }
            "for" => {
                self.needs_lowering = true;
                let (variable, _) = self.ident()?;
                let (word, in_at) = self.ident()?;
                if word != "in" { return Err(error(in_at, "expected 'in' in for loop")); }
                let start = self.expression(0)?;
                let inclusive = if self.consume(TokenKind::DotDotEq) { true }
                    else { self.expect(TokenKind::DotDot, "..")?; false };
                let end = self.expression(0)?;
                Ok(Stmt::For { variable, start, end, inclusive, body: self.block()?, at })
            }
            "while" => {
                self.needs_lowering = true;
                let condition = self.expression(0)?;
                Ok(Stmt::While { condition, body: self.block()?, at })
            },
            "loop" => {
                self.needs_lowering = true;
                Ok(Stmt::Loop { body: self.block()?, at })
            },
            "break" => {
                self.needs_lowering = true;
                self.expect(TokenKind::Semi, ";")?;
                Ok(Stmt::Break { at })
            },
            "continue" => {
                self.needs_lowering = true;
                self.expect(TokenKind::Semi, ";")?;
                Ok(Stmt::Continue { at })
            },
            "match" => {
                self.needs_lowering = true;
                let value = self.expression(0)?;
                self.expect(TokenKind::LBrace, "{")?;
                let mut arms = Vec::new();
                while !self.consume(TokenKind::RBrace) {
                    if arms.len() >= 256 { return Err(error(at, "match exceeds 256 arms")); }
                    let pattern_at = self.at();
                    let pattern = match self.peek() {
                        Some(TokenKind::Ident("true")) => { self.index += 1; MatchPattern::Bool(true) }
                        Some(TokenKind::Ident("false")) => { self.index += 1; MatchPattern::Bool(false) }
                        Some(TokenKind::Ident("_")) => { self.index += 1; MatchPattern::Wildcard }
                        Some(TokenKind::Minus | TokenKind::Number(_)) => {
                            let negative = self.consume(TokenKind::Minus);
                            let Some(TokenKind::Number(raw)) = self.peek() else {
                                return Err(error(self.at(), "expected integer pattern after '-'"));
                            };
                            let Expr::Number(value) = Self::number_expr(raw, self.at())? else { unreachable!() };
                            self.index += 1;
                            let value = if negative { -value } else { value };
                            if value.fract() != 0.0 || value.abs() > 9_007_199_254_740_991.0 {
                                return Err(error(pattern_at, "match patterns require exactly represented integers"));
                            }
                            MatchPattern::Integer(value as i64)
                        }
                        _ => return Err(error(pattern_at, "match patterns must be Bool, integer or '_'")),
                    };
                    self.expect(TokenKind::FatArrow, "=>")?;
                    arms.push((pattern, self.block()?));
                    if self.consume(TokenKind::RBrace) { break; }
                    self.expect(TokenKind::Comma, ",")?;
                }
                if arms.is_empty() { return Err(error(at, "match requires at least one arm")); }
                Ok(Stmt::Match { value, arms, at })
            },
            "return" => Err(error(at, "return values are not supported in 0.4; functions return ()")),
            "let" | "const" => {
                let mutable = if let Some(TokenKind::Ident("mut")) = self.peek() {
                    self.index += 1; true
                } else { false };
                if head == "const" && mutable { return Err(error(at, "const cannot be mutable")); }
                let (name, _) = self.ident()?;
                if crate::surface::reserved_identifier(&name) {
                    return Err(error(at, format!("'{name}' is a reserved keyword")));
                }
                let expected = if self.consume(TokenKind::Colon) {
                    let (kind, type_at) = self.ident()?;
                    //Rust-like type placeholder: `let value: _ = expr;` delegates to the existing semantic inference rules
                    //It never materializes a runtime-tagged value
                    if kind == "_" { None } else {
                        Some(crate::surface::declaration_type(&kind)
                            .ok_or_else(|| error(type_at, format!("unknown type '{kind}'")))?)
                    }
                } else { None };
                self.expect(TokenKind::Equal, "=")?;
                let value = self.expression(0)?;
                self.expect(TokenKind::Semi, ";")?;
                Ok(Stmt::Let { name, expected, value, is_const: head == "const", mutable, at })
            }
            "else" => Err(error(at, "'else' without 'if'")),
            _ => {
                if crate::surface::reserved_identifier(head) {
                    return Err(error(at, format!("unsupported or misplaced keyword '{head}'")));
                }
                let operator = match self.peek() {
                    Some(TokenKind::Equal) => Some(None),
                    Some(TokenKind::PlusEq) => Some(Some(BinaryOp::Add)),
                    Some(TokenKind::MinusEq) => Some(Some(BinaryOp::Sub)),
                    Some(TokenKind::StarEq) => Some(Some(BinaryOp::Mul)),
                    Some(TokenKind::SlashEq) => Some(Some(BinaryOp::Div)),
                    Some(TokenKind::PercentEq) => Some(Some(BinaryOp::Rem)),
                    _ => None,
                };
                if let Some(op) = operator {
                    self.needs_lowering = true;
                    self.index += 1;
                    let rhs = self.expression(0)?;
                    self.expect(TokenKind::Semi, ";")?;
                    let value = match op {
                        Some(op) => Expr::Binary(Box::new(Expr::Var(self.intern(head))), op, Box::new(rhs)),
                        None => rhs,
                    };
                    return Ok(Stmt::Assign { name: self.intern(head), value, at });
                }
                //Compile-time assertions are erased during lowering; do not let them reach the legacy gate dispatcher
                if matches!(head, "static_assert" | "static_assert_eq" |
                    "static_assert_ne" | "static_assert_live" | "static_assert_distinct") {
                    self.needs_lowering = true;
                }
                let args = self.arguments()?;
                self.expect(TokenKind::Semi, ";")?;
                Ok(Stmt::Call { name: self.intern(head), args, at })
            }
        }
    }
    pub fn parse(mut self) -> Result<Parsed, Diagnostic> {
        let estimated = self.tokens.len().min(2048) / 7;
        let mut statements = Vec::with_capacity(estimated);
        while self.index < self.tokens.len() { statements.push(self.statement()?); }
        Ok(Parsed { statements, needs_lowering: self.needs_lowering })
    }
}

#[cfg(test)]
mod interned_name_tests {
    use super::*;
    use std::rc::Rc;

    #[test]
    fn repeated_identifiers_share_one_allocation() {
        let source = "let q = qubit(); h(q); h(q);";
        let parsed = Parser::new(lex(source).unwrap()).parse().unwrap();
        let Stmt::Let { name: declared, .. } = &parsed.statements[0] else { panic!("expected declaration"); };
        let Stmt::Call { name: first_gate, args: first, .. } = &parsed.statements[1] else { panic!("expected gate"); };
        let Stmt::Call { name: second_gate, args: second, .. } = &parsed.statements[2] else { panic!("expected gate"); };
        let Expr::Var(first_operand) = &first[0] else { panic!("expected operand"); };
        let Expr::Var(second_operand) = &second[0] else { panic!("expected operand"); };
        assert!(Rc::ptr_eq(&first_gate.0, &second_gate.0));
        assert!(Rc::ptr_eq(&declared.0, &first_operand.0));
        assert!(Rc::ptr_eq(&first_operand.0, &second_operand.0));
        assert_ne!(first_gate, declared);
    }

    #[test]
    fn borrowed_tokens_and_owned_tokens_produce_identical_asts() {
        let source = "fn apply(q: &mut Qubit) { h(q); } fn main() { let q = qubit(); apply(&mut q); }";
        let tokens = lex(source).unwrap();
        let owned = Parser::new(tokens.clone()).parse().unwrap();
        let borrowed = Parser::from_slice(&tokens).parse().unwrap();
        assert_eq!(owned.needs_lowering, borrowed.needs_lowering);
        assert_eq!(format!("{:?}", owned.statements), format!("{:?}", borrowed.statements));
    }

    #[test]
    fn ast_names_remain_valid_after_source_is_dropped() {
        let parsed = {
            let source = String::from("let register = qubit(); h(register);");
            Parser::new(lex(&source).unwrap()).parse().unwrap()
        };
        let Stmt::Let { name, .. } = &parsed.statements[0] else { panic!("expected declaration"); };
        let Stmt::Call { args, .. } = &parsed.statements[1] else { panic!("expected call"); };
        let Expr::Var(value) = &args[0] else { panic!("expected variable"); };
        assert_eq!(name.as_str(), "register");
        assert!(Rc::ptr_eq(&name.0, &value.0));
    }
}
