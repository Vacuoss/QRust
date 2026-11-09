//Experimental exact, compile-time Rust scalar and aggregate lowering
use std::collections::HashMap;
use crate::syntax::{self, Diagnostic, Position, Token, TokenKind as K};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum IntTy { I64, U64 }
impl IntTy {
    fn name(self) -> &'static str { match self { Self::I64 => "i64", Self::U64 => "u64" } }
    fn checked(self, x: i128, at: Position) -> Result<i128, Diagnostic> {
        let ok = match self { Self::I64 => x >= i64::MIN as i128 && x <= i64::MAX as i128,
                              Self::U64 => x >= 0 && x <= u64::MAX as i128 };
        if ok { Ok(x) } else { Err(diag(at, format!("{} overflow or invalid sign", self.name()))) }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum Ty { Int(IntTy), Bool, Struct(String), Enum(String) }
#[derive(Clone, Debug, PartialEq, Eq)]
enum Val { Int(IntTy, i128), Bool(bool), Struct(String, HashMap<String, Val>), Enum(String, usize) }
impl Val {
    fn ty(&self) -> Ty { match self { Self::Int(t,_)=>Ty::Int(*t), Self::Bool(_)=>Ty::Bool,
        Self::Struct(n,_)=>Ty::Struct(n.clone()), Self::Enum(n,_)=>Ty::Enum(n.clone()) } }
    fn emit(&self, at: Position) -> Result<String, Diagnostic> {
        match self {
            Self::Int(_, n) => {
                if n.abs() > 9_007_199_254_740_992i128 {
                    return Err(diag(at, "integer cannot be represented exactly by the f64 QPU boundary"));
                }
                Ok(n.to_string())
            }
            Self::Bool(b) => Ok(b.to_string()),
            Self::Enum(_, index) => Ok(index.to_string()),
            Self::Struct(_,_) => Err(diag(at, "struct values are compile-time only; use .field")),
        }
    }
}
#[derive(Clone)]
struct Var { value: Val, mutable: bool }
#[derive(Clone)]
struct StructDef { fields: Vec<(String, Ty)> }
#[derive(Clone)]
struct EnumDef { variants: Vec<String> }
#[derive(Clone)]
struct Edit { begin: usize, end: usize, text: String }
fn diag(at: Position, message: impl Into<String>) -> Diagnostic { Diagnostic { at, message: message.into() } }
fn integer(k: K<'_>, at: Position, ty: IntTy) -> Result<Val, Diagnostic> {
    let K::Number(raw) = k else { return Err(diag(at, "expected integer literal")); };
    if raw.bytes().any(|b| matches!(b, b'.' | b'e' | b'E')) { return Err(diag(at, "integers cannot use fractional/exponent syntax")); }
    let cleaned;
    let raw = if raw.contains('_') {cleaned=raw.replace('_', ""); cleaned.as_str()} else {raw};
    let n = raw.parse::<i128>().map_err(|_| diag(at, "integer literal exceeds compile-time precision"))?;
    Ok(Val::Int(ty, ty.checked(n, at)?))
}

struct Pass<'a> {
    source: &'a str, tokens: Vec<Token<'a>>, lines: Vec<usize>, index: usize,
    edits: Vec<Edit>, structs: HashMap<String, StructDef>, enums: HashMap<String, EnumDef>,
    scopes: Vec<HashMap<String, Var>>,
}
impl<'a> Pass<'a> {
    fn kind(&self) -> Option<K<'a>> { self.tokens.get(self.index).map(|x| x.kind) }
    fn ahead(&self, n: usize) -> Option<K<'a>> { self.tokens.get(self.index+n).map(|x| x.kind) }
    fn pos(&self) -> Position { self.tokens.get(self.index).map(|x| x.at).unwrap_or(Position { line:1, column:1 }) }
    fn begin(&self, i: usize) -> usize { let at = self.tokens[i].at; self.lines[at.line-1]+at.column-1 }
    fn end(&self, i: usize) -> usize {
        let start = self.begin(i);
        let len = match self.tokens[i].kind {
            K::Ident(s) | K::Number(s) => s.len(),
            K::DotDotEq => 3,
            K::DotDot | K::FatArrow | K::EqEq | K::NotEq | K::LessEq | K::GreaterEq |
            K::AndAnd | K::OrOr | K::PlusEq | K::MinusEq | K::StarEq | K::SlashEq | K::PercentEq => 2,
            _ => 1,
        };
        start + len
    }
    fn consume(&mut self, k: K<'a>) -> bool { if self.kind()==Some(k) {self.index+=1; true} else {false} }
    fn expect(&mut self, k: K<'a>, msg: &str) -> Result<(), Diagnostic> {
        if self.consume(k) { Ok(()) } else { Err(diag(self.pos(), msg)) }
    }
    fn ident(&mut self) -> Result<String, Diagnostic> {
        let at = self.pos();
        match self.kind() { Some(K::Ident(s))=>{self.index+=1;Ok(s.to_owned())}, _=>Err(diag(at,"expected identifier")) }
    }
    fn parse_ty(&mut self) -> Result<Ty, Diagnostic> {
        let at = self.pos(); let x = self.ident()?;
        match x.as_str() {
            "i64" => Ok(Ty::Int(IntTy::I64)), "u64" => Ok(Ty::Int(IntTy::U64)),
            "bool" | "Bool" => Ok(Ty::Bool),
            _ if self.structs.contains_key(&x) => Ok(Ty::Struct(x)),
            _ if self.enums.contains_key(&x) => Ok(Ty::Enum(x)),
            _ => Err(diag(at, format!("unknown compile-time Rust type '{x}'"))),
        }
    }
    fn lookup(&self, key: &str) -> Option<&Var> {
        self.scopes.iter().rev().find_map(|scope| scope.get(key))
    }
    fn slot(&mut self, key: &str) -> Option<&mut Var> {
        self.scopes.iter_mut().rev().find_map(|scope| scope.get_mut(key))
    }
    fn declare(&mut self, key: String, var: Var, at: Position) -> Result<(),Diagnostic> {
        let current = self.scopes.last_mut().unwrap();
        if current.contains_key(&key) { return Err(diag(at,format!("duplicate compile-time name '{key}'"))); }
        current.insert(key,var); Ok(())
    }
    fn edit(&mut self, from: usize, to: usize, replacement: String) {
        self.edits.push(Edit {begin: self.begin(from),end: self.end(to-1),text:replacement});
    }
    fn parse_struct(&mut self) -> Result<(), Diagnostic> {
        let start=self.index; let at=self.pos();self.index+=1;
        let n=self.ident()?;
        if self.structs.contains_key(&n) || self.enums.contains_key(&n) {return Err(diag(at,"duplicate Rust type name"));}
        self.expect(K::LBrace,"expected '{' in struct")?;
        let mut fields=Vec::new();
        while !self.consume(K::RBrace) {
            if fields.len()>128 {return Err(diag(self.pos(),"struct exceeds 128 fields"));}
            let field=self.ident()?;
            self.expect(K::Colon,"expected ':' after struct field")?;
            let ty=self.parse_ty()?;
            if !matches!(ty, Ty::Int(_) | Ty::Bool) {
                return Err(diag(at,"struct fields currently support only i64/u64/bool"));
            }
            if fields.iter().any(|(n,_)|n==&field) {return Err(diag(at,"duplicate struct field"));}
            fields.push((field,ty));
            if !self.consume(K::RBrace) {self.expect(K::Comma,"expected ',' or '}'")?;}
            else {break;}
        }
        self.structs.insert(n,StructDef{fields});
        let _=self.consume(K::Semi);
        self.edit(start,self.index,String::new());Ok(())
    }
    fn parse_enum(&mut self) -> Result<(), Diagnostic> {
        let start=self.index;let at=self.pos();self.index+=1;
        let n=self.ident()?;
        if self.structs.contains_key(&n) || self.enums.contains_key(&n) {return Err(diag(at,"duplicate Rust type name"));}
        self.expect(K::LBrace,"expected '{' in enum")?;
        let mut variants=Vec::new();
        while !self.consume(K::RBrace) {
            if variants.len()>128 {return Err(diag(self.pos(),"enum exceeds 128 variants"));}
            let v=self.ident()?;
            if variants.contains(&v) {return Err(diag(at,"duplicate enum variant"));}
            variants.push(v);
            if !self.consume(K::RBrace) {self.expect(K::Comma,"expected ',' or '}'")?;}
            else {break;}
        }
        if variants.is_empty() {return Err(diag(at,"enum must declare at least one variant"));}
        self.enums.insert(n,EnumDef{variants});
        let _=self.consume(K::Semi);
        self.edit(start,self.index,String::new());Ok(())
    }
    fn atom(&mut self, hint: Option<&Ty>) -> Result<Val,Diagnostic> {
        let at=self.pos();
        if self.consume(K::Minus) {
            if let Some(K::Number(raw)) = self.kind() {
                if raw.bytes().any(|b| matches!(b, b'.' | b'e' | b'E')) {
                    return Err(diag(at,"integer literals cannot contain a decimal point or exponent"));
                }
                let cleaned = raw.replace('_', "");
                let magnitude = cleaned.parse::<i128>()
                    .map_err(|_|diag(at,"integer literal exceeds compile-time precision"))?;
                let ty = match hint {Some(Ty::Int(t))=>*t,_=>IntTy::I64};
                let negative = magnitude.checked_neg().ok_or_else(||diag(at,"integer negation overflow"))?;
                self.index+=1;
                return Ok(Val::Int(ty, ty.checked(negative,at)?));
            }
            let result=self.atom(hint)?;
            let Val::Int(t,n)=result else{return Err(diag(at,"negation expects an integer"));};
            let out=n.checked_neg().ok_or_else(||diag(at,"integer negation overflow"))?;
            return Ok(Val::Int(t,t.checked(out,at)?));
        }
        if self.consume(K::LParen) {
            let v=self.expr(hint,0)?;self.expect(K::RParen,"expected ')' ")?;return Ok(v);
        }
        if let Some(K::Number(_))=self.kind() {
            let k=self.kind().unwrap();self.index+=1;
            let ty=match hint {Some(Ty::Int(t))=>*t,_=>IntTy::I64};
            return integer(k,at,ty);
        }
        if let Some(K::Ident(s))=self.kind() {
            self.index+=1;
            if s=="true" || s=="false" {return Ok(Val::Bool(s=="true"));}
            if self.consume(K::Colon) {
                self.expect(K::Colon,"expected '::' in enum variant")?;
                let variant=self.ident()?;
                let Some(def)=self.enums.get(s) else{return Err(diag(at,format!("unknown enum '{s}'")));};
                let Some(index)=def.variants.iter().position(|v|v==&variant) else {return Err(diag(at,"unknown enum variant"));};
                return Ok(Val::Enum(s.into(),index));
            }
            if self.consume(K::LBrace) {
                let Some(def)=self.structs.get(s).cloned() else{return Err(diag(at,format!("unknown struct '{s}'")));};
                let mut fields=HashMap::new();
                while !self.consume(K::RBrace) {
                    let fname=self.ident()?;
                    let Some((_,ty))=def.fields.iter().find(|(n,_)| n==&fname) else {return Err(diag(at,"unknown struct field"));};
                    self.expect(K::Colon,"expected ':' in struct literal")?;
                    let v=self.expr(Some(ty),0)?;
                    if v.ty()!=*ty {return Err(diag(at,"struct field type mismatch"));}
                    if fields.insert(fname,v).is_some() {return Err(diag(at,"duplicate struct initializer field"));}
                    if !self.consume(K::RBrace) {self.expect(K::Comma,"expected ',' or '}'")?;}
                    else {break;}
                }
                if fields.len()!=def.fields.len() {return Err(diag(at,"missing struct initializer fields"));}
                return Ok(Val::Struct(s.into(),fields));
            }
            let Some(var)=self.lookup(s) else{return Err(diag(at,format!("unknown compile-time variable '{s}'")));};
            let mut value=var.value.clone();
            if self.consume(K::Dot) {
                let field=self.ident()?;
                let Val::Struct(_,fields)=value else{return Err(diag(at,"field access requires struct"));};
                value=fields.get(&field).ok_or_else(||diag(at,"unknown field"))?.clone();
            }
            return Ok(value);
        }
        Err(diag(at,"expected compile-time Rust value"))
    }
    fn op(&self) -> Option<(u8,K<'a>)> {
        Some(match self.kind()? {
            K::Plus | K::Minus =>(3,self.kind()?),
            K::Star | K::Slash | K::Percent =>(5,self.kind()?),
            K::EqEq | K::NotEq | K::Less | K::LessEq | K::Greater | K::GreaterEq =>(1,self.kind()?),
            _ =>return None,
        })
    }
    fn expr(&mut self, hint: Option<&Ty>, min_bp:u8)->Result<Val,Diagnostic> {
        let mut lhs=self.atom(hint)?;
        while let Some((bp,op))=self.op() {
            if bp<min_bp {break;}
            let at=self.pos();self.index+=1;
            //Unsuffixed RHS integers inherit the precise integer kind of their left operand; never coerce an exact
            //u64 through f64/i64
            let lhs_ty = lhs.ty();
            let rhs_hint = if matches!(lhs_ty, Ty::Int(_)) {Some(&lhs_ty)} else {hint};
            let rhs=self.expr(rhs_hint,bp+1)?;
            lhs=Self::combine(lhs,op,rhs,at)?;
        }
        Ok(lhs)
    }
    fn combine(left:Val,op:K<'a>,right:Val,at:Position)->Result<Val,Diagnostic> {
        if op==K::EqEq || op==K::NotEq {
            if left.ty()!=right.ty() {return Err(diag(at,"equality requires matching types"));}
            return Ok(Val::Bool((left==right)==(op==K::EqEq)));
        }
        let (Val::Int(t,l),Val::Int(rt,r))=(left,right) else{return Err(diag(at,"integer operator expects integers"));};
        if t!=rt {return Err(diag(at,"cannot mix i64 and u64 without explicit conversion"));}
        let n=match op {
            K::Plus =>l.checked_add(r), K::Minus =>l.checked_sub(r),K::Star=>l.checked_mul(r),
            K::Slash=>l.checked_div(r),K::Percent=>l.checked_rem(r),
            K::Less=>return Ok(Val::Bool(l<r)),K::LessEq=>return Ok(Val::Bool(l<=r)),
            K::Greater=>return Ok(Val::Bool(l>r)),K::GreaterEq=>return Ok(Val::Bool(l>=r)),
            _ =>return Err(diag(at,"unsupported integer operator")),
        }.ok_or_else(||diag(at,"integer overflow or division by zero"))?;
        Ok(Val::Int(t,t.checked(n,at)?))
    }
    fn typed_let(&mut self)->Result<(),Diagnostic> {
        let start=self.index;let at=self.pos();
        let is_const=self.consume(K::Ident("const"));
        if !is_const {self.expect(K::Ident("let"),"expected let")?;}
        let mutable=self.consume(K::Ident("mut"));
        if mutable && is_const {return Err(diag(at,"const cannot be mutable"));}
        let n=self.ident()?;
        self.expect(K::Colon,"expected type annotation")?;
        let ty=self.parse_ty()?;
        self.expect(K::Equal,"expected '='")?;
        let val=self.expr(Some(&ty),0)?;
        if val.ty()!=ty {return Err(diag(at,"typed initializer has wrong type"));}
        self.expect(K::Semi,"expected ';'")?;
        self.declare(n,Var{value:val,mutable},at)?;
        self.edit(start,self.index,String::new());Ok(())
    }
    fn exact_assertion(&mut self)->Result<bool,Diagnostic> {
        let Some(K::Ident(op @ ("static_assert_eq" | "static_assert_ne")))=self.kind()
            else {return Ok(false);};
        if self.ahead(1)!=Some(K::LParen) {return Ok(false);}
        let mut end=self.index+2;
        let mut has_exact=false;
        while end<self.tokens.len() && self.tokens[end].kind!=K::Semi {
            if let K::Ident(n)=self.tokens[end].kind {
                has_exact |= self.lookup(n).is_some();
            }
            end+=1;
        }
        if !has_exact {return Ok(false);}
        let start=self.index;let at=self.pos();
        self.index+=1;
        self.expect(K::LParen,"expected '('")?;
        let left=self.expr(None,0)?;
        self.expect(K::Comma,"expected ','")?;
        let ty=left.ty();
        let right=self.expr(Some(&ty),0)?;
        self.expect(K::RParen,"expected ')'")?;
        self.expect(K::Semi,"expected ';'")?;
        if left.ty()!=right.ty() {return Err(diag(at,"exact assertion compares different types"));}
        if matches!(&left,Val::Struct(_, _)) {return Err(diag(at,"struct equality requires PartialEq (not yet supported)"));}
        let success=(left==right)==(op=="static_assert_eq");
        if !success {return Err(diag(at,"exact integer/enum static assertion failed"));}
        self.edit(start,self.index,String::new());Ok(true)
    }
    fn assignment(&mut self)->Result<bool,Diagnostic> {
        let start=self.index;let at=self.pos();
        let Some(K::Ident(n))=self.kind() else{return Ok(false);};
        let key=n.to_owned();
        let op=match self.ahead(1) {
            Some(K::Equal | K::PlusEq | K::MinusEq | K::StarEq | K::SlashEq | K::PercentEq)=>self.ahead(1).unwrap(),
            _=>return Ok(false),
        };
        let Some(var)=self.lookup(&key).cloned() else{return Ok(false);};
        if !var.mutable {return Err(diag(at,"cannot assign to immutable compile-time variable"));}
        self.index+=2;
        let rhs=self.expr(Some(&var.value.ty()),0)?;
        let value=if op==K::Equal {rhs} else {
            let binary=match op {K::PlusEq=>K::Plus,K::MinusEq=>K::Minus,K::StarEq=>K::Star,
                K::SlashEq=>K::Slash,K::PercentEq=>K::Percent,_=>unreachable!()};
            Self::combine(var.value.clone(),binary,rhs,at)?
        };
        if value.ty()!=var.value.ty() {return Err(diag(at,"assignment changes compile-time type"));}
        self.expect(K::Semi,"expected ';'")?;
        self.slot(&key).unwrap().value=value;
        self.edit(start,self.index,String::new());Ok(true)
    }
    fn check_enum_match(&mut self)->Result<(), Diagnostic> {
        let Some(K::Ident(subject))=self.ahead(1) else {return Ok(());};
        let Some(Var {value: Val::Enum(enum_ty, _), ..})=self.lookup(subject) else {return Ok(());};
        if self.ahead(2)!=Some(K::LBrace) {return Ok(());}
        let enum_ty=enum_ty.clone();
        let variants=self.enums.get(&enum_ty).unwrap().variants.clone();
        let mut used=std::collections::HashSet::new();
        let mut wildcard=false;
        let mut depth=0usize;
        let mut i=self.index+2;
        while i<self.tokens.len() {
            match self.tokens[i].kind {
                K::LBrace =>depth+=1,
                K::RBrace => {
                    depth-=1;
                    if depth==0 {break;}
                }
                K::Ident("_") if depth==1 && self.tokens.get(i+1).map(|t|t.kind)==Some(K::FatArrow) => {
                    wildcard=true;
                }
                K::Ident(pattern) if depth==1 &&
                    self.tokens.get(i+1).map(|t|t.kind)==Some(K::Colon) &&
                    self.tokens.get(i+2).map(|t|t.kind)==Some(K::Colon) &&
                    matches!(self.tokens.get(i+3).map(|t|t.kind),Some(K::Ident(_))) &&
                    self.tokens.get(i+4).map(|t|t.kind)==Some(K::FatArrow) => {
                    if pattern != enum_ty {return Err(diag(self.tokens[i].at,
                        "enum match arm uses a variant of another enum type"));}
                    if let Some(K::Ident(variant))=self.tokens.get(i+3).map(|t|t.kind) {
                        if !variants.iter().any(|name|name==variant) {return Err(diag(self.tokens[i].at,"unknown enum match variant"));}
                        if !used.insert(variant.to_owned()) {return Err(diag(self.tokens[i].at,"duplicate enum match variant"));}
                    }
                }
                K::Number(_) if depth==1 && self.tokens.get(i+1).map(|t|t.kind)==Some(K::FatArrow) => {
                    return Err(diag(self.tokens[i].at,"enum match patterns require typed Enum::Variant"));
                }
                _=>{}
            }
            i+=1;
        }
        if i==self.tokens.len() {return Err(diag(self.pos(),"unclosed enum match"));}
        if !wildcard && used.len()!=variants.len() {
            return Err(diag(self.pos(),"nonexhaustive enum match: add missing variants or '_'"));
        }
        if !wildcard {
            let point=self.begin(i);
            let last=self.source[..point].trim_end().as_bytes().last().copied();
            let suffix=if last==Some(b',') {" _ => {}, "} else {", _ => {} "};
            self.edits.push(Edit {begin:point,end:point,text:suffix.to_owned()});
        }
        Ok(())
    }
    fn run(mut self)->Result<String,Diagnostic> {
        while self.index<self.tokens.len() {
            let from=self.index;
            match self.kind() {
                Some(K::Ident("struct")) if self.scopes.len()==1 => {self.parse_struct()?;continue;},
                Some(K::Ident("enum")) if self.scopes.len()==1 => {self.parse_enum()?;continue;},
                Some(K::Ident("let" | "const")) => {
                    let typed=self.ahead(1)==Some(K::Ident("mut"));
                    let colon=if typed {3}else{2};
                    if self.ahead(colon)==Some(K::Colon) {
                        let known=match self.ahead(colon+1) {
                            Some(K::Ident(s)) =>s=="i64"||s=="u64"||self.structs.contains_key(s)||self.enums.contains_key(s),
                            _=>false,
                        };
                        if known {self.typed_let()?;continue;}
                    }
                }
                Some(K::Ident("match")) => {self.check_enum_match()?;},
                Some(K::LBrace) => {self.scopes.push(HashMap::new());},
                Some(K::RBrace) if self.scopes.len()>1 => {self.scopes.pop();},
                Some(K::Ident(_)) => {
                    if self.exact_assertion()? {continue;}
                    if self.assignment()? {continue;}
                    if let Some(K::Ident(prefix))=self.kind() {
                        if self.ahead(1)==Some(K::Dot) {
                            if let Some(K::Ident(field))=self.ahead(2) {
                                if let Some(var)=self.lookup(prefix) {
                                    let Val::Struct(_,values)=&var.value else {return Err(diag(self.pos(),"field access on non-struct"));};
                                    let val=values.get(field).ok_or_else(||diag(self.pos(),"unknown struct field"))?;
                                    let output=val.emit(self.pos())?;
                                    self.index+=3;self.edit(from,self.index,output);continue;
                                }
                            }
                        }
                        if self.ahead(1)==Some(K::Colon) && self.ahead(2)==Some(K::Colon) {
                            if let Some(K::Ident(variant))=self.ahead(3) {
                                if let Some(def)=self.enums.get(prefix) {
                                    let index=def.variants.iter().position(|v|v==variant)
                                        .ok_or_else(||diag(self.pos(),"unknown enum variant"))?;
                                    if self.ahead(4)!=Some(K::FatArrow) {
                                        return Err(diag(self.pos(),"enum variant cannot be used as a numeric value"));
                                    }
                                    self.index+=4;self.edit(from,self.index,index.to_string());continue;
                                }
                            }
                        }
                        if let Some(var)=self.lookup(prefix) {
                            if matches!(&var.value, Val::Enum(_, _)) &&
                                !(from>0 && matches!(self.tokens[from-1].kind,K::Ident("match"))) {
                                return Err(diag(self.pos(),"enum variable is only valid in compile-time match/assertions"));
                            }
                            let val=var.value.emit(self.pos())?;
                            self.index+=1;self.edit(from,self.index,val);continue;
                        }
                    }
                }
                _=>{}
            }
            self.index+=1;
        }
        self.edits.sort_by_key(|e|e.begin);
        let mut out=String::with_capacity(self.source.len());let mut cursor=0;
        for edit in self.edits {
            if edit.begin<cursor {return Err(diag(Position {line:1,column:1},"overlapping static replacements"));}
            out.push_str(&self.source[cursor..edit.begin]);out.push_str(&edit.text);cursor=edit.end;
        }
        out.push_str(&self.source[cursor..]);Ok(out)
    }
}

pub fn lower(source:&str)->Result<Option<String>,Diagnostic> {
    if !source.contains("i64") && !source.contains("u64") && !source.contains("struct ") && !source.contains("enum ") {
        return Ok(None);
    }
    let tokens=syntax::lex(source)?;
    let mut lines=vec![0];
    for (i,b) in source.bytes().enumerate() {if b==b'\n' {lines.push(i+1);}}
    let pass=Pass {source,tokens,lines,index:0,edits:Vec::new(),structs:HashMap::new(),
        enums:HashMap::new(),scopes:vec![HashMap::new()]};
    Ok(Some(pass.run()?))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn signed_minimum_is_exact() {
        assert!(lower("let n: i64 = -9223372036854775808;").is_ok());
        assert!(lower("let n: i64 = -9223372036854775809;").is_err());
    }
    #[test] fn exact_i64_and_u64_boundaries() {
        let src="let a: i64 = 9007199254740993; let b: i64 = a + 2; let c: u64 = 18446744073709551615; static_assert_eq(c,18446744073709551615);";
        let lowered=lower(src).unwrap().unwrap();
        assert!(!lowered.contains("9007199254740993"));
    }
    #[test] fn enum_match_type_and_exhaustiveness() {
        let src="enum A{X,Y} enum B{X,Y} fn main(){let a:A=A::X;match a{A::X=>{x(qubit());},A::Y=>{h(qubit());}}}";
        let lowered=lower(src).unwrap().unwrap();
        assert!(lowered.contains("_ => {}"));
        assert!(lower("enum A{X,Y} enum B{X,Y} fn main(){let a:A=A::X;match a{B::X=>{},_=>{}}}").is_err());
        assert!(lower("enum A{X,Y} fn main(){let a:A=A::X;match a{A::X=>{}}}").is_err());
    }
    #[test] fn overflow_rejected() {
        assert!(lower("let a: i64 = 9223372036854775807 + 1;").is_err());
        assert!(lower("let a: u64 = 0 - 1;").is_err());
    }
    #[test] fn structs_and_enums_are_checked() {
        let src="struct Pulse { angle: i64, enabled: bool } enum Axis { X, Y } fn main(){let p: Pulse = Pulse {angle: 4, enabled:true};let axis: Axis = Axis::Y;let q=qubit();rz(p.angle,q);match axis {Axis::Y => {h(q);}, _ => {x(q);}}}";
        let lowered=lower(src).unwrap().unwrap();
        assert!(lowered.contains("rz(4,q)"));
        assert!(lowered.contains("match 1"));
    }
    #[test] fn huge_integer_cannot_be_silently_converted_to_qasm() {
        assert!(lower("let x: i64 = 9007199254740993; fn main(){let q=qubit();rz(x,q);}").is_err());
    }
}
