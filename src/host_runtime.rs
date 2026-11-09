//QRust host execution preview: bounded classical interpreter sharing the checked local quantum engine
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;
use crate::syntax::{self,Token,TokenKind as K};
use crate::sema;
#[path = "quantum_backend.rs"]
mod quantum_backend;
pub use quantum_backend::BackendKind;
use quantum_backend::QuantumBackend;
#[path = "host_static.rs"]
mod host_static;

const MAX_STEPS:u64=2_000_000;
const MAX_DEPTH:usize=64;
const MAX_SOURCE:usize=1_000_000;
const MAX_SLOTS:usize=2_000_000;

#[derive(Clone, Debug)]
enum Expr {
    Int(i64),Float(f64),Bool(bool),Text(String),Var(String),
    Unary(K<'static>,Box<Expr>), Binary(K<'static>,Box<Expr>,Box<Expr>),
    Call(String,Vec<Expr>), Borrow{source:String,mutable:bool,via_ref:bool},
    Deref(String),
}
#[derive(Clone,Debug)]
enum Stmt {
    Let{name:String,mutable:bool,declared:Option<String>,value:Expr},
    Assign{name:String,operator:K<'static>,value:Expr},
    Expr(Expr), Block(Vec<Stmt>), If{cond:Expr,then_body:Vec<Stmt>,else_body:Vec<Stmt>},
    While{cond:Expr,body:Vec<Stmt>},For{name:String,from:Expr,to:Expr,inclusive:bool,body:Vec<Stmt>},
    Break,Continue,Return(Option<Expr>),
}
#[derive(Clone,Debug)]
struct Param {name:String,ty:String,mutable:bool,lifetime:Option<String>}
#[derive(Clone,Debug)]
struct Function {params:Vec<Param>,ret:String,body:Vec<Stmt>,return_from:Option<String>}
#[derive(Clone,Debug)]
struct Program {main:Vec<Stmt>,functions:HashMap<String,Function>}

//Conservative lexical block liveness
fn uses_expr(e:&Expr,out:&mut HashSet<String>){
    match e {
        Expr::Var(s)|Expr::Deref(s)=>{out.insert(s.clone());},
        Expr::Borrow{source,..}=>{out.insert(source.clone());},
        Expr::Unary(_,a)=>uses_expr(a,out),
        Expr::Binary(_,a,b)=>{uses_expr(a,out);uses_expr(b,out);},
        Expr::Call(_,args)=>for a in args{uses_expr(a,out)},
        Expr::Int(_)|Expr::Float(_)|Expr::Bool(_)|Expr::Text(_)=>{},
    }
}
fn uses_stmts(stmts:&[Stmt],out:&mut HashSet<String>){
    for s in stmts {match s {
        Stmt::Let{value,..}|Stmt::Expr(value)=>uses_expr(value,out),
        Stmt::Assign{name,value,..}=>{out.insert(name.clone());uses_expr(value,out);},
        Stmt::Block(body)=>uses_stmts(body,out),
        Stmt::If{cond,then_body,else_body}=>{
            uses_expr(cond,out);uses_stmts(then_body,out);uses_stmts(else_body,out);
        },
        Stmt::While{cond,body}=>{uses_expr(cond,out);uses_stmts(body,out);},
        Stmt::For{from,to,body,..}=>{uses_expr(from,out);uses_expr(to,out);uses_stmts(body,out);},
        Stmt::Return(expr)=>{if let Some(e)=expr{uses_expr(e,out);}},
        Stmt::Break|Stmt::Continue=>{},
    }}
}
fn live_suffix(stmts:&[Stmt])->Vec<HashSet<String>>{
    let mut after=vec![HashSet::new();stmts.len()];
    let mut live=HashSet::new();
    for i in (0..stmts.len()).rev(){
        after[i]=live.clone();
        uses_stmts(std::slice::from_ref(&stmts[i]),&mut live);
    }
    after
}

struct Parser<'a>{tokens:Vec<Token<'a>>,i:usize}
impl<'a> Parser<'a>{
    fn peek(&self)->Option<K<'a>>{self.tokens.get(self.i).map(|t|t.kind)}
    fn at(&self)->String{match self.tokens.get(self.i){Some(t)=>format!("{}:{}",t.at.line,t.at.column),None=>"end of file".into()}}
    fn error(&self,s:&str)->String{format!("{}: {s}",self.at())}
    fn eat(&mut self,k:K<'a>)->bool{if self.peek()==Some(k){self.i+=1;true}else{false}}
    fn need(&mut self,k:K<'a>)->Result<(),String>{if self.eat(k){Ok(())}else{Err(self.error(&format!("expected {k:?}")))}}
    fn ident(&mut self)->Result<String,String>{match self.peek(){Some(K::Ident(x))=>{self.i+=1;Ok(x.to_owned())},_=>Err(self.error("expected identifier"))}}
    fn block(&mut self,depth:usize)->Result<Vec<Stmt>,String>{
        if depth>MAX_DEPTH{return Err(self.error("nesting limit exceeded"));}
        self.need(K::LBrace)?;
        let mut out=Vec::new();
        while !self.eat(K::RBrace){
            if self.peek().is_none(){return Err(self.error("unclosed block"));}
            out.push(self.statement(depth+1)?);
        }
        Ok(out)
    }
    fn statement(&mut self,depth:usize)->Result<Stmt,String>{
        if depth>MAX_DEPTH{return Err(self.error("nesting limit exceeded"));}
        if self.eat(K::Ident("let")) {
            let mutable=self.eat(K::Ident("mut"));
            let name=self.ident()?;
            let declared=if self.eat(K::Colon){Some(self.ident()?)}else{None};
            self.need(K::Equal)?;
            let value=self.expr(0,depth+1)?;
            self.need(K::Semi)?;
            return Ok(Stmt::Let{name,mutable,declared,value});
        }
        if self.eat(K::Ident("if")) {
            let cond=self.expr(0,depth+1)?;
            let then_body=self.block(depth+1)?;
            let else_body=if self.eat(K::Ident("else")) {
                if self.peek()==Some(K::Ident("if")){vec![self.statement(depth+1)?]}else{self.block(depth+1)?}
            }else{Vec::new()};
            return Ok(Stmt::If{cond,then_body,else_body});
        }
        if self.eat(K::Ident("while")) {
            let cond=self.expr(0,depth+1)?;
            let body=self.block(depth+1)?;
            return Ok(Stmt::While{cond,body});
        }
        if self.eat(K::Ident("for")) {
            let name=self.ident()?;self.need(K::Ident("in"))?;
            let from=self.expr(0,depth+1)?;
            let inclusive=if self.eat(K::DotDotEq){true}else{self.need(K::DotDot)?;false};
            let to=self.expr(0,depth+1)?;let body=self.block(depth+1)?;
            return Ok(Stmt::For{name,from,to,inclusive,body});
        }
        if self.eat(K::Ident("break")){self.need(K::Semi)?;return Ok(Stmt::Break);}
        if self.eat(K::Ident("continue")){self.need(K::Semi)?;return Ok(Stmt::Continue);}
        if self.eat(K::Ident("return")){
            let value=if self.peek()==Some(K::Semi){None}else{Some(self.expr(0,depth+1)?)};
            self.need(K::Semi)?;return Ok(Stmt::Return(value));
        }
        if self.peek()==Some(K::LBrace){return Ok(Stmt::Block(self.block(depth+1)?));}
        if let Some(K::Ident(name))=self.peek(){
            let op=self.tokens.get(self.i+1).map(|t|t.kind);
            if let Some(operator @ (K::Equal|K::PlusEq|K::MinusEq|K::StarEq|K::SlashEq|K::PercentEq))=op {
                self.i+=2;
                let value=self.expr(0,depth+1)?;self.need(K::Semi)?;
                return Ok(Stmt::Assign{name:name.to_owned(),operator:cast_op(operator),value});
            }
        }
        let expr=self.expr(0,depth+1)?;
        self.need(K::Semi)?;Ok(Stmt::Expr(expr))
    }
    fn expr(&mut self,min:u8,depth:usize)->Result<Expr,String>{
        if depth>MAX_DEPTH{return Err(self.error("expression nesting limit exceeded"));}
        let mut left=if self.eat(K::Minus){Expr::Unary(K::Minus,Box::new(self.expr(7,depth+1)?))}
        else if self.eat(K::Bang){Expr::Unary(K::Bang,Box::new(self.expr(7,depth+1)?))}
        else if self.eat(K::Star){Expr::Deref(self.ident()?)}
        else if self.eat(K::Amp){
            let mutable=self.eat(K::Ident("mut"));
            let via_ref=self.eat(K::Star);
            Expr::Borrow{source:self.ident()?,mutable,via_ref}
        }
        else if self.eat(K::LParen){let e=self.expr(0,depth+1)?;self.need(K::RParen)?;e}
        else if let Some(K::Number(x))=self.peek(){
            self.i+=1;let raw=x.replace('_',"");
            if raw.contains('.')||raw.contains('e')||raw.contains('E'){
                let n=raw.parse::<f64>().map_err(|_|self.error("invalid floating literal"))?;
                if !n.is_finite(){return Err(self.error("non-finite float"));}Expr::Float(n)
            }else{Expr::Int(raw.parse::<i64>().map_err(|_|self.error("integer literal out of range"))?)}
        }
        else if let Some(K::StringLit(raw))=self.peek(){self.i+=1;Expr::Text(unescape(raw)?)}
        else if self.eat(K::Ident("true")){Expr::Bool(true)}
        else if self.eat(K::Ident("false")){Expr::Bool(false)}
        else if let Some(K::Ident(_))=self.peek(){
            let name=self.ident()?;
            let _macro=self.eat(K::Bang);
            if self.eat(K::LParen){
                let mut args=Vec::new();
                if !self.eat(K::RParen){loop{args.push(self.expr(0,depth+1)?);
                    if self.eat(K::RParen){break;}self.need(K::Comma)?;
                }}
                Expr::Call(name,args)
            } else if _macro {return Err(self.error("expected '(' after macro call"));}
            else {Expr::Var(name)}
        }else{return Err(self.error("expected expression"));};
        while let Some(op)=self.peek(){
            let prec=match op{K::OrOr=>1,K::AndAnd=>2,K::EqEq|K::NotEq=>3,
                K::Less|K::LessEq|K::Greater|K::GreaterEq=>4,
                K::Plus|K::Minus=>5,K::Star|K::Slash|K::Percent=>6,_=>0};
            if prec==0||prec<min{break;}
            self.i+=1;
            let right=self.expr(prec+1,depth+1)?;
            left=Expr::Binary(cast_op(op),Box::new(left),Box::new(right));
        }
        Ok(left)
    }
    fn signature_type(&mut self)->Result<(String,Option<String>,bool),String>{
        if self.eat(K::Amp){
            let life=if let Some(K::Lifetime(x))=self.peek(){self.i+=1;Some(x.to_owned())}else{None};
            let mutable=self.eat(K::Ident("mut"));
            let inner=self.ident()?;
            if inner!="Qubit" {return Err(self.error("preview function references currently require Qubit"));}
            return Ok(("Reference".into(),life,mutable));
        }
        Ok((self.ident()?,None,false))
    }
    fn parse_program(mut self)->Result<Program,String>{
        let mut main=None;let mut functions=HashMap::new();let mut standalone=Vec::new();
        while self.peek().is_some(){
            if !self.eat(K::Ident("fn")) {
                if main.is_some() || !functions.is_empty(){return Err(self.error("top-level statement after function definition"));}
                standalone.push(self.statement(0)?);continue;
            }
            let name=self.ident()?;
            let mut declared_lifetime=None;
            if self.eat(K::Less){
                let Some(K::Lifetime(x))=self.peek() else{return Err(self.error("expected named lifetime"));};
                declared_lifetime=Some(x.to_owned());self.i+=1;self.need(K::Greater)?;
            }
            self.need(K::LParen)?;
            let mut params=Vec::new();
            if !self.eat(K::RParen){loop{
                let mutable=self.eat(K::Ident("mut"));let pname=self.ident()?;self.need(K::Colon)?;
                let (ty,life,exclusive)=self.signature_type()?;
                if let Some(ref l)=life {if declared_lifetime.as_ref()!=Some(l){return Err(self.error("undeclared parameter lifetime"));}}
                if params.iter().any(|p:&Param|p.name==pname){return Err(self.error("duplicate parameter"));}
                params.push(Param{name:pname,ty,mutable:mutable||exclusive,lifetime:life});
                if self.eat(K::RParen){break;}self.need(K::Comma)?;
            }}
            let (ret,return_life,_)=if self.eat(K::Minus){self.need(K::Greater)?;self.signature_type()?}
                else{("Unit".into(),None,false)};
            let body=self.block(0)?;
            if name=="main"{
                if !params.is_empty()||ret!="Unit"||main.is_some(){return Err(self.error("fn main must have no parameters and return Unit"));}
                main=Some(body);continue;
            }
            if functions.len()>=64{return Err(self.error("function limit exceeded"));}
            if functions.contains_key(&name){return Err(self.error("duplicate function"));}
            let return_from=if ret=="Reference"{
                let lifetime=return_life.ok_or_else(||self.error("reference return requires explicit lifetime 'a"))?;
                if declared_lifetime.as_ref()!=Some(&lifetime){return Err(self.error("return lifetime is not declared"));}
                let candidates=params.iter().filter(|p|p.ty=="Reference"&&p.lifetime.as_deref()==Some(lifetime.as_str())).collect::<Vec<_>>();
                if candidates.len()!=1{return Err(self.error("reference return lifetime must map to exactly one reference parameter"));}
                let name=candidates[0].name.clone();
                if contains_shadow(&body,&name) || !safe_reference_return(&body,&name){
                    return Err(self.error("reference must return the original, unshadowed lifetime parameter"));
                }
                Some(name)
            }else{None};
            functions.insert(name,Function{params,ret,body,return_from});
        }
        if main.is_some()&&!standalone.is_empty(){return Err("top-level code cannot accompany fn main".into());}
        Ok(Program{main:main.unwrap_or(standalone),functions})
    }
    #[allow(dead_code)]
    fn parse(self)->Result<Vec<Stmt>,String>{Ok(self.parse_program()?.main)}
}
fn contains_shadow(stmts:&[Stmt],parameter:&str)->bool{
    stmts.iter().any(|s|match s{
        Stmt::Let{name,..}|Stmt::For{name,..} if name==parameter=>true,
        Stmt::Block(body)|Stmt::While{body,..}|Stmt::For{body,..}=>contains_shadow(body,parameter),
        Stmt::If{then_body,else_body,..}=>contains_shadow(then_body,parameter)||contains_shadow(else_body,parameter),
        _=>false,
    })
}
fn safe_reference_return(stmts:&[Stmt],parameter:&str)->bool{
    let mut has_return=false;
    for stmt in stmts {match stmt {
        Stmt::Return(Some(Expr::Var(name))) if name==parameter=>has_return=true,
        Stmt::Return(_)=>return false,
        Stmt::Block(body)=>{if !safe_reference_return(body,parameter){return false;}has_return=true;},
        Stmt::If{then_body,else_body,..}=>{
            if !safe_reference_return(then_body,parameter)||!safe_reference_return(else_body,parameter){return false;}
            has_return=true;
        },
        Stmt::While{body,..}|Stmt::For{body,..}=>{
            if body.iter().any(|s|matches!(s,Stmt::Return(_))){return false;}
        },
        _=>{},
    }}
    has_return

}
fn cast_op(k:K<'_>)->K<'static>{match k{
    K::Equal=>K::Equal,K::PlusEq=>K::PlusEq,K::MinusEq=>K::MinusEq,K::StarEq=>K::StarEq,
    K::SlashEq=>K::SlashEq,K::PercentEq=>K::PercentEq,K::Minus=>K::Minus,K::Bang=>K::Bang,
    K::OrOr=>K::OrOr,K::AndAnd=>K::AndAnd,K::EqEq=>K::EqEq,K::NotEq=>K::NotEq,
    K::Less=>K::Less,K::LessEq=>K::LessEq,K::Greater=>K::Greater,K::GreaterEq=>K::GreaterEq,
    K::Plus=>K::Plus,K::Star=>K::Star,K::Slash=>K::Slash,K::Percent=>K::Percent,
    _=>unreachable!(),
}}
fn unescape(raw:&str)->Result<String,String>{
    let mut out=String::with_capacity(raw.len());let mut chars=raw.chars();
    while let Some(c)=chars.next(){if c=='\\'{match chars.next(){Some('n')=>out.push('\n'),Some('t')=>out.push('\t'),Some('\\')=>out.push('\\'),Some('"')=>out.push('"'),_=>return Err("unsupported string escape".into())}}else{out.push(c);}}
    Ok(out)
}

#[derive(Clone,Debug,PartialEq)]
enum Value {Int(i64),Float(f64),Bool(bool),Text(String),Qubit(usize),Ref(usize),Unit,Moved}
impl Value {
    fn ty(&self)->&'static str{match self{Self::Int(_)=>"i64",Self::Float(_)=>"Float",Self::Bool(_)=>"bool",
        Self::Text(_)=>"String",Self::Qubit(_)=>"Qubit",Self::Ref(_)=>"Reference",Self::Unit=>"Unit",Self::Moved=>"Moved"}}
    fn display(&self)->String{match self{Self::Int(n)=>n.to_string(),Self::Float(x)=>x.to_string(),Self::Bool(b)=>b.to_string(),
        Self::Text(t)=>t.clone(),Self::Qubit(q)=>format!("Qubit({q})"),Self::Ref(_)=>"<reference>".into(),Self::Unit=>"()".into(),Self::Moved=>"<moved>".into()}}
    fn truth(&self)->Result<bool,String>{match self{Self::Bool(x)=>Ok(*x),Self::Int(0)=>Ok(false),Self::Int(1)=>Ok(true),
        _=>Err(format!("expected bool or measured bit, got {}",self.ty()))}}
    fn integer(&self)->Result<i64,String>{match self{Self::Int(x)=>Ok(*x),_=>Err(format!("expected integer, got {}",self.ty()))}}
    fn number(&self)->Result<f64,String>{match self{Self::Float(x)=>Ok(*x),Self::Int(x)=>Ok(*x as f64),_=>Err(format!("expected number, got {}",self.ty()))}}
}
#[derive(Clone,Debug)]
struct Slot{name:String,mutable:bool,ty:String,value:Value}
#[derive(Clone,Debug)]
struct Loan{target:usize,mutable:bool,parent:Option<usize>,alive:bool}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]enum Flow{Normal,Break,Continue,Return}

pub trait Console {
    fn read_line(&mut self)->Result<String,String>;
    fn write(&mut self,text:&str);
}
pub struct InputConsole<'a> {
    fallback: &'a mut dyn Console,
    pending: VecDeque<String>,
}
impl<'a> InputConsole<'a> {
    pub fn new(fallback: &'a mut dyn Console, inputs: Vec<String>) -> Self {
        Self { fallback, pending: inputs.into_iter().collect() }
    }
}
impl Console for InputConsole<'_> {
    fn read_line(&mut self) -> Result<String, String> {
        match self.pending.pop_front() {
            Some(line) => Ok(line),
            None => self.fallback.read_line(),
        }
    }
    fn write(&mut self, text: &str) { self.fallback.write(text); }
}

fn parse_input_i64(raw: &str) -> Result<i64, String> {
    //UTF-8 BOM is sometimes added by Windows text pipelines. Do not silently discard arbitrary nonnumeric
    //characters or overflow
    let normalized = raw.trim().trim_start_matches('\u{feff}').trim();
    normalized.parse::<i64>().map_err(|_| {
        let reason = if raw.is_empty() { "stdin returned EOF" }
            else { "received data is not a valid signed decimal integer" };
        format!("input expects a signed integer (i64): {reason}; received {} byte(s)", raw.len())
    })
}

pub struct StdConsole;
impl Console for StdConsole{
    fn read_line(&mut self)->Result<String,String>{
        use std::io::{self,Write};
        io::stdout().flush().map_err(|e|e.to_string())?;
        let mut data=String::new();io::stdin().read_line(&mut data).map_err(|e|e.to_string())?;
        if std::env::var_os("QRUST_DEBUG_STDIN").is_some() {
            //Opt-in raw-byte diagnostics. Never print user input by default
            let prefix = data.as_bytes().iter().take(32)
                .map(|b| format!("{b:02X}")).collect::<Vec<_>>().join(" ");
            eprintln!("QRust stdin debug: {} byte(s), hex prefix: {prefix}", data.len());
        }
        Ok(data)
    }
    fn write(&mut self,text:&str){print!("{text}");}
}

#[derive(Debug)]
pub struct RunStats{pub executed_steps:u64,pub allocated_qubits:usize,pub measurements:usize}
struct Vm<'a>{
    console:&'a mut dyn Console,quantum:Box<dyn QuantumBackend>,
    slots:Vec<Slot>,ref_slots:Vec<usize>,loans:Vec<Loan>,scopes:Vec<usize>,
    bindings:HashMap<String,Vec<usize>>,active_loans:HashMap<usize,Vec<usize>>,steps:u64,
    allocated_qubits:usize,measurements:usize,
    functions:HashMap<String,Rc<Function>>,return_value:Option<Value>,call_depth:usize,
    live_cache:HashMap<usize,Vec<HashSet<String>>>,
    continuation_refs:Vec<HashSet<usize>>,
}
impl<'a> Vm<'a>{
    #[cfg(test)]
    fn new(console:&'a mut dyn Console,seed:u64)->Self{Self::with_backend(console,seed,BackendKind::Local).expect("local backend is built in")}
    fn with_backend(console:&'a mut dyn Console,seed:u64,backend:BackendKind)->Result<Self,String>{Ok(Self{console,quantum:quantum_backend::create(backend,seed)?,
        slots:Vec::new(),ref_slots:Vec::new(),loans:Vec::new(),scopes:Vec::new(),bindings:HashMap::new(),active_loans:HashMap::new(),steps:0,allocated_qubits:0,measurements:0,functions:HashMap::new(),return_value:None,call_depth:0,live_cache:HashMap::new(),continuation_refs:Vec::new()})}
    fn step(&mut self)->Result<(),String>{self.steps+=1;if self.steps>MAX_STEPS{Err("host runtime instruction limit exceeded".into())}else{Ok(())}}
    fn lookup(&self,name:&str)->Result<usize,String>{self.bindings.get(name).and_then(|ids|ids.last().copied())
        .ok_or_else(||format!("undefined variable '{name}'"))}
    fn begin_scope(&mut self){self.scopes.push(self.slots.len());}
    fn end_scope(&mut self)->Result<(),String>{
        let start=self.scopes.pop().ok_or("unbalanced host scope")?;
        for idx in (start..self.slots.len()).rev(){
            if let Value::Ref(id)=self.slots[idx].value{self.release_loan(id)?;}
        }
        for idx in (start..self.slots.len()).rev(){
            //A pure state-vector backend cannot trace out a still-live entangled qubit as if it were an ordinary
            //Rust value
            if !self.scopes.is_empty() && matches!(&self.slots[idx].value,Value::Qubit(_)){
                return Err(format!("quantum-aware Drop: live Qubit '{}' requires measure() or return to caller",self.slots[idx].name));
            }
            if self.active_loans.get(&idx).is_some_and(|ids|!ids.is_empty()){
                return Err(format!("borrowed value '{}' outlives storage",self.slots[idx].name));
            }
            self.slots[idx].value=Value::Moved;
            let name=&self.slots[idx].name;
            if let Some(ids)=self.bindings.get_mut(name){ids.pop();}
        }
        self.slots.truncate(start);
        self.ref_slots.retain(|&idx|idx<start);
        Ok(())
    }
    fn release_loan(&mut self,id:usize)->Result<(),String>{
        if !self.loans.get(id).is_some_and(|l|l.alive){return Ok(());}
        //A child must not outlive its parent's reference storage
        let target=self.loans[id].target;
        if self.active_loans.get(&target).is_some_and(|active|active.iter().any(|&other|
            other!=id&&self.ancestor(other,id))){
            return Err("cannot end parent reference with live reborrow".into());
        }
        self.loans[id].alive=false;
        let empty=if let Some(ids)=self.active_loans.get_mut(&target){
            ids.retain(|&other|other!=id);ids.is_empty()
        }else{false};
        if empty{self.active_loans.remove(&target);}
        Ok(())
    }
    fn ancestor(&self,mut node:usize,ancestor:usize)->bool{
        while let Some(l)=self.loans.get(node){if node==ancestor{return true;}if let Some(p)=l.parent{node=p;}else{break;}}
        false
    }
    fn check_access(&self,target:usize,via:Option<usize>,exclusive:bool)->Result<(),String>{
        if let Some(active)=self.active_loans.get(&target){for &i in active{
            let l=&self.loans[i];
            if let Some(v)=via {
                if self.ancestor(i,v) && i!=v{return Err("parent reference is suspended by active reborrow".into());}
                if self.ancestor(v,i){continue;}
                if i==v{continue;}
            }
            if exclusive||l.mutable {return Err("borrow conflict: quantum or host resource already borrowed".into());}
        }}
        Ok(())
    }
    fn make_loan(&mut self,source:&str,mutable:bool,via_ref:bool)->Result<Value,String>{
        let from=self.lookup(source)?;
        let (target,parent)=if via_ref {
            let Value::Ref(id)=self.slots[from].value else {return Err("reborrow requires reference".into());};
            let l=self.loans.get(id).ok_or("invalid loan")?;
            if !l.alive{return Err("reborrow of expired reference".into());}
            if mutable&&!l.mutable{return Err("cannot mutably reborrow shared reference".into());}
            (l.target,Some(id))
        }else{(from,None)};
        if self.slots[target].value==Value::Moved{return Err("borrow of moved value".into());}
        if mutable && !via_ref && !self.slots[target].mutable {return Err("mutable borrow requires let mut owner".into());}
        self.check_access(target,parent,mutable)?;
        let id=self.loans.len();self.loans.push(Loan{target,mutable,parent,alive:true});
        self.active_loans.entry(target).or_default().push(id);
        Ok(Value::Ref(id))
    }
    fn referenced_slots(&self,names:&HashSet<String>)->HashSet<usize>{
        if self.ref_slots.is_empty(){return HashSet::new();}
        names.iter().filter_map(|name| self.bindings.get(name)
            .and_then(|ids|ids.last()).copied())
            .filter(|&idx| self.slots.get(idx).is_some_and(|slot|matches!(&slot.value,Value::Ref(_))))
            .collect()
    }
    fn expire_unused(&mut self,live:&HashSet<String>)->Result<(),String>{
        if self.ref_slots.is_empty(){return Ok(());}
        let mut keep=self.referenced_slots(live);
        for future in &self.continuation_refs {keep.extend(future.iter().copied());}
        let mut expired=Vec::new();
        for &idx in &self.ref_slots{
            let slot=&self.slots[idx];
            let Value::Ref(id)=slot.value else{continue;};
            if keep.contains(&idx){continue;}
            if self.active_loans.get(&self.loans[id].target).is_some_and(|active|
                active.iter().any(|&other|other!=id&&self.ancestor(other,id))) {continue;}
            expired.push((idx,id));
        }
        for (idx,id) in expired{
            self.release_loan(id)?;
            self.slots[idx].value=Value::Moved;
        }
        self.ref_slots.retain(|&idx|matches!(&self.slots[idx].value,Value::Ref(_)));
        Ok(())
    }
    fn read(&mut self,name:&str)->Result<Value,String>{
        let idx=self.lookup(name)?;
        match self.slots[idx].value.clone(){
            Value::Moved=>Err(format!("use of moved value '{name}'")),
            Value::Qubit(q)=>{self.check_access(idx,None,true)?;self.slots[idx].value=Value::Moved;Ok(Value::Qubit(q))},
            Value::Ref(id)=>{
                if !self.loans.get(id).is_some_and(|l|l.alive){return Err("use of expired reference".into());}
                if self.loans[id].mutable{self.slots[idx].value=Value::Moved;Ok(Value::Ref(id))}
                else{let child=self.loans.len();let target=self.loans[id].target;
                    self.loans.push(Loan{target,mutable:false,parent:None,alive:true});
                    self.active_loans.entry(target).or_default().push(child);
                    Ok(Value::Ref(child))}
            },
            v=>{self.check_access(idx,None,false)?;Ok(v)}
        }
    }
    fn quantum_operand(&self,e:&Expr)->Result<(usize,usize,Option<usize>),String>{
        let name=match e{Expr::Var(s)|Expr::Deref(s)=>s,_=>return Err("quantum operand must be a named owner or reference".into())};
        let idx=self.lookup(name)?;
        let (owner,via)=match self.slots[idx].value{
            Value::Ref(id)=>{let l=self.loans.get(id).ok_or("unknown loan")?;
                if !l.alive{return Err("expired quantum reference".into());}
                if !l.mutable{return Err("quantum gate requires mutable reference, not &Qubit".into());}
                (l.target,Some(id))},
            Value::Qubit(_)=>(idx,None),Value::Moved=>return Err("use of moved qubit".into()),
            _=>return Err("expected Qubit".into()),
        };
        let Value::Qubit(q)=self.slots[owner].value else{return Err("quantum owner is moved or invalid".into())};
        self.check_access(owner,via,true)?;
        Ok((q,owner,via))
    }
    fn calculate(&mut self,e:&Expr)->Result<Value,String>{
        self.step()?;
        match e{
            Expr::Int(v)=>Ok(Value::Int(*v)),Expr::Float(v)=>Ok(Value::Float(*v)),Expr::Bool(v)=>Ok(Value::Bool(*v)),
            Expr::Text(t)=>Ok(Value::Text(t.clone())),Expr::Var(s)=>{
                if s=="pi"{return Ok(Value::Float(std::f64::consts::PI));}
                if s=="tau"{return Ok(Value::Float(std::f64::consts::TAU));}
                self.read(s)
            },
            Expr::Borrow{source,mutable,via_ref}=>self.make_loan(source,*mutable,*via_ref),
            Expr::Deref(name)=>{
                let idx=self.lookup(name)?;let Value::Ref(id)=self.slots[idx].value else{return Err("dereference requires a reference".into())};
                if !self.loans.get(id).is_some_and(|l|l.alive){return Err("expired reference".into());}
                let target=self.loans[id].target;
                self.check_access(target,Some(id),false)?;
                match self.slots[target].value.clone(){Value::Qubit(_)=>Err("cannot copy Qubit through reference".into()),Value::Moved=>Err("dereference of moved value".into()),v=>Ok(v)}
            },
            Expr::Unary(op,e)=>{let v=self.calculate(e)?;match op{
                K::Minus=>match v{Value::Int(n)=>n.checked_neg().map(Value::Int).ok_or("integer overflow".into()),Value::Float(n)=>Ok(Value::Float(-n)),_=>Err("unary minus requires number".into())},
                K::Bang=>Ok(Value::Bool(!v.truth()?)),_=>Err("unsupported unary operator".into()),
            }},
            Expr::Binary(K::AndAnd,a,b)=>{let x=self.calculate(a)?.truth()?;if !x{Ok(Value::Bool(false))}else{Ok(Value::Bool(self.calculate(b)?.truth()?))}},
            Expr::Binary(K::OrOr,a,b)=>{let x=self.calculate(a)?.truth()?;if x{Ok(Value::Bool(true))}else{Ok(Value::Bool(self.calculate(b)?.truth()?))}},
            Expr::Binary(op,a,b)=>{let x=self.calculate(a)?;let y=self.calculate(b)?;binary(*op,x,y)},
            Expr::Call(name,args)=>self.call(name,args),
        }
    }
    fn call(&mut self,name:&str,args:&[Expr])->Result<Value,String>{
        if name=="qubit"{if !args.is_empty(){return Err("qubit() expects 0 arguments".into());}
            let id=self.quantum.allocate()?;self.allocated_qubits+=1;return Ok(Value::Qubit(id));}
        if name=="measure"||name=="measure_keep"{
            if args.len()!=1{return Err("measure expects one qubit".into());}
            let (id,owner,via)=self.quantum_operand(&args[0])?;
            if name=="measure" && via.is_some(){return Err("measure() cannot consume Qubit through a reference".into());}
            let result=if name=="measure"{self.quantum.measure_and_release(id)?}else{self.quantum.measure(id)?};
            if name=="measure"{self.slots[owner].value=Value::Moved;}
            self.measurements+=1;return Ok(Value::Int(i64::from(result)));
        }
        if name=="reset"{
            if args.len()!=1{return Err("reset expects one qubit".into());}
            let (id,_,_)=self.quantum_operand(&args[0])?;self.quantum.reset(id)?;
            return Ok(Value::Unit);
        }
        if let Some(id)=sema::gate_id(name){
            let spec=sema::gate_spec(id);
            if args.len()!=spec.parameters+spec.qubits{return Err(format!("gate '{name}' expects {} arguments",spec.parameters+spec.qubits));}
            let mut angle=[0.0f64;4];
            for (i,e) in args[..spec.parameters].iter().enumerate(){angle[i]=self.calculate(e)?.number()?;}
            let mut qs=[0usize;3];let mut owners=[usize::MAX;3];
            for (i,e) in args[spec.parameters..].iter().enumerate(){
                let (q,owner,_)=self.quantum_operand(e)?;
                if owners[..i].contains(&owner){return Err("duplicate quantum owner in gate".into());}
                owners[i]=owner;qs[i]=q;
            }
            self.quantum.apply(id,&qs[..spec.qubits],&angle[..spec.parameters])?;
            return Ok(Value::Unit);
        }
        if name=="input"{
            if args.len()>1{return Err("input accepts zero or one string prompt".into());}
            if let Some(expr)=args.first(){let p=self.calculate(expr)?;let Value::Text(prompt)=p else{return Err("input prompt must be string".into());};self.console.write(&prompt);}
            let raw=self.console.read_line()?;
            let n=parse_input_i64(&raw)?;
            return Ok(Value::Int(n));
        }
        if name=="print"||name=="println"{
            let mut values=Vec::with_capacity(args.len());
            for e in args{values.push(self.calculate(e)?);}
            let message=if let Some(Value::Text(template))=values.first(){
                let mut parts=template.split("{}");let mut result=parts.next().unwrap_or("").to_owned();
                let mut inserted=0;
                for fragment in parts{
                    let value=values.get(inserted+1).ok_or("too few formatting arguments")?;
                    result.push_str(&value.display());result.push_str(fragment);inserted+=1;
                }
                if inserted+1!=values.len(){
                    if inserted==0 {
                        for value in values.iter().skip(1){result.push(' ');result.push_str(&value.display());}
                    }else{return Err("formatting argument count mismatch".into());}
                }
                result
            }else{values.iter().map(Value::display).collect::<Vec<_>>().join(" ")};
            self.console.write(&message);if name=="println"{self.console.write("\n");}
            for v in values{if let Value::Ref(id)=v{self.release_loan(id)?;}}
            return Ok(Value::Unit);
        }
        if let Some(function)=self.functions.get(name).cloned(){
            if function.params.len()!=args.len(){return Err(format!("function '{name}' expects {} arguments",function.params.len()));}
            if self.call_depth>=MAX_DEPTH{return Err("function call depth exceeded".into());}
            let mut values=Vec::with_capacity(args.len());
            for arg in args {values.push(self.calculate(arg)?);}
            self.call_depth+=1;
            let outer_start=self.slots.len();
            self.begin_scope();
            for (param,value) in function.params.iter().zip(values){
                self.add_slot(param.name.clone(),param.mutable,Some(param.ty.clone()),value)?;
            }
            let saved_return=self.return_value.take();
            let result=self.block(&function.body,false);
            let returned=self.return_value.take();self.return_value=saved_return;
            if let Some(Value::Ref(id))=&returned {
                if function.return_from.is_none(){return Err("reference return requires declared lifetime parameter".into());}
                if self.loans.get(*id).is_none_or(|l|l.target>=outer_start){
                    return Err("cannot return reference to callee-local storage".into());
                }
            }
            let cleanup=self.end_scope();self.call_depth-=1;
            let flow=result?;cleanup?;
            let value=if flow==Flow::Return{returned.unwrap_or(Value::Unit)}else{Value::Unit};
            type_check(&function.ret,&value)?;
            return Ok(value);
        }
        Err(format!("unsupported hybrid call '{name}' (no implicit effect-free fallback)"))
    }
    fn add_slot(&mut self,name:String,mutable:bool,declared:Option<String>,value:Value)->Result<(),String>{
        if self.slots.len()>=MAX_SLOTS{return Err("hybrid runtime storage limit exceeded".into());}
        let begin=*self.scopes.last().ok_or("storage outside lexical scope")?;
        if self.bindings.get(&name).and_then(|ids|ids.last()).is_some_and(|&idx|idx>=begin){
            return Err(format!("duplicate binding '{name}'"));
        }
        let ty=declared.unwrap_or_else(||value.ty().to_owned());
        type_check(&ty,&value)?;
        let idx=self.slots.len();self.bindings.entry(name.clone()).or_default().push(idx);
        self.slots.push(Slot{name,mutable,ty,value});
        if matches!(&self.slots[idx].value,Value::Ref(_)){self.ref_slots.push(idx);}
        Ok(())
    }
    fn assign(&mut self,name:&str,op:K<'static>,expr:&Expr)->Result<(),String>{
        let idx=self.lookup(name)?;
        if !self.slots[idx].mutable{return Err(format!("cannot assign immutable variable '{name}'"));}
        let rhs=self.calculate(expr)?;
        let old=self.slots[idx].value.clone();
        if matches!(&old,Value::Qubit(_)){
            return Err("cannot overwrite a live Qubit: consume or measure its handle first".into());
        }
        let result=if op==K::Equal{rhs}else{
            let basic=match op{K::PlusEq=>K::Plus,K::MinusEq=>K::Minus,K::StarEq=>K::Star,
                K::SlashEq=>K::Slash,K::PercentEq=>K::Percent,_=>return Err("unsupported assignment".into())};
            binary(basic,old,rhs)?
        };
        self.check_access(idx,None,true)?;
        type_check(&self.slots[idx].ty,&result)?;
        //Do not silently drop a live mutable/shared reference on overwrite
        if let Value::Ref(id)=self.slots[idx].value{self.release_loan(id)?;}
        self.slots[idx].value=result;
        Ok(())
    }
    fn block(&mut self,body:&[Stmt],is_loop:bool)->Result<Flow,String>{
        let continuation_depth=self.continuation_refs.len();
        self.begin_scope();let result=self.statements(body,is_loop);
        self.continuation_refs.truncate(continuation_depth);
        let cleanup=self.end_scope();
        match (result,cleanup){(Err(e),_)=>Err(e),(Ok(_),Err(e))=>Err(e),(Ok(f),Ok(()))=>Ok(f)}
    }
    fn statements(&mut self,body:&[Stmt],is_loop:bool)->Result<Flow,String>{
        let key=body.as_ptr() as usize;
        if !self.live_cache.contains_key(&key){self.live_cache.insert(key,live_suffix(body));}
        for (idx,stmt) in body.iter().enumerate() {
            self.step()?;
            let mut future=self.live_cache.get(&key).and_then(|v|v.get(idx))
                .cloned().ok_or("missing cached liveness")?;
            if matches!(stmt,Stmt::While{..}|Stmt::For{..}) {
                uses_stmts(std::slice::from_ref(stmt),&mut future);
            }
            self.continuation_refs.push(self.referenced_slots(&future));
            match stmt{
                Stmt::Let{name,mutable,declared,value}=>{let val=self.calculate(value)?;
                    self.add_slot(name.clone(),*mutable,declared.clone(),val)?;},
                Stmt::Assign{name,operator,value}=>self.assign(name,*operator,value)?,
                Stmt::Expr(e)=>{let value=self.calculate(e)?;
                    if let Value::Ref(id)=value {self.release_loan(id)?;}
                },
                Stmt::Block(inner)=>{let f=self.block(inner,is_loop)?;if f!=Flow::Normal{return Ok(f);}},
                Stmt::If{cond,then_body,else_body}=>{
                    let test=self.calculate(cond)?.truth()?;
                    let f=self.block(if test{then_body}else{else_body},is_loop)?;
                    if f!=Flow::Normal{return Ok(f);}
                },
                Stmt::While{cond,body}=>{
                    while self.calculate(cond)?.truth()?{
                        match self.block(body,true)?{Flow::Normal|Flow::Continue=>{},Flow::Break=>break,Flow::Return=>return Ok(Flow::Return)}
                        self.step()?;
                    }
                },
                Stmt::For{name,from,to,inclusive,body}=>{
                    let start=self.calculate(from)?.integer()?;let end=self.calculate(to)?.integer()?;
                    let mut i=start;
                    while if *inclusive{i<=end}else{i<end}{
                        self.begin_scope();
                        let result=(||{
                            self.add_slot(name.clone(),false,Some("i64".into()),Value::Int(i))?;
                            self.block(body,true)
                        })();
                        let cleanup=self.end_scope();
                        let f=result?;cleanup?;
                        match f{Flow::Return=>return Ok(f),Flow::Break=>break,Flow::Normal|Flow::Continue=>{}}
                        i=i.checked_add(1).ok_or("for counter overflow")?;self.step()?;
                    }
                },
                Stmt::Break if is_loop=>return Ok(Flow::Break),
                Stmt::Continue if is_loop=>return Ok(Flow::Continue),
                Stmt::Break|Stmt::Continue=>return Err("break/continue outside loop".into()),
                Stmt::Return(expr)=>{
                    self.return_value=if let Some(value)=expr{Some(self.calculate(value)?)}else{Some(Value::Unit)};
                    return Ok(Flow::Return);
                },
            }
            self.continuation_refs.pop();
            if let Some(live)=self.live_cache.get(&key).and_then(|v|v.get(idx)).cloned(){
                self.expire_unused(&live)?;
            }
        }
        Ok(Flow::Normal)
    }
}
fn type_check(ty:&str,value:&Value)->Result<(),String>{
    let valid=match ty{
        "i64"|"Int"=>matches!(value,Value::Int(_)),
        "u32"=>matches!(value,Value::Int(v) if (0..=u32::MAX as i64).contains(v)),
        "u64"=>matches!(value,Value::Int(v) if *v>=0),
        "Float"|"f64"=>matches!(value,Value::Float(_)),
        "bool"|"Bool"=>matches!(value,Value::Bool(_)),
        "Bit"=>matches!(value,Value::Bool(_)|Value::Int(0|1)),
        "String"=>matches!(value,Value::Text(_)),
        "Qubit"=>matches!(value,Value::Qubit(_)),
        "Reference"=>matches!(value,Value::Ref(_)),
        "Unit"=>matches!(value,Value::Unit),
        _=>return Err(format!("unsupported runtime type '{ty}'")),
    };
    if valid{Ok(())}else{Err(format!("runtime type mismatch: expected {ty}, got {}",value.ty()))}
}
fn binary(op:K<'static>,a:Value,b:Value)->Result<Value,String>{
    use K::*;
    if let (Value::Int(x),Value::Int(y))=(&a,&b){
        let (x,y)=(*x,*y);
        return match op{
            Plus=>x.checked_add(y).map(Value::Int).ok_or("integer overflow".into()),
            Minus=>x.checked_sub(y).map(Value::Int).ok_or("integer overflow".into()),
            Star=>x.checked_mul(y).map(Value::Int).ok_or("integer overflow".into()),
            Slash=>x.checked_div(y).map(Value::Int).ok_or("integer division by zero or overflow".into()),
            Percent=>x.checked_rem(y).map(Value::Int).ok_or("integer remainder by zero or overflow".into()),
            EqEq=>Ok(Value::Bool(x==y)),NotEq=>Ok(Value::Bool(x!=y)),
            Less=>Ok(Value::Bool(x<y)),LessEq=>Ok(Value::Bool(x<=y)),Greater=>Ok(Value::Bool(x>y)),GreaterEq=>Ok(Value::Bool(x>=y)),
            _=>Err("invalid integer operator".into()),
        };
    }
    if let (Value::Bool(x),Value::Bool(y))=(&a,&b){
        return match op{EqEq=>Ok(Value::Bool(x==y)),NotEq=>Ok(Value::Bool(x!=y)),_=>Err("invalid boolean operator".into())};
    }
    if let (Value::Text(x),Value::Text(y))=(&a,&b){
        return match op{EqEq=>Ok(Value::Bool(x==y)),NotEq=>Ok(Value::Bool(x!=y)),Plus=>Ok(Value::Text(format!("{x}{y}"))),_=>Err("invalid string operator".into())};
    }
    let x=a.number()?;let y=b.number()?;
    let value=match op{Plus=>x+y,Minus=>x-y,Star=>x*y,Slash=>x/y,Percent=>x%y,
        EqEq=>return Ok(Value::Bool(x==y)),NotEq=>return Ok(Value::Bool(x!=y)),
        Less=>return Ok(Value::Bool(x<y)),LessEq=>return Ok(Value::Bool(x<=y)),
        Greater=>return Ok(Value::Bool(x>y)),GreaterEq=>return Ok(Value::Bool(x>=y)),
        _=>return Err("invalid floating point operator".into()),
    };
    if !value.is_finite(){return Err("non-finite runtime arithmetic".into());}
    Ok(Value::Float(value))
}

pub fn is_host_source(source:&str)->bool{
    syntax::lex(source).ok().is_some_and(|t|t.windows(2).any(|pair|
        matches!(pair[0].kind,K::Ident("input"|"print"|"println")) &&
        matches!(pair[1].kind,K::LParen|K::Bang)))
}

pub fn check_source(source:&str)->Result<(),String>{
    if source.len()>MAX_SOURCE{return Err("hybrid source exceeds 1 MB".into());}
    let tokens=syntax::lex(source).map_err(|e|e.to_string())?;
    let program=Parser{tokens,i:0}.parse_program()?;
    host_static::verify_program(&program)
}

pub fn bench_static(source:&str,iterations:usize)->Result<(f64,f64,f64),String>{
    if source.len()>MAX_SOURCE{return Err("benchmark source too large".into());}
    if iterations==0 || iterations>50_000{return Err("benchmark iterations must be 1..=50000".into());}
    let tokens=syntax::lex(source).map_err(|e|e.to_string())?;
    let program=Parser{tokens,i:0}.parse_program()?;
    for _ in 0..3{host_static::verify_program(&program)?;}
    let mut samples=Vec::with_capacity(iterations);
    for _ in 0..iterations{
        let start=std::time::Instant::now();
        host_static::verify_program(&program)?;
        samples.push(start.elapsed().as_secs_f64()*1_000_000.0);
    }
    samples.sort_by(|a,b|a.total_cmp(b));
    let avg=samples.iter().sum::<f64>()/iterations as f64;
    let p50=samples[iterations/2];
    let p90=samples[((iterations-1)*9)/10];
    Ok((avg,p50,p90))
}

#[cfg(test)]
pub fn execute(source:&str,console:&mut dyn Console,seed:u64)->Result<RunStats,String>{
    execute_with_backend(source,console,seed,BackendKind::Local)
}

pub fn execute_with_backend(source:&str,console:&mut dyn Console,seed:u64,backend:BackendKind)->Result<RunStats,String>{
    if source.len()>MAX_SOURCE{return Err("hybrid source exceeds 1 MB".into());}
    let tokens=syntax::lex(source).map_err(|e|e.to_string())?;
    let program=Parser{tokens,i:0}.parse_program()?;
    host_static::verify_program(&program)?;
    let mut vm=Vm::with_backend(console,seed,backend)?;
    vm.functions=program.functions.into_iter().map(|(name,function)|(name,Rc::new(function))).collect();
    let flow=vm.block(&program.main,false)?;
    if matches!(flow,Flow::Break|Flow::Continue){return Err("invalid control flow at entry point".into());}
    Ok(RunStats{executed_steps:vm.steps,allocated_qubits:vm.allocated_qubits,measurements:vm.measurements})
}

#[cfg(test)]
mod tests{
    use super::*;
    #[derive(Default)] struct TestIo{lines:Vec<String>,out:String}
    impl Console for TestIo{
        fn read_line(&mut self)->Result<String,String>{if self.lines.is_empty(){return Err("missing test input".into());}Ok(self.lines.remove(0))}
        fn write(&mut self,s:&str){self.out.push_str(s);}
    }
    fn go(src:&str)->Result<String,String>{let mut io=TestIo::default();execute(src,&mut io,42)?;Ok(io.out)}
    fn go_unchecked(src:&str)->Result<String,String>{
        let tokens=syntax::lex(src).map_err(|e|e.to_string())?;
        let program=Parser{tokens,i:0}.parse_program()?;
        let mut io=TestIo::default();
        let mut vm=Vm::new(&mut io,42);
        vm.functions=program.functions.into_iter().map(|(name,f)|(name,Rc::new(f))).collect();
        vm.block(&program.main,false)?;
        drop(vm);
        Ok(io.out)
    }
    #[test] fn classical_dynamic_loop_and_print(){
        assert_eq!(go("fn main(){let mut total:i64=0;for i in 0..5 {total+=i;} println!(\"sum={}\",total);}").unwrap(),"sum=10\n");
    }
    #[test] fn hybrid_coin_flips_from_input(){
        let src=include_str!("../examples/hybrid_coin_flip_0614.qr");
        let mut io=TestIo{lines:vec!["12\n".into()],out:String::new()};
        let stats=execute(src,&mut io,77).unwrap();
        assert_eq!(stats.measurements,12);assert!(io.out.contains("Total: 12"));
    }
    #[test] fn hybrid_quantum_measurement_is_reproducible(){
        let s="fn main(){let q=qubit();h(q);println!(\"{}\",measure(q));}";
        assert_eq!(go(s).unwrap(),go(s).unwrap());
    }
    #[test] fn cannot_overwrite_live_qubit(){
        assert!(go("fn main(){let mut q=qubit();q=qubit();println!(\"x\");}").unwrap_err().contains("overwrite"));
    }
    #[test] fn quantum_move_prevents_use_after_move(){
        let s="fn main(){let q=qubit();let other=q;h(q);println!(\"{}\",measure(other));}";
        assert!(go(s).unwrap_err().contains("moved"));
    }
    #[test] fn independent_loan_prevents_mutation(){
        let s="fn main(){let mut q=qubit();let r=&q;h(q);let next=&*r;println!(\"x\");}";
        assert!(check_source(s).is_err(),"static MIR must reject the live borrow conflict");
        assert!(go(s).is_err(),"runtime entry must reject the live borrow conflict");
        assert!(go_unchecked(s).unwrap_err().contains("borrow"),"runtime must independently reject the live borrow conflict");
    }
    #[test] fn dead_shared_loan_does_not_block_quantum_gate(){
        let s="fn main(){let mut q=qubit();let r=&q;h(q);h(q);println!(\"{}\",measure(q));}";
        assert_eq!(go(s).unwrap(),"0\n");
    }
    #[test] fn mutable_borrow_allows_access_through_reference(){
        let borrowed="fn main(){let mut q=qubit();{let r=&mut q;h(r);}println!(\"{}\",measure(q));}";
        let direct="fn main(){let mut q=qubit();h(q);println!(\"{}\",measure(q));}";
        assert_eq!(go(borrowed).unwrap(),go(direct).unwrap());
        let reversible="fn main(){let mut q=qubit();{let r=&mut q;h(r);h(r);}println!(\"{}\",measure(q));}";
        assert_eq!(go(reversible).unwrap(),"0\n");
    }
    #[test] fn mutable_reference_gate_changes_owner_state(){
        let s="fn main(){let mut q=qubit();{let r=&mut q;x(r);}println!(\"{}\",measure(q));}";
        assert_eq!(go(s).unwrap(),"1\n");
    }
    #[test] fn shared_reference_cannot_become_mutable(){
        let s="fn main(){let mut q=qubit();let r=&q;let s=&mut *r;println!(\"x\");}";
        assert!(go(s).unwrap_err().contains("mutably reborrow"));
    }
    #[test] fn nested_mut_reborrow_suspends_parent(){
        let s="fn main(){let mut q=qubit();let a=&mut q;{let b=&mut *a;h(a);h(b);}println!(\"x\");}";
        assert!(check_source(s).is_err(),"static MIR must reject use of suspended parent");
        assert!(go(s).is_err(),"runtime entry must reject use of suspended parent");
        assert!(go_unchecked(s).unwrap_err().contains("suspended"),"runtime must independently reject the suspended parent");
    }
    #[test] fn dead_mutable_reborrow_allows_parent_access(){
        let s="fn main(){let mut q=qubit();let a=&mut q;{let b=&mut *a;h(a);h(a);}println!(\"{}\",measure(q));}";
        assert_eq!(go(s).unwrap(),"0\n");
    }
    #[test] fn nll_preserves_outer_reference_across_inner_block(){
        let s="fn main(){let mut q=qubit();let r=&mut q;if true{println!(\"inner\");}h(r);h(r);println!(\"{}\",measure(q));}";
        assert_eq!(go(s).unwrap(),"inner\n0\n");
    }
    #[test] fn nll_preserves_reference_across_loop_iterations(){
        let s="fn main(){let mut q=qubit();let r=&mut q;for i in 0..2{h(r);}println!(\"{}\",measure(q));}";
        assert_eq!(go(s).unwrap(),"0\n");
    }
    #[test] fn nll_preserves_reference_across_while_iterations(){
        let s="fn main(){let mut q=qubit();let r=&mut q;let mut i=0;while i<2{h(r);i+=1;}println!(\"{}\",measure(q));}";
        assert_eq!(go(s).unwrap(),"0\n");
    }
    #[test] fn nll_releases_locals_inside_loop(){
        let s="fn main(){let mut q=qubit();for i in 0..2{let r=&mut q;h(r);h(q);}println!(\"{}\",measure(q));}";
        assert_eq!(go(s).unwrap(),"0\n");
    }
    #[test] fn immutable_binding_cannot_assign(){
        let s="fn main(){let x=1;x=2;println!(\"{}\",x);}";
        assert!(go(s).unwrap_err().contains("immutable"));
    }
    #[test] fn division_by_zero_rejected(){assert!(go("fn main(){println!(\"{}\",3/0);}").unwrap_err().contains("zero"));}
    #[test] fn measurement_bit_is_usable_as_condition(){
        assert_eq!(go("fn main(){let q=qubit();let bit:Bit=measure(q);if bit{println!(\"1\");}else{println!(\"0\");}}").unwrap(),"0\n");
    }
    #[test] fn loop_budget_rejected(){assert!(go("fn main(){while true{}} ").unwrap_err().contains("limit"));}
    #[test] fn unsupported_call_rejected(){assert!(go("fn main(){unknown();println!(\"x\");}").unwrap_err().contains("unsupported"));}
    #[test] fn host_branch_takes_only_one_side(){assert_eq!(go("fn main(){if false{println!(\"bad\");}else{println!(\"good\");}}").unwrap(),"good\n");}
    #[test] fn lexical_borrow_blocks_rebinding_owner(){
        assert!(go("fn main(){let mut x=2;let r=&x;x=3;println!(\"{}\",r);}").unwrap_err().contains("borrow"));
    }
    #[test] fn input_negative_u32_is_rejected(){
        let mut io=TestIo{lines:vec!["-1".into()],out:String::new()};
        assert!(execute("fn main(){let x:u32=input();println!(\"{}\",x);}",&mut io,1).unwrap_err().contains("mismatch"));
    }
    #[test] fn long_loop_recycles_local_storage() {
        let tokens=syntax::lex("fn main(){for i in 0..10000{let q=qubit();measure(q);}}").unwrap();
        let body=Parser{tokens,i:0}.parse().unwrap();
        host_static::verify(&body).unwrap();
        let mut io=TestIo::default();
        let mut vm=Vm::new(&mut io,42);
        assert_eq!(vm.block(&body,false).unwrap(),Flow::Normal);
        assert_eq!(vm.slots.len(),0);
        assert!(vm.slots.capacity()<64,"ended loop scopes should release storage");
        assert_eq!(vm.measurements,10000);
    }

    #[test] fn static_failure_occurs_before_any_host_io() {
        let mut io=TestIo::default();
        let src=r#"fn main(){let x=input("PROMPT");if false{unknown_operation();}println!("{}",x);}"#;
        let err=execute(src,&mut io,42).unwrap_err();
        assert!(err.contains("unknown_operation"));
        assert!(io.out.is_empty(),"static analysis must run before input prompts");
    }

    #[test] fn cli_input_console_supplies_values_without_stdin() {
        let mut fallback=TestIo::default();
        let src=r#"fn main(){let a:i64=input("a:");let b:i64=input("b:");println!("{}",a+b);}"#;
        {
            let mut console=InputConsole::new(&mut fallback,vec!["40".into(),"2".into()]);
            execute(src,&mut console,42).unwrap();
        }
        assert_eq!(fallback.out,"a:b:42\n");
    }
    #[test] fn cli_input_console_falls_back_to_interactive_source() {
        let mut fallback=TestIo{lines:vec!["5\n".into()],out:String::new()};
        let src=r#"fn main(){let a:i64=input();let b:i64=input();println!("{}",a+b);}"#;
        {
            let mut console=InputConsole::new(&mut fallback,vec!["37".into()]);
            execute(src,&mut console,42).unwrap();
        }
        assert_eq!(fallback.out,"42\n");
    }
    #[test] fn input_parse_diagnoses_eof_and_bom() {
        assert_eq!(parse_input_i64("100\r\n"),Ok(100));
        assert_eq!(parse_input_i64("\u{feff}100\n"),Ok(100));
        assert!(parse_input_i64("").unwrap_err().contains("EOF"));
        assert!(parse_input_i64("100\0").unwrap_err().contains("4 byte"));
    }

}

#[cfg(test)]
mod hybrid_0616_tests {
    use super::*;
    #[derive(Default)] struct Out {text:String}
    impl Console for Out {
        fn read_line(&mut self)->Result<String,String>{Err("unexpected input".into())}
        fn write(&mut self,s:&str){self.text.push_str(s);}
    }
    fn run(src:&str)->Result<String,String>{
        let mut io=Out::default();execute(src,&mut io,42)?;Ok(io.text)
    }
    #[test] fn runtime_nll_last_use_releases_borrow(){
        let src=r#"fn main(){let mut q=qubit();let r=&mut q;h(r);h(q);println!("{}",measure(q));}"#;
        assert_eq!(run(src).unwrap(),"0\n");
    }
    #[test] fn function_moves_qubit_to_callee_and_returns_owner(){
        let src=r#"fn flip(q:Qubit)->Qubit{h(q);return q;}fn main(){let q=qubit();let moved=flip(q);h(moved);println!("{}",measure(moved));}"#;
        assert_eq!(run(src).unwrap(),"0\n");
    }
    #[test] fn function_mutably_borrows_caller_qubit(){
        let src=r#"fn flip(r:&mut Qubit){x(r);}fn main(){let mut q=qubit();flip(&mut q);println!("{}",measure(q));}"#;
        assert_eq!(run(src).unwrap(),"1\n");
    }
    #[test] fn return_reference_with_named_lifetime_from_parameter(){
        let src=r#"fn pass<'a>(r:&'a mut Qubit)->&'a mut Qubit{return r;}fn main(){let mut q=qubit();let r=pass(&mut q);x(r);println!("{}",measure(q));}"#;
        assert_eq!(run(src).unwrap(),"1\n");
    }
    #[test] fn reject_reference_to_callee_local(){
        let src=r#"fn bad<'a>(r:&'a mut Qubit)->&'a mut Qubit{let mut q=qubit();return &mut q;}fn main(){}"#;
        assert!(check_source(src).unwrap_err().contains("reference"));
    }
    #[test] fn reject_aliasing_mutable_function_arguments(){
        let src=r#"fn pair(a:&mut Qubit,b:&mut Qubit){h(a);h(b);}fn main(){let mut q=qubit();pair(&mut q,&mut q);}"#;
        assert!(check_source(src).is_err());
    }
    #[test] fn quantum_drop_inner_scope_fails_statically(){
        let src=r#"fn main(){{let q=qubit();}}"#;
        assert!(check_source(src).unwrap_err().contains("quantum-aware Drop"));
    }
    #[test] fn quantum_drop_explicit_measure_is_valid(){
        let src=r#"fn main(){{let q=qubit();measure(q);}println!("ok");}"#;
        assert_eq!(run(src).unwrap(),"ok\n");
    }
    #[test] fn qpc_selection_fails_before_side_effects(){
        let mut io=Out::default();
        let src=r#"fn main(){println!("SHOULD NOT PRINT");}"#;
        let err=execute_with_backend(src,&mut io,42,BackendKind::Qpc).unwrap_err();
        assert!(err.contains("unavailable"));assert!(io.text.is_empty());
    }
    #[test] fn helper_recursion_has_no_unsafe_certificate(){
        let src=r#"fn recursive(q:Qubit)->Qubit{return recursive(q);}fn main(){let q=qubit();let s=recursive(q);measure(s);}"#;
        assert!(check_source(src).is_err());
    }
}
