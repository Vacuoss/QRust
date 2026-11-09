//Hybrid host/quantum static effects lowered into the SAME typed MIR and CFG/NLL checker used by
//compiled QRust
use super::{Expr,Stmt,Program,Function};
use crate::{cfg_borrow::{Access,Event,Path},typed_mir::{BasicBlock,FunctionMir,Statement,Terminator},ids::SymbolId,syntax::TokenKind as K,sema};
use std::collections::HashMap;

const MAX_MIR_BLOCKS:usize=8192;
#[derive(Clone,Debug)]
enum Ty {
    Int, Float, Bool, Text, Qubit, Unit,
    Ref {path:Path, loan:SymbolId, mutable:bool},
}
#[derive(Clone,Debug)]
struct Binding {id:SymbolId,mutable:bool,ty:Ty,name:String}
#[derive(Default)]
struct Scope {vars:Vec<Binding>}
#[derive(Clone,Copy)]
struct Loop {break_to:usize,continue_to:usize,depth:usize}
struct Lower {
    blocks:Vec<BasicBlock>,
    scopes:Vec<Scope>,
    bindings:HashMap<String,Vec<Binding>>,
    loans:HashMap<SymbolId,Path>,
    types:HashMap<SymbolId,Ty>,
    serial:u32,
    next_token:usize,
    functions:HashMap<String,Function>,return_type:Option<String>,
}
impl Lower {
    fn new()->Self {Self {blocks:Vec::new(),scopes:Vec::new(),bindings:HashMap::new(),loans:HashMap::new(),types:HashMap::new(),serial:0,next_token:0,functions:HashMap::new(),return_type:None}}
    fn fresh(&mut self)->Result<SymbolId,String>{
        self.serial=self.serial.checked_add(1).ok_or("host MIR symbol limit exceeded")?;
        Ok(SymbolId(self.serial))
    }
    fn token(&mut self)->usize {let n=self.next_token;self.next_token+=1;n}
    fn block(&mut self,statement:Option<Statement>)->Result<usize,String>{
        if self.blocks.len()>=MAX_MIR_BLOCKS {return Err("host MIR CFG block limit exceeded".into());}
        let id=self.blocks.len();self.blocks.push(BasicBlock{statements:statement.into_iter().collect(),terminator:Terminator::Goto(Vec::new())});Ok(id)
    }
    fn connect(&mut self,from:&[usize],to:usize){
        for &id in from {if let Terminator::Goto(ref mut edges)=self.blocks[id].terminator {
            if !edges.contains(&to){edges.push(to);}
        }}
    }
    fn event(&mut self,op:Access,path:Path,loan:Option<SymbolId>,parent:Option<SymbolId>)->Event{
        Event{op,path,loan,parent,token:self.token()}
    }
    fn append(&mut self,from:Vec<usize>,statement:Statement)->Result<Vec<usize>,String>{
        if from.is_empty(){return Ok(from);}let id=self.block(Some(statement))?;
        self.connect(&from,id);Ok(vec![id])
    }
    fn access(&mut self,from:Vec<usize>,op:Access,path:Path,via:Option<SymbolId>)->Result<Vec<usize>,String>{
        let ev=self.event(op,path,via,None);self.append(from,Statement::Access(ev))
    }
    fn bind(&mut self,from:Vec<usize>,name:&str,mutable:bool,ty:Ty)->Result<Vec<usize>,String>{
        let id=self.fresh()?;
        if self.scopes.last().is_some_and(|scope|scope.vars.iter().any(|b|b.name==name)){
            return Err(format!("duplicate binding '{name}'"));
        }
        let b=Binding{id,mutable,ty,name:name.to_owned()};
        self.bindings.entry(name.to_owned()).or_default().push(b.clone());
        self.types.insert(id,b.ty.clone());
        self.scopes.last_mut().ok_or("MIR declaration outside scope")?.vars.push(b);
        let p=Path::root(id);
        let live=self.event(Access::StorageLive,p.clone(),None,None);
        let from=self.append(from,Statement::StorageLive(live))?;
        self.access(from,Access::Initialize,p,None)
    }
    fn binding(&self,name:&str)->Result<Binding,String>{
        self.bindings.get(name).and_then(|v|v.last()).cloned().ok_or_else(||format!("undefined variable '{name}'"))
    }
    fn var(&mut self,from:Vec<usize>,name:&str,move_qubit:bool)->Result<(Vec<usize>,Ty),String>{
        if name=="pi"||name=="tau"{return Ok((from,Ty::Float));}
        let b=self.binding(name)?;
        let (op,via)=match &b.ty {
            Ty::Qubit if move_qubit=>(Access::Move,None),
            _=>(Access::Read,None),
        };
        let from=self.access(from,op,Path::root(b.id),via)?;
        let from=if let Ty::Ref{ref path,loan,..}=b.ty {
            self.access(from,Access::Read,path.clone(),Some(loan))?
        }else{from};
        Ok((from,b.ty))
    }
    fn borrow(&mut self,from:Vec<usize>,name:&str,mutable:bool,via_ref:bool,loan:SymbolId)->Result<(Vec<usize>,Ty),String>{
        let b=self.binding(name)?;
        let (path,parent)=if via_ref {
            match &b.ty {
                Ty::Ref{path,loan:parent,mutable:yes}=>{
                    if mutable&&!*yes{return Err("cannot mutably reborrow shared reference".into());}
                    (path.clone(),Some(*parent))
                },_=>return Err("reborrow requires reference".into()),
            }
        }else{
            if mutable&&!b.mutable{return Err("mutable borrow requires let mut owner".into());}
            (Path::root(b.id),None)
        };
        let from=if via_ref {
            self.access(from,Access::Read,Path::root(b.id),None)?
        }else{from};
        let op=if mutable {Access::BorrowMut}else{Access::BorrowShared};
        let ev=self.event(op,path.clone(),Some(loan),parent);
        let from=self.append(from,Statement::Access(ev))?;
        self.loans.insert(loan,path.clone());
        Ok((from,Ty::Ref{path,loan,mutable}))
    }
    fn quantum_arg(&mut self,from:Vec<usize>,arg:&Expr,consume:bool)->Result<Vec<usize>,String>{
        let name=match arg {Expr::Var(name)|Expr::Deref(name)=>name,_=>return Err("quantum operand must be a named owner or reference".into())};
        let b=self.binding(name)?;
        match b.ty {
            Ty::Qubit=>{
                let path=Path::root(b.id);
                if consume {self.access(from,Access::Move,path,None)}
                else {
                    let from=self.access(from,Access::Read,path.clone(),None)?;
                    self.access(from,Access::Write,path,None)
                }
            },
            Ty::Ref{path,loan,mutable:true} if !consume=>{
                let from=self.access(from,Access::Read,Path::root(b.id),None)?;
                let from=self.access(from,Access::Read,path.clone(),Some(loan))?;
                self.access(from,Access::Write,path,Some(loan))
            },
            Ty::Ref{..}=>Err("quantum operand requires mutable reference; cannot consume through borrow".into()),
            _=>Err("quantum operand must have Qubit type".into()),
        }
    }
    fn expression(&mut self,mut from:Vec<usize>,expr:&Expr,dest:Option<SymbolId>)->Result<(Vec<usize>,Ty),String>{
        match expr {
            Expr::Int(_)=>Ok((from,Ty::Int)),Expr::Float(_)=>Ok((from,Ty::Float)),
            Expr::Bool(_)=>Ok((from,Ty::Bool)),Expr::Text(_)=>Ok((from,Ty::Text)),
            Expr::Var(s)=>{
                let (next,ty)=self.var(from,s,true)?;
                if let (Ty::Ref{path,loan,mutable:false},Some(id))=(&ty,dest) {
                    let ev=self.event(Access::BorrowShared,path.clone(),Some(id),Some(*loan));
                    let next=self.append(next,Statement::Access(ev))?;
                    self.loans.insert(id,path.clone());
                    return Ok((next,Ty::Ref{path:path.clone(),loan:id,mutable:false}));
                }
                if let (Ty::Ref{path,loan,mutable:true},Some(id))=(&ty,dest) {
                    let next=self.access(next,Access::Move,Path::root(self.binding(s)?.id),None)?;
                    let end=self.event(Access::EndLoan,path.clone(),Some(*loan),None);
                    let next=self.append(next,Statement::Access(end))?;
                    let child=self.event(Access::BorrowMut,path.clone(),Some(id),None);
                    let next=self.append(next,Statement::Access(child))?;
                    self.loans.insert(id,path.clone());
                    return Ok((next,Ty::Ref{path:path.clone(),loan:id,mutable:true}));
                }
                Ok((next,ty))
            }
            Expr::Borrow{source,mutable,via_ref}=>{
                let loan=match dest{Some(id)=>id,None=>self.fresh()?};
                self.borrow(from,source,*mutable,*via_ref,loan)
            }
            Expr::Deref(name)=>{
                let b=self.binding(name)?;
                let Ty::Ref{path,loan,..}=b.ty else{return Err("dereference requires reference".into());};
                //`*r` must validate both the reference's local storage and its loan. A move of `r` invalidates only its
                //binding, not necessarily the underlying owner
                let next=self.access(from,Access::Read,Path::root(b.id),None)?;
                let next=self.access(next,Access::Read,path.clone(),Some(loan))?;
                let kind=self.types.get(&path.owner).cloned().ok_or("untyped reference target")?;
                if matches!(kind,Ty::Qubit|Ty::Ref{..}) {
                    return Err("cannot copy linear Qubit or reference by dereference".into());
                }
                Ok((next,kind))
            }
            Expr::Unary(_,e)=>self.expression(from,e,None),
            Expr::Binary(op,a,b)=>{
                let (next,ak)=self.expression(from,a,None)?;
                let (next,bk)=self.expression(next,b,None)?;
                let kind=if matches!(op,K::EqEq|K::NotEq|K::Less|K::LessEq|K::Greater|K::GreaterEq|K::AndAnd|K::OrOr){Ty::Bool}
                    else if matches!(ak,Ty::Float)||matches!(bk,Ty::Float){Ty::Float}else{Ty::Int};
                Ok((next,kind))
            }
            Expr::Call(name,args)=>{
                if name=="qubit"{
                    if !args.is_empty(){return Err("qubit() expects no arguments".into());}
                    return Ok((from,Ty::Qubit));
                }
                if name=="measure"||name=="measure_keep"||name=="reset"{
                    if args.len()!=1{return Err(format!("{name} expects one qubit"));}
                    from=self.quantum_arg(from,&args[0],name=="measure")?;
                    return Ok((from,if name=="reset"{Ty::Unit}else{Ty::Int}));
                }
                if let Some(id)=sema::gate_id(name){
                    let spec=sema::gate_spec(id);
                    if args.len()!=spec.parameters+spec.qubits{return Err(format!("gate '{name}' argument count mismatch"));}
                    for arg in &args[..spec.parameters]{let (f,_)=self.expression(from,arg,None)?;from=f;}
                    for arg in &args[spec.parameters..]{from=self.quantum_arg(from,arg,false)?;}
                    return Ok((from,Ty::Unit));
                }
                if name=="input"{
                    if args.len()>1{return Err("input expects zero or one prompt".into());}
                    for arg in args{let (f,_)=self.expression(from,arg,None)?;from=f;}
                    return Ok((from,Ty::Int));
                }
                if name=="print"||name=="println"{
                    for arg in args{let (f,_)=self.expression(from,arg,None)?;from=f;}
                    return Ok((from,Ty::Unit));
                }
                if let Some(function)=self.functions.get(name).cloned(){
                    if args.len()!=function.params.len(){return Err(format!("function '{name}' argument count mismatch"));}
                    let returned_param=function.return_from.as_deref();
                    let mut returned_reference=None;
                    let mut end_call_loans:Vec<(Path,SymbolId)>=Vec::new();
                    let mut call_uses:Vec<Event>=Vec::new();
                    for (param,arg) in function.params.iter().zip(args){
                        let dest_id=self.fresh()?;
                        let returning=returned_param==Some(param.name.as_str());
                        let id=if returning{dest.unwrap_or(dest_id)}else{dest_id};
                        let (f,actual)=self.expression(from,arg,Some(id))?;from=f;
                        let matches=match param.ty.as_str(){
                            "Qubit"=>matches!(&actual,Ty::Qubit),
                            "Reference"=>matches!(&actual,Ty::Ref{mutable,..} if !param.mutable||*mutable),
                            "i64"|"u32"|"u64"|"Int"=>matches!(&actual,Ty::Int),
                            "bool"|"Bool"=>matches!(&actual,Ty::Bool),
                            "Float"|"f64"=>matches!(&actual,Ty::Float),
                            "String"=>matches!(&actual,Ty::Text),
                            _=>false,
                        };
                        if !matches{return Err(format!("invalid argument type for '{}': {}",name,param.name));}
                        if let Ty::Ref{path,loan,..}=actual {
                            call_uses.push(self.event(Access::Read,path.clone(),Some(loan),None));
                            if returning {returned_reference=Some(Ty::Ref{path,loan,mutable:param.mutable});}
                            else {end_call_loans.push((path,loan));}
                        }
                    }
                    let token=self.token();
                    let call=self.block(Some(Statement::Call{
                        name:name.to_owned(),token,events:call_uses,effects:Vec::new(),path_cases:Vec::new()
                    }))?;
                    self.connect(&from,call);from=vec![call];
                    //Every argument loan stays live THROUGH the call, so overlapping &mut parameters cannot be accepted by
                    //ending the first temporary before evaluating the next
                    for (path,loan) in end_call_loans.into_iter().rev(){
                        let event=self.event(Access::EndLoan,path,Some(loan),None);
                        from=self.append(from,Statement::Access(event))?;
                    }
                    if let Some(ty)=returned_reference {return Ok((from,ty));}
                    let ty=match function.ret.as_str(){
                        "Qubit"=>Ty::Qubit,
                        "Unit"=>Ty::Unit,
                        "Reference"=>return Err("reference return without proven parameter origin".into()),
                        "i64"|"u32"|"u64"|"Int"=>Ty::Int,
                        "bool"|"Bool"=>Ty::Bool,
                        "Float"|"f64"=>Ty::Float,
                        "String"=>Ty::Text,
                        _=>return Err(format!("unsupported return type in '{name}'")),
                    };
                    return Ok((from,ty));
                }
                Err(format!("unsupported hybrid call '{name}' (missing trusted effects)"))
            }
        }
    }
    fn enter(&mut self){self.scopes.push(Scope::default());}
    fn cleanup(&mut self,mut from:Vec<usize>,scope:usize)->Result<Vec<usize>,String>{
        let vars=self.scopes.get(scope).ok_or("invalid host MIR scope")?.vars.clone();
        for b in vars.iter().rev(){
            if (scope>0||self.return_type.is_some()) && matches!(&b.ty,Ty::Qubit)
                && !b.name.starts_with("__param_target_"){
                let ev=self.event(Access::QuantumRequireConsumed,Path::root(b.id),None,None);
                from=self.append(from,Statement::Access(ev))?;
            }
            let ev=self.event(Access::StorageDead,Path::root(b.id),None,None);
            from=self.append(from,Statement::StorageDead(ev))?;
        }
        Ok(from)
    }
    fn leave(&mut self,from:Vec<usize>)->Result<Vec<usize>,String>{
        let index=self.scopes.len()-1;
        let from=self.cleanup(from,index)?;
        let vars=self.scopes.pop().ok_or("host MIR scope underflow")?.vars;
        for b in vars.iter().rev(){
            if let Some(ids)=self.bindings.get_mut(&b.name){ids.pop();}
        }
        Ok(from)
    }
    fn exit_scopes(&mut self,mut from:Vec<usize>,down_to:usize)->Result<Vec<usize>,String>{
        for idx in (down_to..self.scopes.len()).rev(){from=self.cleanup(from,idx)?;}
        Ok(from)
    }
    fn body(&mut self,stmts:&[Stmt],mut from:Vec<usize>,loop_ctx:Option<Loop>,scoped:bool,loop_var:Option<&str>)->Result<Vec<usize>,String>{
        if scoped{self.enter();}
        if let Some(name)=loop_var{from=self.bind(from,name,false,Ty::Int)?;}
        for stmt in stmts{
            if from.is_empty(){
                //Unreachable code is still parsed and checked by the frontend; do not manufacture CFG paths from dead
                //statements
                break;
            }
            from=match stmt{
                Stmt::Let{name,mutable,declared,value}=>{
                    let id=self.fresh()?;
                    let (f,kind)=self.expression(from,value,Some(id))?;
                    if let Some(declared)=declared{
                        let good=match declared.as_str(){
                            "Qubit"=>matches!(kind,Ty::Qubit),
                            "Reference"=>matches!(kind,Ty::Ref{..}),
                            "i64"|"u32"|"u64"|"Int"|"Bit"=>matches!(kind,Ty::Int|Ty::Bool),
                            "bool"|"Bool"=>matches!(kind,Ty::Bool),
                            "Float"|"f64"=>matches!(kind,Ty::Float),
                            "String"=>matches!(kind,Ty::Text),
                            _=>false,
                        };
                        if !good{return Err(format!("static type mismatch: '{name}' declared as {declared}"));}
                    }
                    self.bind_existing(f,name,*mutable,id,kind)?
                }
                Stmt::Assign{name,operator,value}=>{
                    let b=self.binding(name)?;
                    if !b.mutable{return Err(format!("cannot assign immutable variable '{name}'"));}
                    if matches!(b.ty,Ty::Qubit){return Err("cannot overwrite a live Qubit".into());}
                    let (f,ty)=self.expression(from,value,None)?;
                    if matches!(ty,Ty::Qubit|Ty::Ref{..}) {return Err("assignment of linear or borrowed value requires a typed move destination".into());}
                    if matches!(operator,K::PlusEq|K::MinusEq|K::StarEq|K::SlashEq|K::PercentEq){
                        let f=self.access(f,Access::Read,Path::root(b.id),None)?;
                        self.access(f,Access::Write,Path::root(b.id),None)?
                    }else{self.access(f,Access::Write,Path::root(b.id),None)?}
                }
                Stmt::Expr(expr)=>{
                    let (f,_) = self.expression(from,expr,None)?;f
                }
                Stmt::Block(inner)=>self.body(inner,from,loop_ctx,true,None)?,
                Stmt::If{cond,then_body,else_body}=>{
                    let (cond_end,_)=self.expression(from,cond,None)?;
                    let fork=self.block(None)?;self.connect(&cond_end,fork);
                    let left=self.block(None)?;let right=self.block(None)?;
                    self.connect(&[fork],left);self.connect(&[fork],right);
                    let lt=self.body(then_body,vec![left],loop_ctx,true,None)?;
                    let rt=self.body(else_body,vec![right],loop_ctx,true,None)?;
                    let join=self.block(None)?;
                    self.connect(&lt,join);self.connect(&rt,join);
                    if lt.is_empty() && rt.is_empty(){Vec::new()}else{vec![join]}
                }
                Stmt::While{cond,body}=>{
                    let head=self.block(None)?;self.connect(&from,head);
                    let (f,_)=self.expression(vec![head],cond,None)?;
                    let fork=self.block(None)?;self.connect(&f,fork);
                    let inside=self.block(None)?;let after=self.block(None)?;
                    self.connect(&[fork],inside);self.connect(&[fork],after);
                    let context=Loop{break_to:after,continue_to:head,depth:self.scopes.len()};
                    let tail=self.body(body,vec![inside],Some(context),true,None)?;
                    self.connect(&tail,head);vec![after]
                }
                Stmt::For{name,from:begin,to,inclusive:_,body}=>{
                    let (f,_)=self.expression(from,begin,None)?;
                    let (f,_)=self.expression(f,to,None)?;
                    let head=self.block(None)?;self.connect(&f,head);
                    let inside=self.block(None)?;let after=self.block(None)?;
                    self.connect(&[head],inside);self.connect(&[head],after);
                    let context=Loop{break_to:after,continue_to:head,depth:self.scopes.len()};
                    let tail=self.body(body,vec![inside],Some(context),true,Some(name))?;
                    self.connect(&tail,head);vec![after]
                }
                Stmt::Break|Stmt::Continue=>{
                    let context=loop_ctx.ok_or("break/continue outside loop")?;
                    let exit=self.exit_scopes(from,context.depth)?;
                    let to=if matches!(stmt,Stmt::Break){context.break_to}else{context.continue_to};
                    self.connect(&exit,to);Vec::new()
                }
                Stmt::Return(expr)=>{
                    let mut from=from;
                    if let Some(expr)=expr{
                        let (f,ty)=self.expression(from,expr,None)?;from=f;
                        let valid=match self.return_type.as_deref(){
                            Some("Qubit")=>matches!(ty,Ty::Qubit),
                            Some("Reference")=>matches!(ty,Ty::Ref{..}),
                            Some("i64"|"u32"|"u64"|"Int")=>matches!(ty,Ty::Int),
                            Some("bool"|"Bool")=>matches!(ty,Ty::Bool),
                            Some("Float"|"f64")=>matches!(ty,Ty::Float),
                            Some("String")=>matches!(ty,Ty::Text),
                            Some("Unit")|None=>false,
                            _=>false,
                        };
                        if !valid {return Err("function return type mismatch".into());}
                    }else if self.return_type.as_deref().is_some_and(|t|t!="Unit"){
                        return Err("non-Unit function must return a value".into());
                    }
                    let exit=self.exit_scopes(from,0)?;
                    for id in exit{self.blocks[id].terminator=Terminator::Return;}
                    Vec::new()
                }
            };
        }
        if scoped{self.leave(from)}else{Ok(from)}
    }
    fn bind_existing(&mut self,from:Vec<usize>,name:&str,mutable:bool,id:SymbolId,ty:Ty)->Result<Vec<usize>,String>{
        if self.scopes.last().is_some_and(|scope|scope.vars.iter().any(|b|b.name==name)) {return Err(format!("duplicate binding '{name}'"));}
        let b=Binding{id,mutable,ty,name:name.to_owned()};
        self.bindings.entry(name.to_owned()).or_default().push(b.clone());
        self.types.insert(id,b.ty.clone());
        self.scopes.last_mut().ok_or("host MIR declaration outside scope")?.vars.push(b);
        let p=Path::root(id);
        let ev=self.event(Access::StorageLive,p.clone(),None,None);
        let from=self.append(from,Statement::StorageLive(ev))?;
        self.access(from,Access::Initialize,p,None)
    }
}
pub(super) fn verify_program(program:&Program)->Result<(),String>{
    for (name,func) in &program.functions {
        let mut lower=Lower::new();lower.return_type=Some(func.ret.clone());
        let entry=lower.block(None)?;lower.enter();
        let mut from=vec![entry];
        for param in &func.params{
            let kind=match param.ty.as_str(){
                "Qubit"=>Ty::Qubit,"i64"|"u32"|"u64"|"Int"=>Ty::Int,
                "bool"|"Bool"=>Ty::Bool,"Float"|"f64"=>Ty::Float,
                "String"=>Ty::Text,
                "Reference"=>{
                    let ghost=format!("__param_target_{}",param.name);
                    from=lower.bind(from,&ghost,true,Ty::Qubit)?;
                    let owner=lower.binding(&ghost)?;
                    let id=lower.fresh()?;
                    let path=Path::root(owner.id);
                    let ev=lower.event(if param.mutable{Access::BorrowMut}else{Access::BorrowShared},path.clone(),Some(id),None);
                    from=lower.append(from,Statement::Access(ev))?;
                    lower.loans.insert(id,path.clone());
                    from=lower.bind_existing(from,&param.name,param.mutable,id,Ty::Ref{path,loan:id,mutable:param.mutable})?;
                    continue;
                },
                _=>return Err(format!("unsupported type in function '{name}'")),
            };
            from=lower.bind(from,&param.name,param.mutable,kind)?;
        }
        let tails=lower.body(&func.body,from,None,true,None)?;
        if func.ret!="Unit" && !tails.is_empty(){return Err(format!("function '{name}' may exit without returning a value"));}
        let tails=lower.cleanup(tails,0)?;
        for id in tails{lower.blocks[id].terminator=Terminator::Return;}
        let mir=FunctionMir{blocks:lower.blocks,entry,loans:lower.loans};
        let errors=mir.verify()?;
        if let Some(error)=errors.first(){return Err(format!("function '{name}' static borrow check: {} (MIR node {})",error.message,error.node));}
    }
    let mut lower=Lower::new();lower.functions=program.functions.clone();
    let entry=lower.block(None)?;
    let tails=lower.body(&program.main,vec![entry],None,true,None)?;
    for id in tails{lower.blocks[id].terminator=Terminator::Return;}
    let mir=FunctionMir{blocks:lower.blocks,entry,loans:lower.loans};
    let conflicts=mir.verify()?;
    if let Some(error)=conflicts.first(){return Err(format!("static host/quantum borrow check: {} (MIR node {})",error.message,error.node));}
    Ok(())
}
#[allow(dead_code)]
pub(super) fn verify(stmts:&[Stmt])->Result<(),String>{
    let mut lower=Lower::new();
    let entry=lower.block(None)?;
    let tails=lower.body(stmts,vec![entry],None,true,None)?;
    for id in tails{lower.blocks[id].terminator=Terminator::Return;}
    let mir=FunctionMir{blocks:lower.blocks,entry,loans:lower.loans};
    let conflicts=mir.verify()?;
    if let Some(error)=conflicts.first(){return Err(format!("static host/quantum borrow check: {} (MIR node {})",error.message,error.node));}
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::check_source;
    #[test] fn rejects_use_after_move_in_untaken_if_arm() {
        let src="fn main(){let q=qubit();if false{let moved=q;}else{println!(\"ok\");}h(q);}";
        assert!(check_source(src).unwrap_err().contains("moved"));
    }
    #[test] fn rejects_conflicting_mutation_in_untaken_if_arm() {
        let src="fn main(){let mut q=qubit();let r=&mut q;if false{h(q);}else{h(r);}h(r);}";
        assert!(check_source(src).unwrap_err().contains("borrow"));
    }
    #[test] fn accepts_nll_last_use_before_new_loan_in_cfg() {
        let src="fn main(){let mut q=qubit();let r=&mut q;h(r);h(q);println!(\"done\");}";
        check_source(src).unwrap();
    }
    #[test] fn rejects_double_consumption_across_loop_iterations() {
        let src="fn main(){let q=qubit();let mut i=0;while i<2{measure(q);i+=1;}}";
        assert!(check_source(src).unwrap_err().contains("moved"));
    }
    #[test] fn reborrow_chain_with_scoped_child_is_valid() {
        let src="fn main(){let mut q=qubit();let a=&mut q;{let b=&mut *a;h(b);}h(a);}";
        check_source(src).unwrap();
    }
    #[test] fn host_assign_conflicts_with_live_borrow_even_in_false_branch() {
        let src="fn main(){let mut x=0;let r=&x;if false{x=2;}println!(\"{}\",r);}";
        assert!(check_source(src).unwrap_err().contains("borrow"));
    }
    #[test] fn unknown_effectful_call_cannot_get_empty_mir_certificate() {
        let src="fn main(){println!(\"ok\");if false{unknown_effect();}}";
        assert!(check_source(src).unwrap_err().contains("unsupported hybrid call"));
    }
    #[test] fn quantum_only_fast_path_remains_separate() {
        assert!(!super::super::is_host_source("let q=qubit();h(q);measure(q);"));
    }
    #[test] fn mutable_reference_move_preserves_exclusive_capability() {
        check_source("fn main(){let mut q=qubit();let r=&mut q;let s=r;h(s);}").unwrap();
    }
    #[test] fn stale_reference_binding_cannot_be_used_after_move() {
        let s="fn main(){let mut q=qubit();let r=&mut q;let s=r;h(r);h(s);}";
        assert!(check_source(s).unwrap_err().contains("moved"));
    }
    #[test] fn moved_reference_cannot_be_dereferenced_in_host_expression() {
        let s=r#"fn main(){let mut x=1;let r=&mut x;let s=r;println!("{}",*r);}"#;
        assert!(check_source(s).unwrap_err().contains("moved"));
    }
    #[test] fn moved_reference_cannot_be_reborrowed() {
        let s="fn main(){let mut q=qubit();let r=&mut q;let s=r;let t=&mut *r;h(s);}";
        assert!(check_source(s).unwrap_err().contains("moved"));
    }
    #[test] fn reborrow_of_live_reference_still_passes() {
        let s="fn main(){let mut q=qubit();let r=&mut q;{let s=&mut *r;h(s);}h(r);}";
        check_source(s).unwrap();
    }

}
