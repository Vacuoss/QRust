//Typed, compilation-local MIR for ownership-sensitive QRust host functions
use std::collections::{HashMap,HashSet,VecDeque};
use std::sync::Arc;
use std::ops::Range;
use crate::{syntax::{Token,TokenKind as K},ids::SymbolId,
    ir::{ConstType,TypeId,FieldId},cfg_borrow::{self,Access,Event,Path,FieldKey}};

const LIMIT:usize=8192;
#[derive(Debug,Clone)]
pub enum Statement {
    Access(Event),
    //A call is one MIR operation containing its ordered, type-checked receiver reservation, argument
    //evaluations and activation events
    Call {name:String,token:usize,events:Vec<Event>,
        effects:Vec<VerifiedAppliedEffect>,
        //Callee alternatives must remain separate execution traces and each case is type-checked
        path_cases:Vec<VerifiedAppliedPathCase>},
    //Explicit storage lifetime boundaries and destruction in the typed MIR
    StorageLive(Event),StorageDead(Event),Drop(Event),
    HostOperation {name:String,events:Vec<Event>},
    QuantumOperation {name:String,events:Vec<Event>},
    LatePhiReborrow {ty:ConstType,source_generation:SymbolId,
        generation:SymbolId,children:Vec<RefOption>,event:Event,
        projection:Option<FieldKey>},
    ValuePhi {ty:ConstType, predecessors:Vec<usize>,check:Event,
        generation:Option<SymbolId>,
        provenance:Option<(Path,bool,Option<SymbolId>)>,
        alternatives:Vec<RefOption>},
}
#[derive(Debug,Clone,PartialEq,Eq)]
pub enum Terminator {Goto(Vec<usize>), Return}
#[derive(Debug,Clone)]
pub struct BasicBlock {pub statements:Vec<Statement>,pub terminator:Terminator}
#[derive(Debug)]
pub struct FunctionMir {pub blocks:Vec<BasicBlock>,pub entry:usize,pub loans:HashMap<SymbolId,Path>}
impl Statement {
    pub(crate) fn verified_effects(&self)->&[VerifiedAppliedEffect]{match self {
        Statement::Call{effects,..}=>effects.as_slice(),
        _=>&[],
    }}
    pub(crate) fn events(&self)->&[Event]{match self {
        Statement::Access(e)|Statement::StorageLive(e)|Statement::StorageDead(e)|Statement::Drop(e)
            =>std::slice::from_ref(e),
        Statement::Call{events,..}|Statement::HostOperation{events,..}|
            Statement::QuantumOperation{events,..}=>events.as_slice(),
        Statement::ValuePhi{check,..}=>std::slice::from_ref(check),
        Statement::LatePhiReborrow{event,..}=>std::slice::from_ref(event),
    }}
}
#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub struct RefOption {pub loan:SymbolId,pub path:Path,pub exclusive:bool,
    pub parent:Option<SymbolId>}
#[derive(Clone)]
struct Binding {id:SymbolId,ty:ConstType,reference:Option<(Path,bool)>,
    loan:Option<SymbolId>,borrow_parent:Option<SymbolId>,
    alternatives:Vec<RefOption>,phi_generation:Option<SymbolId>,mutable:bool}

#[derive(Debug,Clone,Copy,PartialEq,Eq,Hash)]
pub enum VerifiedEffectKind {Move,Write,Drop}
#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub struct VerifiedParameterEffect {
    pub parameter:usize,
    pub fields:Vec<FieldKey>,
    pub kind:VerifiedEffectKind,
}
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct VerifiedAppliedEffect {
    pub path:Path,
    pub kind:VerifiedEffectKind,
    pub alternatives:Vec<Path>,
}

#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub struct VerifiedParameterPath {
    pub parameter:usize,
    pub fields:Vec<FieldKey>,
}
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct VerifiedPathCase {
    pub effects:Vec<VerifiedParameterEffect>,
    pub returned:Option<usize>,
    //Exact uninitialized formal MovePaths on this particular return branch. This is proof metadata, never a
    //second ownership transfer
    pub uninitialized:Vec<VerifiedParameterPath>,
}
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct VerifiedAppliedPathCase {
    pub effects:Vec<VerifiedAppliedEffect>,
    pub returned:Option<usize>,
    pub uninitialized:Vec<Path>,
}

#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub struct VerifiedFieldWrite {
    pub parameter:usize,
    pub fields:Vec<FieldKey>,
}

#[derive(Debug,Clone)]
pub struct VerifiedReturnedReference {
    pub parameter:usize,
    pub fields:Vec<FieldKey>,
    pub ty:ConstType,
}

#[derive(Debug,Clone)]
pub struct VerifiedCallSummary {
    pub parameters:Vec<ConstType>,
    pub field_writes:Vec<VerifiedFieldWrite>,
    //Closed, proof-carrying transitive effects. Never guessed for unsupported calls, generic instantiations
    //or unverified bodies
    pub parameter_effects:Vec<VerifiedParameterEffect>,
    pub returned:Option<VerifiedReturnedReference>,
    pub returned_alternatives:Vec<VerifiedReturnedReference>,
    //Feasible (effect, return-origin) pairs after bounded CFG traversal Empty means the proof is
    //unavailable and MAY checking is mandatory
    pub path_cases:Vec<VerifiedPathCase>,
}

pub struct Schema<'a> {
    //Exact variants of declared enums, including positional payload variants MIR does not infer
    //exhaustiveness from arms that happen to be present
    pub enums:&'a HashMap<String,Vec<String>>,
    pub enum_payloads:&'a HashMap<String,Vec<Vec<ConstType>>>,
    pub types:&'a HashMap<String,Vec<(String,ConstType)>>,
    pub type_ids:&'a HashMap<String,TypeId>,
    pub type_names:&'a [String],
    pub methods:&'a HashMap<(TypeId,String),(bool,usize,ConstType)>,
    pub verified_effects:&'a HashMap<String,(bool,Vec<Access>)>,
}
struct Builder<'a,'s> {
    tokens:&'a [Token<'a>], schema:&'s Schema<'s>,
    verified_calls:&'s HashMap<String,VerifiedCallSummary>, blocks:Vec<BasicBlock>,
    scopes:Vec<HashMap<String,Binding>>,loans:HashMap<SymbolId,Path>,
    next_temp:u32, unsupported:bool, copy_generics:HashSet<String>, failure:Option<String>,
    nested_call_depth:usize,
}
impl<'a,'s> Builder<'a,'s> {
    fn kind(&self,i:usize)->Option<K<'a>>{self.tokens.get(i).map(|t|t.kind)}
    fn block(&mut self)->Result<usize,String>{
        if self.blocks.len()>=LIMIT{return Err("typed MIR block limit exceeded".into());}
        let id=self.blocks.len();self.blocks.push(BasicBlock{statements:Vec::new(),terminator:Terminator::Goto(Vec::new())});Ok(id)
    }
    fn link(&mut self,from:&[usize],to:usize){
        for &id in from {if let Terminator::Goto(next)=&mut self.blocks[id].terminator {
            if !next.contains(&to){next.push(to);}
        }}
    }
    fn add(&mut self,from:Vec<usize>,stmts:Vec<Statement>)->Result<Vec<usize>,String>{
        let id=self.block()?;self.link(&from,id);self.blocks[id].statements=stmts;Ok(vec![id])
    }
    fn lookup(&self,name:&str)->Option<Binding>{
        self.scopes.iter().rev().find_map(|scope|scope.get(name).cloned())
    }
    fn lookup_ref_by_id(&self,id:SymbolId)->Option<(Path,bool)>{
        self.scopes.iter().rev().flat_map(|s|s.values())
            .find(|b|b.loan==Some(id)).and_then(|b|b.reference.clone())
    }
    fn ty_id(&self,ty:&ConstType)->Option<TypeId>{match ty {
        ConstType::Named(name)=>self.schema.type_ids.get(name).copied(),
        ConstType::Resolved(id)=>Some(*id),_=>None,
    }}
    fn field(&self,ty:&ConstType,name:&str)->Option<(FieldKey,ConstType)>{
        let id=self.ty_id(ty)?;
        let name_of_type=self.schema.type_names.get(id.0 as usize)?;
        let (index,(_,ty))=self.schema.types.get(name_of_type)?
            .iter().enumerate().find(|(_, (n,_))|n==name)?;
        Some((FieldKey{aggregate:id,field:FieldId(index as u32)},ty.clone()))
    }
    fn project_verified(&self,root:&Path,ty:&ConstType,
        fields:&[FieldKey])->Option<(Path,ConstType)>{
        let mut path=root.clone();
        let mut current=ty.clone();
        if fields.len()>16{return None;}
        for key in fields {
            if self.ty_id(&current)!=Some(key.aggregate){return None;}
            let type_name=self.schema.type_names.get(key.aggregate.0 as usize)?;
            let (_,next)=self.schema.types.get(type_name)?
                .get(key.field.0 as usize)?;
            path=path.child(*key);
            current=next.clone();
        }
        Some((path,current))
    }
    fn resolve_path(&self,lo:usize,hi:usize)->Option<(Path,ConstType,Option<SymbolId>)>{
        let K::Ident(name)=self.kind(lo)? else{return None;};
        let binding=self.lookup(name)?;
        //A PHI reference has several conditional referents. It cannot be lowered as a concrete path or copied
        //by guessing one alternative
        if !binding.alternatives.is_empty(){return None;}
        if binding.reference.is_some() && hi==lo+1{return None;}
        let mut path=Path::root(binding.id);
        let bare_formal_reference=binding.reference.is_none();
        let mut ty=binding.ty;
        let via=binding.reference.as_ref().and(binding.loan);
        if let Some((reference,_))=binding.reference {path=reference;
            ty=match ty {ConstType::Ref(inner)|ConstType::RefMut(inner)=>*inner,_=>return None};
        }
        let mut i=lo+1;
        if i<hi && self.kind(i)==Some(K::Dot) && bare_formal_reference {
            let implicit_pointee=match &ty {
                ConstType::Ref(inner)|ConstType::RefMut(inner)=>Some((**inner).clone()),
                _=>None,
            };
            if let Some(pointee)=implicit_pointee {ty=pointee;}
        }
        while i<hi {
            if self.kind(i)!=Some(K::Dot){return None;}
            let K::Ident(field_name)=self.kind(i+1)? else{return None;};
            let (key,next_ty)=self.field(&ty,field_name)?;
            path=path.child(key);ty=next_ty;i+=2;
        }
        Some((path,ty,via))
    }
    fn event(&self,op:Access,path:Path,loan:Option<SymbolId>,token:usize)->Statement{
        Statement::Access(Event{op,path,loan,parent:None,token})
    }
    fn same_type(&self,left:&ConstType,right:&ConstType)->bool {
        if left==right {return true;}
        match (left,right) {
            (ConstType::Named(name),ConstType::Resolved(id))|
            (ConstType::Resolved(id),ConstType::Named(name))=>self.schema.type_ids.get(name)==Some(id),
            (ConstType::Ref(a),ConstType::Ref(b))|
            (ConstType::RefMut(a),ConstType::RefMut(b))=>self.same_type(a,b),
            _=>false,
        }
    }
    fn is_copy(&self,ty:&ConstType)->bool {
        matches!(ty,ConstType::I64|ConstType::U64|ConstType::Bool|ConstType::Ref(_)) ||
            matches!(ty,ConstType::Generic(name) if self.copy_generics.contains(name))
    }
    fn close(&self,from:usize,end:usize,open:K<'a>,close:K<'a>)->Option<usize>{
        if self.kind(from)!=Some(open){return None;}
        let mut depth=0usize;
        for at in from..end {let k=self.kind(at)?;
            if k==open{depth+=1;}else if k==close{depth-=1;if depth==0{return Some(at);}}
        }None
    }
    fn split_top(&self,start:usize,end:usize,delimiter:K<'a>)->Vec<Range<usize>> {
        let mut out=Vec::new();let mut begin=start;
        let (mut par,mut brace,mut bracket)=(0usize,0usize,0usize);
        for i in start..end {match self.kind(i){
            Some(K::LParen)=>par+=1,Some(K::RParen)=>par=par.saturating_sub(1),
            Some(K::LBrace)=>brace+=1,Some(K::RBrace)=>brace=brace.saturating_sub(1),
            Some(K::LBracket)=>bracket+=1,Some(K::RBracket)=>bracket=bracket.saturating_sub(1),
            Some(k) if k==delimiter&&par==0&&brace==0&&bracket==0=>{
                if begin<i{out.push(begin..i);}begin=i+1;
            },_=>(),}}
        if begin<end{out.push(begin..end);}out
    }
    fn temp_id(&mut self)->Option<SymbolId>{
        self.next_temp=self.next_temp.checked_add(1)?;Some(SymbolId(self.next_temp))
    }
    fn phi_generation(&self,tails:&[usize],binding:SymbolId)->Option<SymbolId>{
        let &[node]=tails else{return None};
        self.blocks.get(node)?.statements.iter().rev().find_map(|stmt|match stmt {
            Statement::ValuePhi{check,generation,..} if check.path==Path::root(binding)=>*generation,
            _=>None,
        })
    }
    fn verified_user_call(&mut self,start:usize,end:usize,name:&str,
        summary:VerifiedCallSummary)
        ->Option<(Vec<Statement>,ConstType,Option<(Path,bool,Option<SymbolId>)>)> {
        self.verified_user_call_on_edge(start,end,name,summary,None)
    }
    fn emit_actual_argument(ordered:bool,prelude:&mut Vec<Statement>,
        boundary:&mut Vec<Event>,event:Event){
        if ordered {prelude.push(Statement::Access(event));}
        else {boundary.push(event);}
    }
    fn verified_user_call_on_edge(&mut self,start:usize,end:usize,name:&str,
        summary:VerifiedCallSummary,selected:Option<&[(SymbolId,RefOption)]>)
        ->Option<(Vec<Statement>,ConstType,Option<(Path,bool,Option<SymbolId>)>)> {
        let args=self.split_top(start+2,end-1,K::Comma);
        if args.len()!=summary.parameters.len(){return None;}
        let ordered_args=args.iter().skip(1).any(|arg|
            matches!(self.kind(arg.start),Some(K::Ident(_))) &&
            self.kind(arg.start+1)==Some(K::LParen) &&
            self.close(arg.start+1,arg.end,K::LParen,K::RParen)==Some(arg.end-1));
        let effectful_outer=!summary.field_writes.is_empty() ||
            !summary.parameter_effects.is_empty() ||
            summary.path_cases.iter().any(|case|
                !case.effects.is_empty() || !case.uninitialized.is_empty());
        if ordered_args && effectful_outer {
            let may=summary.parameter_effects.iter().cloned().collect::<HashSet<_>>();
            let witnessed=summary.path_cases.iter().flat_map(|case|
                case.effects.iter().cloned()).collect::<HashSet<_>>();
            if selected.is_some() || !summary.returned_alternatives.is_empty() ||
                summary.parameters.iter().any(|ty|
                    !matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_))) ||
                summary.path_cases.is_empty() || summary.path_cases.len()>128 ||
                may!=witnessed || may.is_empty() ||
                summary.parameter_effects.iter().any(|effect|
                    effect.kind!=VerifiedEffectKind::Write || effect.fields.is_empty() ||
                    !matches!(summary.parameters.get(effect.parameter),Some(ConstType::RefMut(_)))) ||
                summary.field_writes.iter().any(|effect|
                    !may.contains(&VerifiedParameterEffect{
                        parameter:effect.parameter,fields:effect.fields.clone(),
                        kind:VerifiedEffectKind::Write,
                    })) ||
                summary.path_cases.iter().any(|case|
                    !case.uninitialized.is_empty() ||
                    case.returned!=summary.returned.as_ref().map(|_|0) ||
                    case.effects.iter().any(|effect|!may.contains(effect))) {
                return None;
            }
        }
        let mut events=Vec::with_capacity(args.len()*3+summary.field_writes.len());
        let mut applied_effects=Vec::with_capacity(summary.parameter_effects.len());
        let mut owned_actuals=vec![None;args.len()];
        let mut phi_actuals:Vec<Option<(Path,ConstType,SymbolId,Vec<RefOption>)>>=
            vec![None;args.len()];
        //(real referent, pointee type, temporary loan, original reference parent). A parameter is mapped only
        //if its actual has been completely type-checked as a borrow
        let mut referents:Vec<Option<(Path,ConstType,SymbolId,Option<SymbolId>)>>=
            vec![None;args.len()];
        let mut borrowed=Vec::new();
        let mut prelude=Vec::<Statement>::new();
        let mut nested_results=Vec::<(usize,SymbolId,Path,bool)>::new();
        for (index,(arg,formal)) in args.iter().zip(&summary.parameters).enumerate() {
            match formal {
                ConstType::Ref(inner)|ConstType::RefMut(inner) => {
                    let exclusive=matches!(formal,ConstType::RefMut(_));
                    let (path,actual,parent)=if self.kind(arg.start)==Some(K::Amp) {
                        let mut at=arg.start+1;
                        let mut_mut=self.kind(at)==Some(K::Ident("mut"));
                        if mut_mut{at+=1;}
                        if mut_mut!=exclusive{return None;}
                        let (path,ty,parent)=self.resolve_path(at,arg.end)?;
                        if exclusive {
                            let K::Ident(root)=self.kind(at)? else{return None;};
                            let owner=self.lookup(root)?;
                            let through_mut=matches!(owner.ty,ConstType::RefMut(_)) &&
                                self.kind(at+1)==Some(K::Dot);
                            if !owner.mutable && owner.reference.is_none() && !through_mut {
                                return None;
                            }
                        }
                        (path,ty,parent)
                    }else if arg.end==arg.start+1 {
                        let K::Ident(source)=self.kind(arg.start)? else{return None;};
                        let binding=self.lookup(source)?;
                        if !self.same_type(&binding.ty,formal){return None;}
                        if let Some((source_id,option))=selected.and_then(|choices|
                            choices.iter().find(|(source_id,_)|*source_id==binding.id)) {
                            //The original PHI binding still contains its parent loan until all alternatives have been constructed
                            let original=binding.alternatives.contains(option);
                            let verified_child=binding.phi_generation.is_some() &&
                                binding.alternatives.iter().any(|base|
                                    option.loan!=base.loan &&
                                    option.parent==Some(base.loan) &&
                                    option.path==base.path &&
                                    option.exclusive==base.exclusive &&
                                    self.loans.get(&base.loan)==Some(&base.path));
                            if *source_id!=binding.id ||
                                (!original && !verified_child) ||
                                option.exclusive!=exclusive ||
                                self.loans.get(&option.loan)!=Some(&option.path) {
                                return None;
                            }
                            (option.path.clone(),*inner.clone(),Some(option.loan))
                        }else if !binding.alternatives.is_empty() {
                            let nonreturned=summary.returned.as_ref()
                                .is_some_and(|origin|origin.parameter!=index);
                            if (summary.returned.is_some() && !nonreturned) ||
                                !summary.returned_alternatives.is_empty() ||
                                summary.parameter_effects.iter().any(|effect|
                                    effect.parameter==index &&
                                    (effect.kind!=VerifiedEffectKind::Write ||
                                        !exclusive || effect.fields.is_empty())) ||
                                summary.field_writes.iter().any(|effect|
                                    effect.parameter==index &&
                                    (!exclusive || effect.fields.is_empty())) ||
                                summary.path_cases.iter().any(|case|
                                    case.uninitialized.iter().any(|path|
                                        path.parameter==index)) {
                                return None;
                            }
                            if binding.alternatives.len()>32 ||
                                binding.alternatives.iter().any(|candidate|
                                    candidate.exclusive!=exclusive ||
                                    self.loans.get(&candidate.loan)!=Some(&candidate.path)) {
                                return None;
                            }
                            let generation=binding.phi_generation?;
                            let phi_path=Path::root(binding.id);
                            phi_actuals[index]=Some((phi_path.clone(),*inner.clone(),
                                generation,binding.alternatives.clone()));
                            Self::emit_actual_argument(ordered_args,&mut prelude,&mut events,
                                Event{op:Access::Read,path:phi_path.clone(),
                                    loan:Some(generation),parent:None,token:arg.start});
                            if exclusive {
                                Self::emit_actual_argument(ordered_args,&mut prelude,&mut events,
                                    Event{op:Access::Write,path:phi_path.clone(),
                                        loan:Some(generation),parent:None,token:arg.start});
                                if ordered_args && effectful_outer {
                                    events.push(Event{op:Access::Write,path:phi_path,
                                        loan:Some(generation),parent:None,token:start});
                                }
                            }
                            //No fabricated temporary borrow of one candidate: the source PHI's exact loans already enforce all
                            //alias and lifetime restrictions
                            continue;
                        }else if let Some((path,source_mut))=binding.reference {
                            if exclusive && !source_mut {return None;}
                            (path,*inner.clone(),binding.loan)
                        }else{
                            (Path::root(binding.id),*inner.clone(),None)
                        }
                    }else if let (Some(K::Ident(inner_name)),Some(K::LParen))=
                        (self.kind(arg.start),self.kind(arg.start+1)) {
                        if self.close(arg.start+1,arg.end,K::LParen,K::RParen)
                                !=Some(arg.end-1) || self.nested_call_depth>=16 {
                            return None;
                        }
                        let nested=self.verified_calls.get(inner_name)?.clone();
                        if !nested.returned_alternatives.is_empty() ||
                            nested.returned.is_none() {return None;}
                        self.nested_call_depth+=1;
                        let result=self.verified_user_call_on_edge(
                            arg.start,arg.end,inner_name,nested,selected);
                        self.nested_call_depth-=1;
                        let (statements,returned_ty,returned)=result?;
                        if !self.same_type(&returned_ty,formal){return None;}
                        let (path,returned_mut,parent)=returned?;
                        if exclusive && !returned_mut {return None;}
                        let loan=self.temp_id()?;
                        self.loans.insert(loan,path.clone());
                        prelude.extend(statements);
                        prelude.push(Statement::Access(Event{
                            op:if returned_mut{Access::BorrowMut}else{Access::BorrowShared},
                            path:path.clone(),loan:Some(loan),parent,token:arg.start,
                        }));
                        nested_results.push((index,loan,path.clone(),returned_mut));
                        (path,*inner.clone(),Some(loan))
                    }else{return None;};
                    if !self.same_type(&actual,inner){return None;}
                    if let Some(source)=parent {
                        let source_mut=if let Some((_,candidate))=selected.and_then(|choices|
                            choices.iter().find(|(_,candidate)|candidate.loan==source)) {
                            candidate.exclusive
                        }else if let Some((_,_,_,mutable))=nested_results.iter()
                            .find(|(_,id,_,_)|*id==source) {
                            *mutable
                        }else{
                            self.lookup_ref_by_id(source)?.1
                        };
                        if exclusive && !source_mut{return None;}
                    }
                    let loan=self.temp_id()?;
                    Self::emit_actual_argument(ordered_args,&mut prelude,&mut events,
                        Event{op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
                            path:path.clone(),loan:Some(loan),parent,token:arg.start});
                    self.loans.insert(loan,path.clone());
                    referents[index]=Some((path.clone(),actual,loan,parent));
                    borrowed.push((loan,path));
                }
                _=>{
                    //Compile-time primitive literals have no owned MIR place. Their evaluation is effect-free, but their
                    //exact type must still match the formal parameter
                    let literal=arg.end==arg.start+1 && match self.kind(arg.start) {
                        Some(K::Ident("true"|"false"))=>*formal==ConstType::Bool,
                        Some(K::Number(_))=>matches!(formal,ConstType::I64|ConstType::U64),
                        _=>false,
                    };
                    if literal {continue;}
                    let (path,actual,via)=self.resolve_path(arg.start,arg.end)?;
                    if via.is_some() || !self.same_type(&actual,formal){return None;}
                    let op=if self.is_copy(formal){Access::Read}else{Access::Move};
                    owned_actuals[index]=Some((path.clone(),actual));
                    Self::emit_actual_argument(ordered_args,&mut prelude,&mut events,
                        Event{op,path,loan:None,parent:None,token:arg.start});
                }
            }
        }
        //Every MAY write through a formal &mut MUST still be checked on the caller's actual MovePath
        let mut checked_writes=HashSet::<(usize,Vec<FieldKey>)>::new();
        //The callee's may-writes must be legal under the actual exclusive loan and any simultaneously borrowed
        //siblings A shared reference can never acquire write authority
        for effect in &summary.field_writes {
            let formal=summary.parameters.get(effect.parameter)?;
            if !matches!(formal,ConstType::RefMut(_)) || effect.fields.is_empty(){
                return None;
            }
            if let Some((_,pointee,_,options))=phi_actuals.get(effect.parameter)?.as_ref() {
                for candidate in options {
                    self.project_verified(&candidate.path,pointee,&effect.fields)?;
                }
                checked_writes.insert((effect.parameter,effect.fields.clone()));
            }else{
                let (base,ty,loan,_) = referents.get(effect.parameter)?.as_ref()?;
                let (target,_)=self.project_verified(base,ty,&effect.fields)?;
                if checked_writes.insert((effect.parameter,effect.fields.clone())) {
                    events.push(Event{op:Access::Write,path:target,loan:Some(*loan),
                        parent:None,token:start});
                }
            }
        }
        for effect in &summary.parameter_effects {
            let formal=summary.parameters.get(effect.parameter)?;
            if let Some((root,pointee,_,options))=phi_actuals.get(effect.parameter)?.as_ref() {
                if effect.kind!=VerifiedEffectKind::Write ||
                    !matches!(formal,ConstType::RefMut(_)) || effect.fields.is_empty() {
                    return None;
                }
                let mut alternatives=Vec::with_capacity(options.len());
                for candidate in options {
                    let (target,_)=self.project_verified(&candidate.path,pointee,&effect.fields)?;
                    alternatives.push(target);
                }
                applied_effects.push(VerifiedAppliedEffect{
                    path:root.clone(),kind:VerifiedEffectKind::Write,alternatives});
                checked_writes.insert((effect.parameter,effect.fields.clone()));
                continue;
            }
            let (root,ty)=match formal {
                ConstType::RefMut(_) if effect.kind==VerifiedEffectKind::Write => {
                    let (root,ty,_,_)=referents.get(effect.parameter)?.as_ref()?;
                    (root,ty)
                }
                ConstType::Ref(_) | ConstType::RefMut(_) => return None,
                _ => {
                    let (root,ty)=owned_actuals.get(effect.parameter)?.as_ref()?;
                    (root,ty)
                }
            };
            let (path,_) = self.project_verified(root,ty,&effect.fields)?;
            if matches!(formal,ConstType::RefMut(_)) &&
                effect.kind==VerifiedEffectKind::Write {
                if effect.fields.is_empty(){return None;}
                if checked_writes.insert((effect.parameter,effect.fields.clone())) {
                    let (_,_,loan,_)=referents.get(effect.parameter)?.as_ref()?;
                    events.push(Event{op:Access::Write,path:path.clone(),
                        loan:Some(*loan),parent:None,token:start});
                }
            }
            applied_effects.push(VerifiedAppliedEffect{path,kind:effect.kind,
                alternatives:Vec::new()});
        }
        if !summary.path_cases.is_empty() {
            let exhaustive=summary.path_cases.iter()
                .flat_map(|case|case.effects.iter().cloned())
                .collect::<HashSet<_>>();
            if exhaustive!=summary.parameter_effects.iter().cloned()
                .collect::<HashSet<_>>() {return None;}
        }
        //Effect cases remain paired with their returned PHI origin; missing witnesses are not
        //accepted as proof
        let mut path_cases=Vec::with_capacity(summary.path_cases.len());
        for case in &summary.path_cases {
            let legal_origin=if summary.returned.is_some(){case.returned==Some(0)}
                else if !summary.returned_alternatives.is_empty(){
                    case.returned.is_some_and(|index|index<summary.returned_alternatives.len())
                }else{case.returned.is_none()};
            if !legal_origin{return None;}
            let mut real=Vec::with_capacity(case.effects.len());
            for proof in &case.effects {
                let Some(index)=summary.parameter_effects.iter().position(|e|e==proof)
                    else{return None};
                real.push(applied_effects[index].clone());
            }
            let mut uninitialized=Vec::with_capacity(case.uninitialized.len());
            for proof in &case.uninitialized {
                let formal=summary.parameters.get(proof.parameter)?;
                if matches!(formal,ConstType::Ref(_)|ConstType::RefMut(_)) {
                    return None;
                }
                let (root,ty)=owned_actuals.get(proof.parameter)?.as_ref()?;
                let (path,_)=self.project_verified(root,ty,&proof.fields)?;
                if !case.effects.iter().any(|effect|
                    effect.parameter==proof.parameter &&
                    matches!(effect.kind,VerifiedEffectKind::Move|VerifiedEffectKind::Drop) &&
                    effect.fields.len()<=proof.fields.len() &&
                    effect.fields.iter().zip(&proof.fields).all(|(a,b)|a==b)) {
                    return None;
                }
                if !uninitialized.contains(&path){uninitialized.push(path);}
            }
            path_cases.push(VerifiedAppliedPathCase{effects:real,
                returned:case.returned,uninitialized});
        }
        //Exact single-origin return: source lifetime and mutability have already been universally proved in
        //ReferenceSummarySolver
        let (result,returned)=if let Some(origin)=&summary.returned {
            let formal=summary.parameters.get(origin.parameter)?;
            let (base,ty,_,parent)=referents.get(origin.parameter)?.as_ref()?;
            let (target,pointee)=self.project_verified(base,ty,&origin.fields)?;
            let (expected,mutability)=match &origin.ty {
                ConstType::Ref(inner)=>(inner.as_ref(),false),
                ConstType::RefMut(inner)=>(inner.as_ref(),true),
                _=>return None,
            };
            if mutability && !matches!(formal,ConstType::RefMut(_)) ||
                !self.same_type(&pointee,expected) {return None;}
            (origin.ty.clone(),Some((target,mutability,*parent)))
        }else{(ConstType::Unit,None)};
        for (loan,path) in borrowed.into_iter().rev() {
            events.push(Event{op:Access::EndLoan,path,loan:Some(loan),parent:None,token:start});
        }
        let retained=returned.as_ref().and_then(|(_,_,parent)|*parent);
        prelude.push(Statement::Call{name:name.to_owned(),token:start,events,
            effects:applied_effects,path_cases});
        for (_,loan,path,_) in nested_results.into_iter().rev() {
            if Some(loan)!=retained {
                prelude.push(Statement::Access(Event{op:Access::EndLoan,
                    path,loan:Some(loan),parent:None,token:start}));
            }
        }
        Some((prelude,result,returned))
    }
    fn expr(&mut self,start:usize,end:usize)->Option<(Vec<Statement>,ConstType,Option<(Path,bool,Option<SymbolId>)>)>{
        if start>=end{return None;}
        if self.kind(start)==Some(K::Amp){
            let exclusive=self.kind(start+1)==Some(K::Ident("mut"));
            let at=start+1+usize::from(exclusive);
            if exclusive && self.kind(at)!=Some(K::Star) {
                if let Some(K::Ident(name))=self.kind(at) {
                    if let Some(binding)=self.lookup(name) {
                        let mutable_receiver=matches!(&binding.ty,ConstType::RefMut(_)) &&
                            self.kind(at+1)==Some(K::Dot);
                        if !binding.mutable && binding.reference.is_none() && !mutable_receiver {
                            self.failure=Some(format!(
                                "cannot mutably borrow immutable binding '{name}'"));
                            return None;
                        }
                    }
                }
            }
            let (path,ty,parent)=if self.kind(at)==Some(K::Star) {
                //&*r and &mut *r create a new loan with the provenance of r; they never move the referenced value
                if end!=at+2 {return None;}
                let K::Ident(name)=self.kind(at+1)? else{return None;};
                let binding=self.lookup(name)?;
                let (path,mutable)=binding.reference?;
                if exclusive && !mutable{return None;}
                let ty=match binding.ty{ConstType::Ref(inner)|ConstType::RefMut(inner)=>*inner,_=>return None};
                (path,ty,binding.loan)
            }else{
                self.resolve_path(at,end)?
            };
            if let Some(id)=parent {
                let base=self.lookup_ref_by_id(id)?;
                if exclusive && !base.1{return None;}
            }
            let ty=if exclusive{ConstType::RefMut(Box::new(ty))}else{ConstType::Ref(Box::new(ty))};
            return Some((Vec::new(),ty,Some((path,exclusive,parent))));
        }
        if let (Some(K::Ident(name)),Some(K::Dot),Some(K::Ident(method)),Some(K::LParen))=
            (self.kind(start),self.kind(start+1),self.kind(start+2),self.kind(start+3)) {
            if self.close(start+3,end,K::LParen,K::RParen)==Some(end-1) {
                let binding=self.lookup(name)?;
                if binding.reference.is_some(){return None;}
                let owner=self.ty_id(&binding.ty)?;
                let (mutability,arity,result)=self.schema.methods.get(&(owner,method.to_owned()))?.clone();
                let arguments=self.split_top(start+4,end-1,K::Comma);
                if arguments.len()+1!=arity {return None;}
                let path=Path::root(binding.id);
                let mut operations=Vec::new();
                let mut call_events=Vec::new();
                let receiver_id=self.temp_id()?;
                if mutability {
                    call_events.push(Event{op:Access::ReserveMut,path:path.clone(),loan:Some(receiver_id),parent:None,token:start});
                }else{
                    call_events.push(Event{op:Access::BorrowShared,path:path.clone(),loan:Some(receiver_id),parent:None,token:start});
                }
                for arg in arguments {
                    let (parts,_,_)=self.expr(arg.start,arg.end)?;
                    for item in parts {
                        match item {
                            Statement::Access(e)|Statement::StorageLive(e)|Statement::StorageDead(e)|Statement::Drop(e)=>call_events.push(e),
                            Statement::Call{events,..}|Statement::HostOperation{events,..}|
                                Statement::QuantumOperation{events,..}=>call_events.extend(events),
                            Statement::ValuePhi{check,..}=>call_events.push(check),
                            //A late PHI reborrow is relational: its selected parent and all child alternatives must be registered
                            //together
                            Statement::LatePhiReborrow{..}=>return None,
                        }
                    }
                }
                if mutability {
                    call_events.push(Event{op:Access::ActivateMut,path:path.clone(),loan:Some(receiver_id),parent:None,token:start});
                }
                call_events.push(Event{op:Access::EndLoan,path,loan:Some(receiver_id),parent:None,token:start});
                operations.push(Statement::Call{name:method.to_owned(),token:start,
                    events:call_events,effects:Vec::new(),path_cases:Vec::new()});
                return Some((operations,result,None));
            }
        }
        if let (Some(K::Ident(name)),Some(K::LParen))=(self.kind(start),self.kind(start+1)) {
            if self.close(start+1,end,K::LParen,K::RParen)==Some(end-1) {
                if let Some((quantum,effects))=self.schema.verified_effects.get(name).cloned() {
                    let args=self.split_top(start+2,end-1,K::Comma);
                    if args.len()!=effects.len(){return None;}
                    let mut events=Vec::with_capacity(args.len());
                    for (arg,op) in args.into_iter().zip(effects) {
                        if !matches!(op,Access::Read|Access::Move|Access::Write|Access::Drop){return None;}
                        let (path,ty,via)=self.resolve_path(arg.start,arg.end)?;
                        if via.is_some() && matches!(op,Access::Move|Access::Drop){return None;}
                        if op==Access::Move && self.is_copy(&ty){return None;}
                        events.push(Event{op,path,loan:via,parent:None,token:arg.start});
                    }
                    if !quantum && name=="drop" && events.len()==1 && events[0].op==Access::Drop {
                        return Some((vec![Statement::Drop(events.remove(0))],ConstType::Unit,None));
                    }
                    let statement=if quantum{
                        Statement::QuantumOperation{name:name.to_owned(),events}
                    }else{Statement::HostOperation{name:name.to_owned(),events}};
                    return Some((vec![statement],ConstType::Unit,None));
                }
            }
        }
        //The verified call proof can also be instantiated once for each possible result provenance by the
        //call-PHI lowering below
        if let (Some(K::Ident(name)),Some(K::LParen))=
            (self.kind(start),self.kind(start+1)) {
            if self.close(start+1,end,K::LParen,K::RParen)==Some(end-1) {
                if let Some(summary)=self.verified_calls.get(name).cloned() {
                    if summary.returned_alternatives.len()>1 { return None; }
                    return self.verified_user_call(start,end,name,summary);
                }
            }
        }
        if let Some(K::Ident(name))=self.kind(start) {
            if let Some(binding)=self.lookup(name) {
                if !binding.alternatives.is_empty() &&
                    self.kind(start+1)==Some(K::Dot) {
                    let mut ty=match &binding.ty {
                        ConstType::Ref(inner)|ConstType::RefMut(inner)=>(**inner).clone(),
                        _=>return None,
                    };
                    let mut at=start+1;
                    while at<end {
                        if self.kind(at)!=Some(K::Dot){return None;}
                        let K::Ident(field)=self.kind(at+1)? else{return None;};
                        let (_,next)=self.field(&ty,field)?;
                        ty=next;at+=2;
                    }
                    if !self.is_copy(&ty){return None;}
                    return Some((vec![self.event(Access::Read,Path::root(binding.id),
                        binding.phi_generation,start)],ty,None));
                }
            }
        }
        if self.kind(start)==Some(K::Star) && end==start+2 {
            let K::Ident(name)=self.kind(start+1)? else{return None;};
            let binding=self.lookup(name)?;
            let ty=match binding.ty {ConstType::Ref(ty)|ConstType::RefMut(ty)=>*ty,_=>return None};
            if !self.is_copy(&ty){return None;}
            if !binding.alternatives.is_empty(){
                binding.phi_generation?;
                return Some((vec![self.event(Access::Read,Path::root(binding.id),
                    binding.phi_generation,start)],ty,None));
            }
            let (path,_)=binding.reference?;
            return Some((vec![self.event(Access::Read,path,binding.loan,start)],ty,None));
        }
        if end==start+1 {
            if let Some(K::Ident(name))=self.kind(start) {
                if let Some(binding)=self.lookup(name) {
                    if let (ConstType::Ref(_),Some((path,false)))=(&binding.ty,&binding.reference) {
                        return Some((vec![self.event(Access::Read,path.clone(),binding.loan,start)],
                            binding.ty.clone(),Some((path.clone(),false,None))));
                    }
                }
            }
        }
        if let Some((path,ty,via))=self.resolve_path(start,end){
            let op=if self.is_copy(&ty){Access::Read}else{Access::Move};
            if via.is_some() && op==Access::Move{return None;}
            return Some((vec![self.event(op,path,via,start)],ty,None));
        }
        if end>=start+4 && self.kind(start+1)==Some(K::Colon) &&
            self.kind(start+2)==Some(K::Colon) {
            if let (Some(K::Ident(owner)),Some(K::Ident(variant)))=
                (self.kind(start),self.kind(start+3)) {
                let index=self.schema.enums.get(owner)?.iter()
                    .position(|name|name.as_str()==variant)?;
                let id=*self.schema.type_ids.get(owner)?;
                let field_types=self.schema.enum_payloads.get(owner)
                    .and_then(|fields|fields.get(index));
                if end==start+4 && field_types.is_none_or(|fields|fields.is_empty()) {
                    return Some((Vec::new(),ConstType::Resolved(id),None));
                }
                let fields=field_types?.clone();
                if fields.is_empty() || self.kind(start+4)!=Some(K::LParen) ||
                    self.close(start+4,end,K::LParen,K::RParen)!=Some(end-1){return None;}
                let args=self.split_top(start+5,end-1,K::Comma);
                if args.len()!=fields.len(){return None;}
                let mut operations=Vec::new();
                for (arg,expected) in args.iter().zip(&fields){
                    let (events,actual,_)=self.expr(arg.start,arg.end)?;
                    let expected_normalized=self.ty_id(expected)
                        .map(ConstType::Resolved).unwrap_or_else(||expected.clone());
                    let actual_normalized=self.ty_id(&actual)
                        .map(ConstType::Resolved).unwrap_or_else(||actual.clone());
                    let contextual_unsigned=*expected==ConstType::U64 &&
                        actual==ConstType::I64 && arg.end==arg.start+1 &&
                        matches!(self.kind(arg.start),Some(K::Number(_)));
                    if actual_normalized!=expected_normalized && !contextual_unsigned{return None;}
                    operations.extend(events);
                }
                return Some((operations,ConstType::Resolved(id),None));
            }
        }
        if end==start+1 {return match self.kind(start)? {
            K::Number(_)=>Some((Vec::new(),ConstType::I64,None)),
            K::Ident("true"|"false")=>Some((Vec::new(),ConstType::Bool,None)),
            _=>None,
        };}
        if self.kind(start)==Some(K::LParen) && self.close(start,end,K::LParen,K::RParen)==Some(end-1){
            return self.expr(start+1,end-1);
        }
        if matches!(self.kind(start),Some(K::Bang|K::Minus|K::Plus)) && start+1<end {
            let (ops,ty,_) = self.expr(start+1,end)?;
            match (self.kind(start)?,&ty){
                (K::Bang,ConstType::Bool)=>return Some((ops,ty,None)),
                (K::Minus|K::Plus,ConstType::I64|ConstType::U64)=>return Some((ops,ty,None)),
                _=>return None,
            }
        }
        if let (Some(K::Ident(name)),Some(K::LBrace))=(self.kind(start),self.kind(start+1)) {
            if self.close(start+1,end,K::LBrace,K::RBrace)==Some(end-1) {
                let id=*self.schema.type_ids.get(name)?;
                let mut statements=Vec::new();
                for pair in self.split_top(start+2,end-1,K::Comma) {
                    if self.kind(pair.start+1)!=Some(K::Colon){return None;}
                    let (part,_,_)=self.expr(pair.start+2,pair.end)?;
                    statements.extend(part);
                }
                return Some((statements,ConstType::Resolved(id),None));
            }
        }
        for i in (start+1..end).rev(){
            if !matches!(self.kind(i),Some(K::Plus|K::Minus|K::Star|K::Slash|K::Percent|K::Less|K::Greater|K::EqEq|K::NotEq|K::LessEq|K::GreaterEq|K::AndAnd|K::OrOr)){continue;}
            let (mut left,lt,_)=self.expr(start,i)?;
            let (right,rt,_)=self.expr(i+1,end)?;
            let same_generic=matches!((&lt,&rt),(ConstType::Generic(a),ConstType::Generic(b)) if a==b);
            if (!self.is_copy(&lt)||!self.is_copy(&rt)) &&
                !(same_generic && matches!(self.kind(i),Some(K::Plus|K::Minus|K::Star|K::Slash|K::Percent))) {
                return None;
            }
            if matches!(self.kind(i),Some(K::AndAnd|K::OrOr)) &&
                !(matches!(&lt,ConstType::Bool)&&matches!(&rt,ConstType::Bool)){return None;}
            left.extend(right);
            let result=if matches!(self.kind(i),Some(K::Less|K::Greater|K::EqEq|K::NotEq|K::LessEq|K::GreaterEq|K::AndAnd|K::OrOr)){
                ConstType::Bool
            }else{lt};
            return Some((left,result,None));
        }
        None
    }
    fn relocate_mut_loan(&mut self,source_name:&str,dest_loan:SymbolId,
        token:usize)->Option<(Vec<Statement>,ConstType,Path,Option<SymbolId>)>{
        let source=self.lookup(source_name)?;
        if !matches!(&source.ty,ConstType::RefMut(_)) || !source.alternatives.is_empty(){return None;}
        let (path,true)=source.reference.clone()? else{return None;};
        let source_loan=source.loan?;
        let parent=source.borrow_parent;
        if source_loan==dest_loan{return None;}
        let events=vec![
            self.event(Access::Read,path.clone(),Some(source_loan),token),
            self.event(Access::Move,Path::root(source.id),None,token),
            self.event(Access::EndLoan,path.clone(),Some(source_loan),token),
            Statement::Access(Event{op:Access::BorrowMut,path:path.clone(),
                loan:Some(dest_loan),parent,token}),
        ];
        self.loans.insert(dest_loan,path.clone());
        Some((events,source.ty,path,parent))
    }
    fn reassign_mut_reference(&mut self,start:usize,end:usize)->Option<Vec<Statement>>{
        let K::Ident(name)=self.kind(start)? else{return None;};
        if self.kind(start+1)!=Some(K::Equal){return None;}
        let old=self.lookup(name)?;
        if !matches!(&old.ty,ConstType::RefMut(_)) || !old.mutable{return None;}
        let retired=if !old.alternatives.is_empty() {
            if old.loan.is_some() || old.reference.is_some() ||
                old.alternatives.iter().any(|option|!option.exclusive) {return None;}
            old.alternatives.iter().map(|option|
                (option.path.clone(),option.loan)).collect::<Vec<_>>()
        } else {
            let (path,true)=old.reference.clone()? else{return None;};
            vec![(path,old.loan?)]
        };
        if !self.scopes.last().is_some_and(|scope|scope.contains_key(name)) {
            self.failure=Some(format!(
                "mutable reference '{name}' reassigned across a CFG scope without provenance PHI"));
            return None;
        }
        if end<=start+2{return None;}
        let new_loan=self.temp_id()?;
        let (mut ops,path,parent)=if end==start+3 {
            let K::Ident(source_name)=self.kind(start+2)? else{return None;};
            if source_name==name{return None;}
            let (ops,ty,path,parent)=self.relocate_mut_loan(source_name,new_loan,start)?;
            if ty!=old.ty{return None;}
            (ops,path,parent)
        }else{
            let (ops,ty,reference)=self.expr(start+2,end)?;
            if ty!=old.ty{return None;}
            let (path,true,parent)=reference? else{return None;};
            let mut ops=ops;
            ops.push(Statement::Access(Event{op:Access::BorrowMut,
                path:path.clone(),loan:Some(new_loan),parent,token:start}));
            self.loans.insert(new_loan,path.clone());
            (ops,path,parent)
        };
        if !old.alternatives.is_empty() {
            let new_borrow=ops.pop()?;
            if !matches!(&new_borrow,Statement::Access(Event{
                op:Access::BorrowMut,loan:Some(id),..}) if *id==new_loan) {return None;}
            for (path,id) in retired {
                ops.push(self.event(Access::EndLoan,path,Some(id),start));
            }
            ops.push(new_borrow);
        } else {
            for (path,id) in retired {
                ops.push(self.event(Access::EndLoan,path,Some(id),start));
            }
        }
        ops.push(self.event(Access::Write,Path::root(old.id),None,start));
        let binding=self.scopes.last_mut()?.get_mut(name)?;
        binding.loan=Some(new_loan);
        binding.borrow_parent=parent;
        binding.reference=Some((path,true));
        binding.alternatives.clear();
        binding.phi_generation=None;
        Some(ops)
    }
    fn analyze_stmt(&mut self,start:usize,end:usize)->Option<Vec<Statement>>{
        if start>=end{return None;}
        if matches!(self.kind(start),Some(K::Ident("let"|"const"))){
            let mut i=start+1;
            let mutable=self.kind(i)==Some(K::Ident("mut"));
            if mutable{i+=1;}
            if let (Some(K::Ident(type_name)),Some(K::LBrace))=(self.kind(i),self.kind(i+1)) {
                let close=self.close(i+1,end,K::LBrace,K::RBrace)?;
                if self.kind(close+1)!=Some(K::Equal){return None;}
                let id=*self.schema.type_ids.get(type_name)?;
                let (owner,actual,via)=self.resolve_path(close+2,end)?;
                if via.is_some()||self.ty_id(&actual)!=Some(id){return None;}
                let mut ops=Vec::new();
                let mut used=HashSet::new();
                for item in self.split_top(i+2,close,K::Comma) {
                    if item.end!=item.start+1{return None;}
                    let K::Ident(field_name)=self.kind(item.start)? else{return None;};
                    let (key,ty)=self.field(&ConstType::Resolved(id),field_name)?;
                    if !used.insert(key){return None;}
                    let local=SymbolId(u32::try_from(item.start+1).ok()?);
                    let path=owner.child(key);
                    ops.push(Statement::StorageLive(Event{op:Access::StorageLive,
                        path:Path::root(local),loan:None,parent:None,token:item.start}));
                    ops.push(self.event(if self.is_copy(&ty){Access::Read}else{Access::Move},
                        path,None,item.start));
                    ops.push(self.event(Access::Initialize,Path::root(local),None,item.start));
                    self.scopes.last_mut()?.insert(field_name.to_owned(),Binding{
                        id:local,ty,reference:None,loan:None,borrow_parent:None,alternatives:Vec::new(),phi_generation:None,mutable:false});
                }
                return Some(ops);
            }
            let K::Ident(name)=self.kind(i)? else{return None;};
            let binding_at=i;i+=1;
            let annotated=if self.kind(i)==Some(K::Colon){
                i+=1;let mut r=false;let mut m=false;
                if self.kind(i)==Some(K::Amp){r=true;i+=1;
                    if self.kind(i)==Some(K::Ident("mut")){m=true;i+=1;}}
                let K::Ident(ty)=self.kind(i)? else{return None;};i+=1;
                Some((ty.to_owned(),r,m))
            }else{None};
            if self.kind(i)!=Some(K::Equal){return None;}i+=1;
            let (mut statements,inferred,reference,move_source)=if end==i+1 {
                if let Some(K::Ident(source_name))=self.kind(i) {
                    if self.lookup(source_name).is_some_and(|binding|
                        matches!(binding.ty,ConstType::RefMut(_))) {
                        let dest=SymbolId(u32::try_from(binding_at+1).ok()?);
                        let (ops,ty,path,parent)=self.relocate_mut_loan(source_name,dest,start)?;
                        (ops,ty,Some((path,true,parent)),true)
                    }else{
                        let (ops,ty,reference)=self.expr(i,end)?;
                        (ops,ty,reference,false)
                    }
                }else{
                    let (ops,ty,reference)=self.expr(i,end)?;
                    (ops,ty,reference,false)
                }
            }else{
                let (ops,ty,reference)=self.expr(i,end)?;
                (ops,ty,reference,false)
            };
            let declared=match annotated {
                Some((ty,reference,mutable))=>{
                    let base=match ty.as_str(){"i64"=>ConstType::I64,"u64"=>ConstType::U64,"bool"=>ConstType::Bool,
                        _=>ConstType::Named(ty)};
                    let declared=if reference {
                        if mutable {ConstType::RefMut(Box::new(base))}
                        else {ConstType::Ref(Box::new(base))}
                    }else{base};
                    if move_source && declared!=inferred {
                        self.failure=Some("mutable reference alias type mismatch".into());
                        return None;
                    }
                    declared
                },None=>inferred,
            };
            let id=SymbolId(u32::try_from(binding_at+1).ok()?);
            statements.insert(0,Statement::StorageLive(Event{
                op:Access::StorageLive,path:Path::root(id),loan:None,parent:None,token:start}));
            if !move_source {
                if let Some((path,exclusive,parent))=&reference {
                    statements.push(Statement::Access(Event{
                        op:if *exclusive{Access::BorrowMut}else{Access::BorrowShared},
                        path:path.clone(),loan:Some(id),parent:*parent,token:start}));
                    self.loans.insert(id,path.clone());
                }
            }
            self.scopes.last_mut()?.insert(name.to_owned(),Binding{id,ty:declared,
                loan:reference.as_ref().map(|_|id),
                borrow_parent:reference.as_ref().and_then(|(_,_,parent)|*parent),
                reference:reference.map(|(path,exclusive,_)|(path,exclusive)),
                alternatives:Vec::new(),phi_generation:None,mutable});
            statements.push(self.event(Access::Initialize,Path::root(id),None,start));
            return Some(statements);
        }
        if self.kind(start+1)==Some(K::Equal) {
            if let Some(K::Ident(name))=self.kind(start) {
                if self.lookup(name).is_some_and(|binding|
                    matches!(binding.ty,ConstType::RefMut(_))) {
                    return self.reassign_mut_reference(start,end);
                }
            }
        }
        if self.kind(start)==Some(K::Star) && self.kind(start+2)==Some(K::Equal){
            let K::Ident(name)=self.kind(start+1)? else{return None;};
            let binding=self.lookup(name)?;
            let pointee=match &binding.ty {ConstType::RefMut(ty)=>ty.as_ref(),_=>return None};
            let (mut ops,actual,_)=self.expr(start+3,end)?;
            if &actual!=pointee{return None;}
            if !binding.alternatives.is_empty() {
                binding.phi_generation?;
                ops.push(self.event(Access::Write,Path::root(binding.id),binding.phi_generation,start));
                return Some(ops);
            }
            let (path,exclusive)=binding.reference.clone()?;
            if !exclusive{return None;}
            ops.push(self.event(Access::Write,path,binding.loan,start));
            return Some(ops);
        }
        //A projected write through an exclusive call-result PHI must be authorized by every possible loan
        if let Some(K::Ident(name))=self.kind(start) {
            if let Some(binding)=self.lookup(name) {
                if !binding.alternatives.is_empty() &&
                    matches!(&binding.ty,ConstType::RefMut(_)) &&
                    self.kind(start+1)==Some(K::Dot) {
                    if let Some(equal)=(start+2..end).find(|&at|
                        self.kind(at)==Some(K::Equal)) {
                        let mut ty=match &binding.ty {
                            ConstType::RefMut(inner)=>(**inner).clone(),_=>return None,
                        };
                        let mut i=start+1;
                        while i<equal {
                            if self.kind(i)!=Some(K::Dot){return None;}
                            let K::Ident(field)=self.kind(i+1)? else{return None;};
                            let (_,next)=self.field(&ty,field)?;
                            ty=next;i+=2;
                        }
                        let (mut events,rhs,_)=self.expr(equal+1,end)?;
                        if !self.same_type(&ty,&rhs){return None;}
                        events.push(self.event(Access::Write,Path::root(binding.id),
                            binding.phi_generation,start));
                        return Some(events);
                    }
                }
            }
        }
        for at in start+1..end {
            if !matches!(self.kind(at),Some(K::PlusEq|K::MinusEq|K::StarEq|
                K::SlashEq|K::PercentEq)){continue;}
            let (path,ty,via)=self.resolve_path(start,at)?;
            if !matches!(&ty,ConstType::I64|ConstType::U64){return None;}
            let Some(K::Ident(root))=self.kind(start)else{return None;};
            let binding=self.lookup(root)?;
            if via.is_some() {
                if !matches!(&binding.ty,ConstType::RefMut(_)){return None;}
            }else if !binding.mutable {return None;}
            let (mut rhs,actual,reference)=self.expr(at+1,end)?;
            if actual!=ty || reference.is_some(){return None;}
            let mut operations=Vec::with_capacity(rhs.len()+2);
            operations.push(self.event(Access::Read,path.clone(),via,start));
            operations.append(&mut rhs);
            operations.push(self.event(Access::Write,path,via,start));
            return Some(operations);
        }
        for i in start+1..end {
            if self.kind(i)!=Some(K::Equal){continue;}
            let (path,_,via)=self.resolve_path(start,i)?;
            let (mut right,_,_)=self.expr(i+1,end)?;
            right.push(self.event(Access::Write,path,via,start));return Some(right);
        }
        let (ops,_,_)=self.expr(start,end)?;Some(ops)
    }
    fn leave_scopes(&self,first:usize,token:usize)->Vec<Statement>{
        let mut locals=self.scopes.iter().skip(first).flat_map(|s|s.values().cloned()).collect::<Vec<_>>();
        locals.sort_by_key(|b|((b.reference.is_none() && b.alternatives.is_empty()),std::cmp::Reverse(b.id.0)));
        let mut out=Vec::with_capacity(locals.len()*2);
        for b in &locals {
            if !b.alternatives.is_empty(){
                for candidate in &b.alternatives {
                    out.push(self.event(Access::EndLoan,candidate.path.clone(),
                        Some(candidate.loan),token));
                }
            }else if let Some((path,_))=&b.reference {
                out.push(self.event(Access::EndLoan,path.clone(),b.loan,token));
            }
        }
        for b in &locals {
            out.push(Statement::StorageDead(Event{op:Access::StorageDead,
                path:Path::root(b.id),loan:None,parent:None,token}));
        }
        out
    }
    fn rebind_arm(&self,range:Range<usize>)->Option<(String,Range<usize>)>{
        let stop=if range.start<range.end && self.kind(range.end-1)==Some(K::Semi){
            range.end-1
        }else{range.end};
        if stop<=range.start+2 || self.kind(range.start+1)!=Some(K::Equal) ||
            self.kind(range.start+2)!=Some(K::Amp) {return None;}
        let K::Ident(name)=self.kind(range.start)? else{return None;};
        Some((name.to_owned(),range.start+2..stop))
    }
    fn finish_mut_rebind_branches(&mut self,at:usize,from:&[usize],
        control:Vec<Statement>,arms:[(String,Range<usize>);2],next:usize)
        ->Result<Option<(Vec<usize>,usize)>,String>{
        let [(left_name,left_rhs),(right_name,right_rhs)]=arms;
        if left_name!=right_name{return Ok(None);}
        let Some(original)=self.lookup(&left_name)else{return Ok(None)};
        if !original.mutable || !matches!(&original.ty,ConstType::RefMut(_)){
            return Ok(None);
        }
        let retired=if !original.alternatives.is_empty() {
            if original.loan.is_some() || original.reference.is_some() ||
                original.alternatives.iter().any(|candidate|!candidate.exclusive) {
                return Ok(None);
            }
            original.alternatives.iter().map(|candidate|
                (candidate.path.clone(),candidate.loan)).collect::<Vec<_>>()
        } else {
            let Some((path,true))=original.reference.clone()else{return Ok(None)};
            let Some(loan)=original.loan else{return Ok(None)};
            vec![(path,loan)]
        };
        let Some((mut left_ops,left_type,Some((left_path,true,left_parent))))=
            self.expr(left_rhs.start,left_rhs.end)else{return Ok(None)};
        let Some((mut right_ops,right_type,Some((right_path,true,right_parent))))=
            self.expr(right_rhs.start,right_rhs.end)else{return Ok(None)};
        if left_type!=original.ty || right_type!=original.ty{return Ok(None);}
        //All CFG paths retire the old destination loan BEFORE the new branch-specific loan. A still-live child
        //prevents EndLoan
        let control_node=self.add(from.to_vec(),control)?[0];
        let retirement=retired.into_iter().map(|(path,loan)|
            self.event(Access::EndLoan,path,Some(loan),at)).collect();
        let retired=self.add(vec![control_node],retirement)?[0];
        let left_entry=self.block()?;let right_entry=self.block()?;
        self.link(&[retired],left_entry);
        self.link(&[retired],right_entry);
        let left_loan=self.temp_id().ok_or("too many mutable branch loans")?;
        let right_loan=self.temp_id().ok_or("too many mutable branch loans")?;
        let left=RefOption{loan:left_loan,path:left_path.clone(),exclusive:true,parent:left_parent};
        let right=RefOption{loan:right_loan,path:right_path.clone(),exclusive:true,parent:right_parent};
        for (ops,option,token) in [(&mut left_ops,&left,left_rhs.start),
                                   (&mut right_ops,&right,right_rhs.start)] {
            ops.push(Statement::Access(Event{op:Access::BorrowMut,
                path:option.path.clone(),loan:Some(option.loan),parent:option.parent,token}));
            ops.push(self.event(Access::Initialize,Path::root(original.id),None,token));
            self.loans.insert(option.loan,option.path.clone());
        }
        let left_end=self.add(vec![left_entry],left_ops)?;
        let right_end=self.add(vec![right_entry],right_ops)?;
        let (tails,_,alternatives)=self.finish_value_phi(
            left_end.into_iter().chain(right_end).collect(),original.id,
            original.ty.clone(),vec![left,right],at)?;
        let phi_generation=self.phi_generation(&tails,original.id)
            .ok_or("missing mutable PHI generation")?;
        let binding=self.scopes.iter_mut().rev().find_map(|s|s.get_mut(&left_name))
            .ok_or("missing mutable binding after conditional PHI")?;
        binding.loan=None;
        binding.borrow_parent=None;
        binding.reference=None;
        binding.alternatives=alternatives;
        binding.phi_generation=Some(phi_generation);
        Ok(Some((tails,next)))
    }
    fn parse_mut_rebind_if(&mut self,at:usize,limit:usize,from:&[usize])
        ->Result<Option<(Vec<usize>,usize)>,String>{
        let Some(brace)=(at+1..limit).find(|&p|self.kind(p)==Some(K::LBrace))
            else{return Ok(None)};
        let Some(end_yes)=self.close(brace,limit,K::LBrace,K::RBrace)
            else{return Ok(None)};
        let else_at=end_yes+1;
        if self.kind(else_at)!=Some(K::Ident("else")) ||
            self.kind(else_at+1)!=Some(K::LBrace){return Ok(None);}
        let no_brace=else_at+1;
        let Some(end_no)=self.close(no_brace,limit,K::LBrace,K::RBrace)
            else{return Ok(None)};
        let Some(left)=self.rebind_arm(brace+1..end_yes)else{return Ok(None)};
        let Some(right)=self.rebind_arm(no_brace+1..end_no)else{return Ok(None)};
        let Some((control,ConstType::Bool,_))=self.expr(at+1,brace)
            else{return Ok(None)};
        self.finish_mut_rebind_branches(at,from,control,[left,right],end_no+1)
    }
    fn parse_mut_rebind_match(&mut self,at:usize,limit:usize,from:&[usize])
        ->Result<Option<(Vec<usize>,usize)>,String>{
        let Some(brace)=(at+1..limit).find(|&p|self.kind(p)==Some(K::LBrace))
            else{return Ok(None)};
        let Some(last)=self.close(brace,limit,K::LBrace,K::RBrace)
            else{return Ok(None)};
        let Some((control,ConstType::Bool,_))=self.expr(at+1,brace)
            else{return Ok(None)};
        let mut arm=brace+1;
        let mut true_arm=None;
        let mut false_arm=None;
        let mut default_arm=None;
        while arm<last {
            if self.kind(arm+1)!=Some(K::FatArrow) ||
                self.kind(arm+2)!=Some(K::LBrace){return Ok(None);}
            let Some(end)=self.close(arm+2,last,K::LBrace,K::RBrace)
                else{return Ok(None)};
            let Some(rebind)=self.rebind_arm(arm+3..end)else{return Ok(None)};
            match self.kind(arm) {
                Some(K::Ident("true")) if true_arm.is_none() && default_arm.is_none()=>true_arm=Some(rebind),
                Some(K::Ident("false")) if false_arm.is_none() && default_arm.is_none()=>false_arm=Some(rebind),
                Some(K::Ident("_")) if default_arm.is_none()=>default_arm=Some(rebind),
                _=>return Ok(None),
            }
            arm=end+1;
            if default_arm.is_some() && arm<last && self.kind(arm)!=Some(K::Comma){
                return Ok(None);
            }
            if self.kind(arm)==Some(K::Comma){arm+=1;}
        }
        //Exactly two reachable boolean cases. A final wildcard may fill the single missing case, but can never
        //shadow another arm
        let yes=true_arm.or_else(||default_arm.clone());
        let no=false_arm.or(default_arm);
        let (Some(yes),Some(no))=(yes,no)else{return Ok(None)};
        self.finish_mut_rebind_branches(at,from,control,[yes,no],last+1)
    }
    fn parse_enum_mut_rebind_match(&mut self,at:usize,limit:usize,from:&[usize])
        ->Result<Option<(Vec<usize>,usize)>,String>{
        let Some(brace)=(at+1..limit).find(|&p|self.kind(p)==Some(K::LBrace))
            else{return Ok(None)};
        let Some(last)=self.close(brace,limit,K::LBrace,K::RBrace)
            else{return Ok(None)};
        let Some((control,subject_ty,_))=self.expr(at+1,brace)else{return Ok(None)};
        let Some(type_id)=self.ty_id(&subject_ty)else{return Ok(None)};
        let Some(type_name)=self.schema.type_names.get(type_id.0 as usize)else{return Ok(None)};
        let Some(variants)=self.schema.enums.get(type_name)else{return Ok(None)};
        if variants.is_empty() || variants.len()>128{return Ok(None)};
        let mut arm=brace+1;
        let mut seen=0u128;
        let mut wildcard=false;
        let mut bodies=Vec::<(String,Range<usize>)>::new();
        while arm<last {
            if wildcard{return Err("unreachable enum match arm after wildcard".into());}
            let arrow=if self.kind(arm)==Some(K::Ident("_")) {
                wildcard=true;arm+1
            }else{
                let Some(K::Ident(owner))=self.kind(arm)else{return Ok(None)};
                if owner!=type_name.as_str() || self.kind(arm+1)!=Some(K::Colon) ||
                    self.kind(arm+2)!=Some(K::Colon){return Ok(None);}
                let Some(K::Ident(variant))=self.kind(arm+3)else{return Ok(None)};
                let Some(index)=variants.iter().position(|name|name.as_str()==variant)else{
                    return Err("unknown enum match variant in MIR".into());
                };
                let bit=1u128<<index;
                if seen&bit!=0{return Err("duplicate enum match variant in MIR".into());}
                seen|=bit;arm+4
            };
            if self.kind(arrow)!=Some(K::FatArrow) ||
                self.kind(arrow+1)!=Some(K::LBrace){return Ok(None)};
            let Some(end)=self.close(arrow+1,last,K::LBrace,K::RBrace)
                else{return Ok(None)};
            let Some(body)=self.rebind_arm(arrow+2..end)else{return Ok(None)};
            bodies.push(body);
            arm=end+1;
            if self.kind(arm)==Some(K::Comma){arm+=1;}
            if bodies.len()>32{return Err("too many enum mutable PHI alternatives".into());}
        }
        if !wildcard && seen.count_ones() as usize != variants.len(){
            return Err("nonexhaustive enum match in typed MIR".into());
        }
        if bodies.len()<2{return Ok(None)};
        let target=bodies[0].0.clone();
        if bodies.iter().any(|(name,_)|name!=&target){return Ok(None)};
        let Some(original)=self.lookup(&target)else{return Ok(None)};
        if !original.mutable || !matches!(&original.ty,ConstType::RefMut(_)){
            return Ok(None);
        }
        let retired=if original.alternatives.is_empty(){
            let Some((path,true))=original.reference.clone()else{return Ok(None)};
            let Some(loan)=original.loan else{return Ok(None)};
            vec![(path,loan)]
        }else{
            if original.reference.is_some() || original.loan.is_some() ||
                original.alternatives.iter().any(|o|!o.exclusive){return Ok(None)};
            original.alternatives.iter().map(|o|(o.path.clone(),o.loan)).collect()
        };
        let mut evaluated=Vec::with_capacity(bodies.len());
        for (_,range) in bodies {
            let Some((ops,ty,Some((path,true,parent))))=
                self.expr(range.start,range.end)else{return Ok(None)};
            if ty!=original.ty{return Ok(None)};
            evaluated.push((ops,path,parent,range.start));
        }
        let dispatch=self.add(from.to_vec(),control)?[0];
        let mut endings=Vec::with_capacity(evaluated.len());
        let mut alternatives=Vec::with_capacity(evaluated.len());
        for (mut ops,path,parent,token) in evaluated {
            let entry=self.block()?;self.link(&[dispatch],entry);
            for (old_path,id) in &retired {
                ops.push(self.event(Access::EndLoan,old_path.clone(),Some(*id),token));
            }
            let loan=self.temp_id().ok_or("too many enum PHI loans")?;
            ops.push(Statement::Access(Event{op:Access::BorrowMut,path:path.clone(),
                loan:Some(loan),parent,token}));
            ops.push(self.event(Access::Initialize,Path::root(original.id),None,token));
            self.loans.insert(loan,path.clone());
            alternatives.push(RefOption{loan,path,exclusive:true,parent});
            endings.extend(self.add(vec![entry],ops)?);
        }
        let (tails,_,alternatives)=self.finish_value_phi(
            endings,original.id,original.ty.clone(),alternatives,at)?;
        let generation=self.phi_generation(&tails,original.id)
            .ok_or("missing enum PHI generation")?;
        let binding=self.scopes.iter_mut().rev().find_map(|scope|scope.get_mut(&target))
            .ok_or("missing enum mutable binding")?;
        binding.reference=None;binding.loan=None;binding.borrow_parent=None;
        binding.alternatives=alternatives;binding.phi_generation=Some(generation);
        Ok(Some((tails,last+1)))
    }
    fn parse_mut_rebind_else_if(&mut self,at:usize,limit:usize,from:&[usize])
        ->Result<Option<(Vec<usize>,usize)>,String>{
        let mut conditional=Vec::<(Range<usize>,(String,Range<usize>))>::new();
        let mut cursor=at;
        let (otherwise,next)=loop {
            if self.kind(cursor)!=Some(K::Ident("if")){return Ok(None);}
            let Some(brace)=(cursor+1..limit).find(|&p|self.kind(p)==Some(K::LBrace))
                else{return Ok(None)};
            let Some(close)=self.close(brace,limit,K::LBrace,K::RBrace)
                else{return Ok(None)};
            let Some(arm)=self.rebind_arm(brace+1..close)else{return Ok(None)};
            conditional.push((cursor+1..brace,arm));
            if conditional.len()>16{return Err("too many mutable reference CFG arms".into());}
            let else_at=close+1;
            if self.kind(else_at)!=Some(K::Ident("else")){return Ok(None);}
            cursor=else_at+1;
            if self.kind(cursor)==Some(K::Ident("if")){continue;}
            if self.kind(cursor)!=Some(K::LBrace){return Ok(None);}
            let Some(end)=self.close(cursor,limit,K::LBrace,K::RBrace)
                else{return Ok(None)};
            let Some(last)=self.rebind_arm(cursor+1..end)else{return Ok(None)};
            break (last,end+1);
        };
        if conditional.len()<2{return Ok(None);}
        let target=conditional[0].1.0.as_str();
        if otherwise.0.as_str()!=target ||
            conditional.iter().any(|(_,arm)|arm.0.as_str()!=target){
            return Ok(None);
        }
        let Some(original)=self.lookup(target)else{return Ok(None)};
        if !original.mutable || !matches!(&original.ty,ConstType::RefMut(_)){
            return Ok(None);
        }
        let retirement=if !original.alternatives.is_empty(){
            if original.reference.is_some() || original.loan.is_some(){return Ok(None);}
            original.alternatives.iter().map(|option|{
                (option.path.clone(),option.loan)
            }).collect::<Vec<_>>()
        }else{
            let Some((path,true))=original.reference.clone()else{return Ok(None)};
            let Some(loan)=original.loan else{return Ok(None)};
            vec![(path,loan)]
        };
        if retirement.is_empty() || retirement.len()+conditional.len()+1>32{
            return Ok(None);
        }
        let mut decisions=Vec::with_capacity(conditional.len());
        let mut arms=Vec::with_capacity(conditional.len()+1);
        for (condition,(_,rhs)) in &conditional {
            let Some((events,ConstType::Bool,_))=self.expr(condition.start,condition.end)
                else{return Ok(None)};
            decisions.push(events);
            let Some((events,ty,Some((path,true,parent))))=
                self.expr(rhs.start,rhs.end)else{return Ok(None)};
            if ty!=original.ty{return Ok(None);}
            arms.push((events,path,parent,rhs.start));
        }
        let Some((events,ty,Some((path,true,parent))))=
            self.expr(otherwise.1.start,otherwise.1.end)else{return Ok(None)};
        if ty!=original.ty{return Ok(None);}
        arms.push((events,path,parent,otherwise.1.start));
        let mut incoming=from.to_vec();
        let mut entries=Vec::with_capacity(arms.len());
        for events in decisions {
            let decision=self.add(incoming,events)?[0];
            let yes=self.block()?;let no=self.block()?;
            self.link(&[decision],yes);
            self.link(&[decision],no);
            entries.push(yes);
            incoming=vec![no];
        }
        entries.push(incoming[0]);
        let mut endings=Vec::with_capacity(arms.len());
        let mut alternatives=Vec::with_capacity(arms.len());
        for (entry,(mut events,path,parent,token)) in entries.into_iter().zip(arms){
            for (old_path,old_id) in &retirement {
                events.push(self.event(Access::EndLoan,old_path.clone(),Some(*old_id),token));
            }
            let loan=self.temp_id().ok_or("too many mutable branch loans")?;
            events.push(Statement::Access(Event{
                op:Access::BorrowMut,path:path.clone(),loan:Some(loan),parent,token,
            }));
            events.push(self.event(Access::Initialize,Path::root(original.id),None,token));
            self.loans.insert(loan,path.clone());
            alternatives.push(RefOption{loan,path,exclusive:true,parent});
            endings.extend(self.add(vec![entry],events)?);
        }
        let (tails,_,new_options)=self.finish_value_phi(
            endings,original.id,original.ty.clone(),alternatives,at)?;
        let phi_generation=self.phi_generation(&tails,original.id)
            .ok_or("missing else-if PHI generation")?;
        let binding=self.scopes.iter_mut().rev().find_map(|scope|scope.get_mut(target))
            .ok_or("missing mutable binding after else-if PHI")?;
        binding.loan=None;
        binding.borrow_parent=None;
        binding.reference=None;
        binding.alternatives=new_options;
        binding.phi_generation=Some(phi_generation);
        Ok(Some((tails,next)))
    }
    //An immediate `let child = &mut *merged` after a mutable reference PHI is lowered into one child loan
    //per incoming CFG edge
    fn immediate_phi_mut_reborrow(&mut self,start:usize,end:usize,tails:&[usize])
        ->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")){return Ok(None);}
        let mutable=self.kind(start+1)==Some(K::Ident("mut"));
        let name_at=start+1+usize::from(mutable);
        let Some(K::Ident(dest_name))=self.kind(name_at)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        if self.kind(name_at+1)!=Some(K::Equal) ||
           self.kind(name_at+2)!=Some(K::Amp) ||
           self.kind(name_at+3)!=Some(K::Ident("mut")) {return Ok(None);}
        let (source_name,field_name)=if end==name_at+6 &&
            self.kind(name_at+4)==Some(K::Star) {
            let Some(K::Ident(name))=self.kind(name_at+5)else{return Ok(None)};
            (name.to_owned(),None)
        }else if end==name_at+7 &&
            self.kind(name_at+5)==Some(K::Dot) {
            let (Some(K::Ident(name)),Some(K::Ident(field)))=
                (self.kind(name_at+4),self.kind(name_at+6))else{return Ok(None)};
            (name.to_owned(),Some(field.to_owned()))
        }else{return Ok(None)};
        let Some(source)=self.lookup(&source_name)else{return Ok(None)};
        if !matches!(&source.ty,ConstType::RefMut(_)) ||
            source.alternatives.len()<2 || source.loan.is_some() ||
            source.reference.is_some(){return Ok(None);}
        if dest_name==source_name || self.scopes.last().is_some_and(|scope|
            scope.contains_key(&dest_name)){return Ok(None);}
        let projected=if let Some(field)=field_name.as_deref(){
            let ConstType::RefMut(inner)=&source.ty else{return Ok(None)};
            let Some((field_key,ty))=self.field(inner,field)else{return Ok(None)};
            Some((field_key,ty))
        }else{None};
        let dest_ty=if let Some((_,ty))=&projected {
            ConstType::RefMut(Box::new(ty.clone()))
        }else{source.ty.clone()};
        let [join]=tails else{return Ok(None)};
        let join=*join;
        //The source must be the current result PHI, not an earlier PHI separated by an access, a call, or a
        //control-flow transition
        let Some(Statement::ValuePhi{predecessors,alternatives,..})=
            self.blocks.get(join).and_then(|block|block.statements.iter().find(|stmt|
                matches!(stmt,Statement::ValuePhi{check,..} if check.path==Path::root(source.id))))
            else{return Ok(None)};
        let predecessors=predecessors.clone();
        let alternatives=alternatives.clone();
        if predecessors.len()!=alternatives.len() || predecessors.len()<2 ||
            predecessors.len()>32 || alternatives.iter().any(|o|!o.exclusive){return Ok(None);}
        if !matches!(&self.blocks[join].terminator,Terminator::Goto(next) if next.is_empty()) {
            return Ok(None);
        }
        if self.blocks[join].statements.iter().any(|stmt|!matches!(stmt,
            Statement::ValuePhi{..}|Statement::StorageLive(_)|
            Statement::Access(Event{op:Access::Initialize,..}))) {return Ok(None);}
        //Each CFG predecessor must have a direct, proven loan which matches exactly one alternative. Reject
        //overlapping/missing providers
        let mut selected=Vec::with_capacity(predecessors.len());
        for &pred in &predecessors {
            let Some(block)=self.blocks.get(pred)else{return Ok(None)};
            if !matches!(&block.terminator,Terminator::Goto(next) if next.contains(&join)){
                return Ok(None);
            }
            let matches=alternatives.iter().filter(|opt|block.statements.iter().any(|stmt|
                matches!(stmt,Statement::Access(Event{
                    op:Access::BorrowMut,path,loan:Some(id),parent,..}
                    ) if *id==opt.loan && *path==opt.path && *parent==opt.parent)))
                .collect::<Vec<_>>();
            if matches.len()!=1{return Ok(None);}
            selected.push((*matches[0]).clone());
        }
        let unique=selected.iter().map(|o|o.loan).collect::<HashSet<_>>();
        if unique.len()!=selected.len() ||
            unique.len()!=alternatives.len(){return Ok(None);}
        let dest=SymbolId(u32::try_from(name_at+1).map_err(|_|"too many MIR locals")?);
        let mut children=Vec::with_capacity(selected.len());
        for option in &selected {
            let child=self.temp_id().ok_or("too many PHI reborrow loans")?;
            let path=if let Some((field,_))=&projected {
                option.path.child(*field)
            }else{option.path.clone()};
            children.push(RefOption{loan:child,path,
                exclusive:true,parent:Some(option.loan)});
        }
        for (&pred,child) in predecessors.iter().zip(&children) {
            self.blocks[pred].statements.push(Statement::Access(Event{
                op:Access::BorrowMut,path:child.path.clone(),loan:Some(child.loan),
                parent:child.parent,token:start,
            }));
            self.loans.insert(child.loan,child.path.clone());
        }
        self.blocks[join].statements.push(Statement::StorageLive(Event{
            op:Access::StorageLive,path:Path::root(dest),loan:None,parent:None,token:start,
        }));
        self.blocks[join].statements.push(Statement::Access(Event{
            op:Access::Initialize,path:Path::root(dest),
            loan:None,parent:None,token:start,
        }));
        let uniform=children.first().and_then(|first|children.iter().all(|next|
            next.path==first.path && next.exclusive==first.exclusive &&
            next.parent==first.parent).then(||(first.path.clone(),true,first.parent)));
        let phi_generation=self.temp_id().ok_or("too many PHI generations")?;
        self.blocks[join].statements.push(Statement::ValuePhi{
            ty:dest_ty.clone(),predecessors,provenance:uniform,
            alternatives:children.clone(),generation:Some(phi_generation),
            check:Event{op:Access::Read,path:Path::root(dest),
                loan:None,parent:None,token:start},
        });
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty:dest_ty,reference:None,loan:None,borrow_parent:None,
            alternatives:children,phi_generation:Some(phi_generation),mutable,
        });
        Ok(Some(tails.to_vec()))
    }
    fn late_independent_mut_phi_bind(&mut self,start:usize,end:usize,
        tails:&[usize])->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")) || tails.len()!=1 {
            return Ok(None);
        }
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable{i+=1;}
        let Some(K::Ident(dest_name))=self.kind(i)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        if self.kind(i+1)!=Some(K::Equal) || self.scopes.last().is_some_and(|scope|
            scope.contains_key(&dest_name)) {return Ok(None);}
        let dest=SymbolId(u32::try_from(i+1).map_err(|_|"too many MIR locals")?);
        let expr=i+2;
        let mut named_fields=Vec::<String>::new();
        let mut forwarded=None::<(String,VerifiedCallSummary,usize,usize)>;
        let source_name=if self.kind(expr)==Some(K::Amp) &&
            self.kind(expr+1)==Some(K::Ident("mut")) {
            if self.kind(expr+2)==Some(K::Star) && end==expr+4 {
                let Some(K::Ident(name))=self.kind(expr+3)else{return Ok(None)};
                name.to_owned()
            }else {
                let Some(K::Ident(name))=self.kind(expr+2)else{return Ok(None)};
                let mut at=expr+3;
                while at+1<end && self.kind(at)==Some(K::Dot) {
                    let Some(K::Ident(field))=self.kind(at+1)else{return Ok(None)};
                    named_fields.push(field.to_owned());
                    if named_fields.len()>16{return Ok(None);}
                    at+=2;
                }
                if at!=end || named_fields.is_empty(){return Ok(None);}
                name.to_owned()
            }
        }else{
            let Some(K::Ident(name))=self.kind(expr)else{return Ok(None)};
            let name=name.to_owned();
            if self.kind(expr+1)!=Some(K::LParen) ||
                self.close(expr+1,end,K::LParen,K::RParen)!=Some(end-1){
                return Ok(None);
            }
            let Some(summary)=self.verified_calls.get(&name).cloned()else{return Ok(None)};
            let Some(origin)=summary.returned.as_ref()else{return Ok(None)};
            let count=summary.parameters.len();
            if !(1..=4).contains(&count) || origin.parameter>=count ||
                !matches!(&origin.ty,ConstType::RefMut(_)) ||
                !matches!(&summary.parameters[origin.parameter],ConstType::RefMut(_)) ||
                !summary.returned_alternatives.is_empty() ||
                summary.parameters.iter().any(|formal|
                    !matches!(formal,ConstType::Ref(_)|ConstType::RefMut(_))) ||
                summary.path_cases.len()>128 ||
                summary.path_cases.iter().any(|case|
                    case.returned!=Some(0) || !case.uninitialized.is_empty()) {
                return Ok(None);
            }
            //Do not let a MAY-write be discarded by a forged or absent path-case certificate
            let proven=summary.path_cases.iter().flat_map(|case|
                case.effects.iter().cloned()).collect::<HashSet<_>>();
            let may=summary.parameter_effects.iter().cloned().collect::<HashSet<_>>();
            if (!may.is_empty() && (summary.path_cases.is_empty() || proven!=may)) ||
                summary.parameter_effects.iter().any(|effect|
                    effect.kind!=VerifiedEffectKind::Write ||
                    effect.fields.is_empty() ||
                    !matches!(summary.parameters.get(effect.parameter),
                        Some(ConstType::RefMut(_)))) ||
                summary.field_writes.iter().any(|write|
                    !may.contains(&VerifiedParameterEffect{
                        parameter:write.parameter,fields:write.fields.clone(),
                        kind:VerifiedEffectKind::Write})) {
                return Ok(None);
            }
            let args=self.split_top(expr+2,end-1,K::Comma);
            if args.len()!=count{return Ok(None);}
            //The returned parent must be a named PHI binding, not a guessed owner or a selected alternative from
            //another merge
            let selected=&args[origin.parameter];
            if selected.end!=selected.start+1{return Ok(None);}
            let Some(K::Ident(source))=self.kind(selected.start)else{return Ok(None)};
            forwarded=Some((name,summary,expr,end));
            source.to_owned()
        };
        let Some(source)=self.lookup(&source_name)else{return Ok(None)};
        if !matches!(&source.ty,ConstType::RefMut(_)) ||
            source.reference.is_some() || source.loan.is_some() ||
            source.alternatives.len()<2 || source.alternatives.len()>32 ||
            source.phi_generation.is_none() || dest==source.id ||
            source.alternatives.iter().any(|option|!option.exclusive ||
                self.loans.get(&option.loan)!=Some(&option.path)) {
            return Ok(None);
        }
        if let Some((_,summary,call_at,call_end))=&forwarded {
            let args=self.split_top(*call_at+2,*call_end-1,K::Comma);
            let mut actuals=Vec::<(bool,Vec<Path>)>::with_capacity(args.len());
            for (argument,formal) in args.iter().zip(&summary.parameters) {
                let exclusive=matches!(formal,ConstType::RefMut(_));
                let candidates=if self.kind(argument.start)==Some(K::Amp) {
                    let mut at=argument.start+1;
                    if self.kind(at)==Some(K::Ident("mut")){at+=1;}
                    let Some((path,_,_))=self.resolve_path(at,argument.end)else{
                        return Ok(None);
                    };
                    vec![path]
                }else if argument.end==argument.start+1 {
                    let Some(K::Ident(name))=self.kind(argument.start)else{return Ok(None)};
                    let Some(binding)=self.lookup(name)else{return Ok(None)};
                    if !binding.alternatives.is_empty(){
                        binding.alternatives.iter().map(|o|o.path.clone()).collect()
                    }else if let Some((path,_))=binding.reference {
                        vec![path]
                    }else{return Ok(None);}
                }else{return Ok(None);};
                actuals.push((exclusive,candidates));
            }
            for i in 0..actuals.len() {
                for j in i+1..actuals.len() {
                    if !(actuals[i].0 || actuals[j].0){continue;}
                    if actuals[i].1.iter().any(|a|actuals[j].1.iter().any(|b|
                        a.ancestor_of(b) || b.ancestor_of(a))) {
                        return Ok(None);
                    }
                }
            }
        }
        let joined=tails[0];
        if self.blocks.get(joined).is_some_and(|block|
            block.statements.iter().any(|statement|matches!(statement,
                Statement::ValuePhi{check,..} if check.path==Path::root(source.id)))) {
            return Ok(None);
        }
        let ConstType::RefMut(pointee)=&source.ty else{return Ok(None)};
        let mut current=(**pointee).clone();
        let mut projections=Vec::<(FieldKey,ConstType)>::new();
        if let Some((_,summary,_,_))=&forwarded {
            let origin=summary.returned.as_ref().ok_or("missing verified return")?;
            if !self.same_type(&summary.parameters[origin.parameter],&source.ty){
                return Ok(None);
            }
            if origin.fields.len()>16{return Ok(None);}
            for &field in &origin.fields {
                if self.ty_id(&current)!=Some(field.aggregate){return Ok(None);}
                let Some(type_name)=self.schema.type_names.get(field.aggregate.0 as usize)
                    else{return Ok(None)};
                let Some((_,next))=self.schema.types.get(type_name)
                    .and_then(|fields|fields.get(field.field.0 as usize))
                    else{return Ok(None)};
                current=next.clone();
                projections.push((field,current.clone()));
            }
            let expected=ConstType::RefMut(Box::new(current.clone()));
            if !self.same_type(&expected,&origin.ty){return Ok(None);}
        }else{
            for name in &named_fields {
                let Some((field,next))=self.field(&current,name)else{return Ok(None)};
                current=next.clone();
                projections.push((field,next));
            }
        }
        let dest_ty=ConstType::RefMut(Box::new(current));
        let mut statements=vec![Statement::StorageLive(Event{
            op:Access::StorageLive,path:Path::root(dest),
            loan:None,parent:None,token:start})];
        if let Some((name,summary,call_at,call_end))=forwarded {
            let mut audit=summary;
            audit.returned=None;
            for case in &mut audit.path_cases {case.returned=None;}
            let Some((operations,ConstType::Unit,None))=
                self.verified_user_call(call_at,call_end,&name,audit)else{
                return Ok(None);
            };
            statements.extend(operations);
        }
        let mut parent_generation=source.phi_generation.ok_or("missing source PHI generation")?;
        let mut parents=source.alternatives;
        let count=projections.len().max(1);
        for depth in 0..count {
            let last=depth+1==count;
            let owner=if last{dest}else{
                self.temp_id().ok_or("too many intermediate PHI binding IDs")?
            };
            let generation=self.temp_id().ok_or("too many late PHI generations")?;
            let step=projections.get(depth);
            let stage_ty=ConstType::RefMut(Box::new(match step {
                Some((_,ty))=>ty.clone(),
                None=>(**pointee).clone(),
            }));
            let mut children=Vec::with_capacity(parents.len());
            for option in &parents {
                let loan=self.temp_id().ok_or("too many late PHI loan identities")?;
                let path=match step {Some((field,_))=>option.path.child(*field),
                    None=>option.path.clone()};
                self.loans.insert(loan,path.clone());
                children.push(RefOption{loan,path,exclusive:true,
                    parent:Some(option.loan)});
            }
            if !last {
                statements.push(Statement::StorageLive(Event{op:Access::StorageLive,
                    path:Path::root(owner),loan:None,parent:None,token:start}));
            }
            statements.push(Statement::Access(Event{op:Access::Initialize,
                path:Path::root(owner),loan:None,parent:None,token:start}));
            statements.push(Statement::LatePhiReborrow{
                ty:stage_ty,source_generation:parent_generation,
                generation,children:children.clone(),
                projection:step.map(|(field,_)|*field),
                event:Event{op:Access::BindPhiMut,path:Path::root(owner),
                    loan:Some(generation),parent:Some(parent_generation),token:start},
            });
            parent_generation=generation;
            parents=children;
        }
        let blocks=self.add(tails.to_vec(),statements)?;
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty:dest_ty,reference:None,loan:None,borrow_parent:None,
            alternatives:parents,phi_generation:Some(parent_generation),mutable,
        });
        Ok(Some(blocks))
    }
    fn parse_if(&mut self,at:usize,limit:usize,from:Vec<usize>,
        loop_target:Option<(usize,usize,usize)>,depth:usize)
        ->Result<(Vec<usize>,usize),String>{
        if depth>64{return Err("typed MIR nesting limit exceeded".into());}
        let Some(brace)=(at+1..limit).find(|&p|self.kind(p)==Some(K::LBrace))else{
            self.unsupported=true;return Ok((Vec::new(),limit));
        };
        let Some(last)=self.close(brace,limit,K::LBrace,K::RBrace)else{
            self.unsupported=true;return Ok((Vec::new(),limit));
        };
        let Some((ops,ty,_))=self.expr(at+1,brace)else{
            self.unsupported=true;return Ok((Vec::new(),limit));
        };
        if ty!=ConstType::Bool {
            self.unsupported=true;return Ok((Vec::new(),limit));
        }
        let branch=self.add(from,ops)?[0];
        let yes=self.block()?;self.link(&[branch],yes);
        let yes_tails=self.parse_seq(brace+1..last,vec![yes],loop_target,depth+1)?;
        let no=self.block()?;self.link(&[branch],no);
        let mut next=last+1;
        let no_tails=if self.kind(next)==Some(K::Ident("else")) {
            next+=1;
            if self.kind(next)==Some(K::LBrace) {
                let Some(end)=self.close(next,limit,K::LBrace,K::RBrace)else{
                    self.unsupported=true;return Ok((Vec::new(),limit));
                };
                let result=self.parse_seq(next+1..end,vec![no],loop_target,depth+1)?;
                next=end+1;result
            }else if self.kind(next)==Some(K::Ident("if")) {
                let (result,end)=self.parse_if(next,limit,vec![no],loop_target,depth+1)?;
                next=end;result
            }else{
                self.unsupported=true;return Ok((Vec::new(),limit));
            }
        }else{vec![no]};
        Ok((yes_tails.into_iter().chain(no_tails).collect(),next))
    }
    fn result_arm(&mut self,range:Range<usize>,from:Vec<usize>,dest:SymbolId,
        depth:usize)->Result<Option<(Vec<usize>,ConstType,Vec<RefOption>)>,String>{
        if depth>64{return Err("typed MIR result nesting limit exceeded".into());}
        if range.start>=range.end{return Ok(None);}
        if matches!(self.kind(range.start),Some(K::Ident("if"))) {
            let at=range.start;
            let Some(brace)=(at+1..range.end).find(|&i|self.kind(i)==Some(K::LBrace))else{return Ok(None)};
            let Some(last)=self.close(brace,range.end,K::LBrace,K::RBrace)else{return Ok(None)};
            let Some((condition,ConstType::Bool,_))=self.expr(at+1,brace)else{return Ok(None)};
            let branch=self.add(from,condition)?[0];
            let yes=self.block()?;self.link(&[branch],yes);
            let Some((mut yes_tails,yes_type,mut yes_options))=self.result_arm(brace+1..last,vec![yes],dest,depth+1)? else{return Ok(None)};
            let no=self.block()?;self.link(&[branch],no);
            let next=last+1;
            if self.kind(next)!=Some(K::Ident("else")){return Ok(None)};
            let no_start=next+1;
            let no_result=if self.kind(no_start)==Some(K::LBrace){
                let Some(end)=self.close(no_start,range.end,K::LBrace,K::RBrace)else{return Ok(None)};
                if end!=range.end-1{return Ok(None)};
                self.result_arm(no_start+1..end,vec![no],dest,depth+1)?
            }else if self.kind(no_start)==Some(K::Ident("if")){
                self.result_arm(no_start..range.end,vec![no],dest,depth+1)?
            }else{return Ok(None)};
            let Some((no_tails,no_type,no_options))=no_result else{return Ok(None)};
            if yes_type!=no_type{return Ok(None)};
            yes_tails.extend(no_tails);
            yes_options.extend(no_options);
            return self.finish_value_phi(yes_tails,dest,yes_type,yes_options,at).map(Some);
        }
        if self.kind(range.start)==Some(K::Ident("match")) {
            let at=range.start;
            let Some(brace)=(at+1..range.end).find(|&i|self.kind(i)==Some(K::LBrace))else{return Ok(None)};
            let Some(last)=self.close(brace,range.end,K::LBrace,K::RBrace)else{return Ok(None)};
            if last!=range.end-1{return Ok(None)};
            let Some((scrutinee,scrutinee_type,_))=self.expr(at+1,brace)else{return Ok(None)};
            let branch=self.add(from,scrutinee)?[0];
            let (mut arm,mut predecessors,mut inferred)=(brace+1,Vec::new(),None);
            let mut options=Vec::new();
            let (mut has_true,mut has_false,mut wildcard)=(false,false,false);
            let mut enum_seen=0u128;
            let enum_variants=self.ty_id(&scrutinee_type)
                .and_then(|id|self.schema.type_names.get(id.0 as usize))
                .and_then(|name|self.schema.enums.get(name)
                    .map(|variants|(name.clone(),variants.clone())));
            while arm<last {
                if wildcard{return Ok(None);}
                let arrow=match self.kind(arm) {
                    Some(K::Ident("_"))=>{wildcard=true;arm+1},
                    Some(K::Ident("true")) if scrutinee_type==ConstType::Bool && !has_true=>{
                        has_true=true;arm+1
                    }
                    Some(K::Ident("false")) if scrutinee_type==ConstType::Bool && !has_false=>{
                        has_false=true;arm+1
                    }
                    Some(K::Ident(owner)) if enum_variants.is_some() &&
                        self.kind(arm+1)==Some(K::Colon) &&
                        self.kind(arm+2)==Some(K::Colon)=>{
                        let Some((enum_name,variants))=enum_variants.as_ref()
                            else{return Ok(None)};
                        if owner!=enum_name.as_str(){return Ok(None);}
                        let Some(K::Ident(variant))=self.kind(arm+3)else{return Ok(None)};
                        let Some(index)=variants.iter().position(|n|n.as_str()==variant)else{return Ok(None)};
                        let bit=1u128<<index;
                        if enum_seen&bit!=0{return Ok(None);}
                        enum_seen|=bit;arm+4
                    }
                    Some(K::Number(_)) if matches!(scrutinee_type,ConstType::I64|ConstType::U64)=>{
                        arm+1
                    }
                    _=>return Ok(None),
                };
                if self.kind(arrow)!=Some(K::FatArrow) ||
                    self.kind(arrow+1)!=Some(K::LBrace){return Ok(None)};
                let Some(end)=self.close(arrow+1,last,K::LBrace,K::RBrace)else{return Ok(None)};
                let entry=self.block()?;self.link(&[branch],entry);
                let Some((tails,ty,source))=self.result_arm(arrow+2..end,vec![entry],dest,depth+1)? else{return Ok(None)};
                if inferred.as_ref().is_some_and(|previous|previous!=&ty){return Ok(None)};
                inferred=Some(ty);
                options.extend(source);
                predecessors.extend(tails);
                arm=end+1;if self.kind(arm)==Some(K::Comma){arm+=1;}
            }
            let exhaustive=if let Some((_,variants))=enum_variants.as_ref() {
                wildcard || enum_seen.count_ones() as usize==variants.len()
            }else if scrutinee_type==ConstType::Bool {
                wildcard || (has_true && has_false)
            }else{wildcard};
            if !exhaustive{return Ok(None)};
            let Some(ty)=inferred else{return Ok(None)};
            return self.finish_value_phi(predecessors,dest,ty,options,at).map(Some);
        }
        let Some((mut ops,ty,provenance))=self.expr(range.start,range.end)else{return Ok(None)};
        let mut alternatives=Vec::new();
        match (&ty,&provenance) {
            (ConstType::Ref(_),Some((_,false,_)))|
            (ConstType::RefMut(_),Some((_,true,_))) => {
                let (path,exclusive,parent)=provenance.clone().expect("matched reference provenance");
                let loan=self.temp_id().ok_or("too many reference alternatives")?;
                ops.push(Statement::Access(Event{
                    op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
                    path:path.clone(),loan:Some(loan),parent,token:range.start,
                }));
                self.loans.insert(loan,path.clone());
                alternatives.push(RefOption{loan,path,exclusive,parent});
            }
            (ConstType::Ref(_)|ConstType::RefMut(_),_)|(_,Some(_))=>return Ok(None),
            _=>(),
        }
        ops.push(self.event(Access::Initialize,Path::root(dest),None,range.start));
        Ok(Some((self.add(from,ops)?,ty,alternatives)))
    }
    fn finish_value_phi(&mut self,predecessors:Vec<usize>,dest:SymbolId,ty:ConstType,
        alternatives:Vec<RefOption>,token:usize)
        ->Result<(Vec<usize>,ConstType,Vec<RefOption>),String>{
        if alternatives.len()>32{return Err("too many reference PHI alternatives".into());}
        if matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_))==alternatives.is_empty(){
            return Err("reference PHI missing alternative provenance".into());
        }
        let unanimous=alternatives.first().and_then(|first|{
            let same=alternatives.iter().all(|next|next.path==first.path &&
                next.exclusive==first.exclusive && next.parent==first.parent);
            same.then(||(first.path.clone(),first.exclusive,first.parent))
        });
        let phi_generation=if alternatives.is_empty(){None}else{
            Some(self.temp_id().ok_or("too many PHI generations")?)
        };
        let phi=self.block()?;
        self.link(&predecessors,phi);
        self.blocks[phi].statements.push(Statement::ValuePhi{
            ty:ty.clone(),predecessors,provenance:unanimous,
            alternatives:alternatives.clone(),generation:phi_generation,
            check:Event{op:Access::Read,path:Path::root(dest),loan:None,parent:None,token},
        });
        Ok((vec![phi],ty,alternatives))
    }
    //Every remaining MAY effect must occur in at least one of that origin's feasible cases
    fn restrict_return_origin(summary:&mut VerifiedCallSummary,index:usize)->bool {
        if summary.path_cases.is_empty(){return true;}
        //Soundness boundary: before pruning any return-origin cases, ensure their union equals the full MAY
        //summary
        let may=summary.parameter_effects.iter().cloned().collect::<HashSet<_>>();
        let witnessed=summary.path_cases.iter().flat_map(|case|
            case.effects.iter().cloned()).collect::<HashSet<_>>();
        if may!=witnessed || summary.field_writes.iter().any(|write|
            !may.contains(&VerifiedParameterEffect{
                parameter:write.parameter,fields:write.fields.clone(),
                kind:VerifiedEffectKind::Write,
            })) {return false;}
        summary.path_cases.retain(|case|case.returned==Some(index));
        if summary.path_cases.is_empty(){return false;}
        let effects=summary.path_cases.iter().flat_map(|case|case.effects.iter().cloned())
            .collect::<HashSet<_>>();
        summary.parameter_effects.retain(|effect|effects.contains(effect));
        summary.field_writes.retain(|write|effects.contains(&VerifiedParameterEffect{
            parameter:write.parameter,fields:write.fields.clone(),kind:VerifiedEffectKind::Write,
        }));
        for case in &mut summary.path_cases {case.returned=Some(0);}
        true
    }
    //The PHI establishes the complete set of possible owners, never a guessed common referent This
    //temporary result is retired at the function boundary
    fn projected_return_call(&mut self,start:usize,end:usize,from:Vec<usize>)
        ->Result<Option<Vec<usize>>,String>{
        let Some(K::Ident(name))=self.kind(start) else{return Ok(None)};
        let name=name.to_owned();
        if self.kind(start+1)!=Some(K::LParen) ||
            self.close(start+1,end,K::LParen,K::RParen)!=Some(end-1) {
            return Ok(None);
        }
        let Some(summary)=self.verified_calls.get(&name).cloned() else{return Ok(None)};
        if summary.returned_alternatives.len()<2 {return Ok(None);}
        if summary.returned.is_some() || summary.returned_alternatives.len()>32 {
            self.unsupported=true;return Ok(Some(Vec::new()));
        }
        let ty=summary.returned_alternatives[0].ty.clone();
        if !matches!(&ty,ConstType::Ref(_)|ConstType::RefMut(_)) ||
            summary.returned_alternatives.iter().any(|o|o.ty!=ty) {
            self.unsupported=true;return Ok(Some(Vec::new()));
        }
        let dest=self.temp_id().ok_or("too many returned-call temporaries")?;
        let root=Path::root(dest);
        let live=self.add(from,vec![Statement::StorageLive(Event{
            op:Access::StorageLive,path:root.clone(),loan:None,parent:None,token:start,
        })])?;
        let mut predecessors=Vec::with_capacity(summary.returned_alternatives.len());
        let mut alternatives=Vec::with_capacity(summary.returned_alternatives.len());
        for (origin_index,origin) in summary.returned_alternatives.iter().enumerate() {
            let mut one=summary.clone();
            if !Self::restrict_return_origin(&mut one,origin_index){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            one.returned=Some(origin.clone());
            one.returned_alternatives.clear();
            let Some((mut operations,result,returned))=
                self.verified_user_call(start,end,&name,one)else{
                self.unsupported=true;
                return Ok(Some(Vec::new()));
            };
            if result!=ty{self.unsupported=true;return Ok(Some(Vec::new()));}
            let Some((path,exclusive,parent))=returned else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let loan=self.temp_id().ok_or("too many returned-call loans")?;
            self.loans.insert(loan,path.clone());
            operations.push(Statement::Access(Event{
                op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
                path:path.clone(),loan:Some(loan),parent,token:start,
            }));
            operations.push(self.event(Access::Initialize,root.clone(),None,start));
            predecessors.extend(self.add(live.clone(),operations)?);
            alternatives.push(RefOption{loan,path,exclusive,parent});
        }
        let (joined,_,options)=self.finish_value_phi(predecessors,dest,ty,alternatives,start)?;
        let mut exit_events=options.iter().map(|option|self.event(
            Access::EndLoan,option.path.clone(),Some(option.loan),start)).collect::<Vec<_>>();
        exit_events.push(Statement::StorageDead(Event{
            op:Access::StorageDead,path:root,loan:None,parent:None,token:start,
        }));
        Ok(Some(self.add(joined,exit_events)?))
    }

    fn immediate_phi_multi_return_call(&mut self,start:usize,end:usize,from:&[usize])
        ->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")) || from.len()!=1 {
            return Ok(None);
        }
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable{i+=1;}
        let Some(K::Ident(dest_name))=self.kind(i)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        let dest=SymbolId(u32::try_from(i+1).map_err(|_|"too many MIR locals")?);
        if self.kind(i+1)!=Some(K::Equal){return Ok(None);}
        let call_at=i+2;
        let Some(K::Ident(callee))=self.kind(call_at)else{return Ok(None)};
        let callee=callee.to_owned();
        if self.kind(call_at+1)!=Some(K::LParen) ||
            self.close(call_at+1,end,K::LParen,K::RParen)!=Some(end-1){return Ok(None);}
        let Some(summary)=self.verified_calls.get(&callee).cloned()else{return Ok(None)};
        let origins=&summary.returned_alternatives;
        let count=summary.parameters.len();
        if summary.returned.is_some() || origins.len()<2 || origins.len()>4 ||
            count==0 || count>4 || summary.parameters.iter().any(|ty|
                !matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_))) ||
            summary.parameter_effects.iter().any(|effect|
                effect.kind!=VerifiedEffectKind::Write || effect.fields.is_empty() ||
                !matches!(summary.parameters.get(effect.parameter),Some(ConstType::RefMut(_)))) ||
            summary.field_writes.iter().any(|write|
                write.fields.is_empty() ||
                !matches!(summary.parameters.get(write.parameter),Some(ConstType::RefMut(_)))) ||
            ((!summary.parameter_effects.is_empty() || !summary.field_writes.is_empty()) &&
                summary.path_cases.is_empty()) {
            return Ok(None);
        }
        let ty=origins[0].ty.clone();
        if !matches!(&ty,ConstType::Ref(_)|ConstType::RefMut(_)) ||
            origins.iter().any(|origin|origin.ty!=ty ||
                origin.parameter>=count ||
                (matches!(&ty,ConstType::RefMut(_)) &&
                    !matches!(&summary.parameters[origin.parameter],ConstType::RefMut(_)))) ||
            summary.path_cases.iter().any(|case|
                case.returned.is_none_or(|index|index>=origins.len()) ||
                !case.uninitialized.is_empty()) {
            return Ok(None);
        }
        //A field-write witness cannot be silently omitted from the MAY effects: otherwise per-origin
        //restriction could discard it
        if summary.field_writes.iter().any(|write|
            !summary.parameter_effects.contains(&VerifiedParameterEffect{
                parameter:write.parameter,fields:write.fields.clone(),
                kind:VerifiedEffectKind::Write,
            })) {return Ok(None);}
        //All callee return alternatives must be backed by complete path cases when branch-correlated write
        //effects are used
        if !summary.path_cases.is_empty() &&
            ((0..origins.len()).any(|origin|
                !summary.path_cases.iter().any(|case|case.returned==Some(origin))) ||
             summary.path_cases.iter().flat_map(|case|case.effects.iter().cloned())
                .collect::<HashSet<_>>()!=summary.parameter_effects.iter().cloned()
                .collect::<HashSet<_>>()) {
            return Ok(None);
        }
        let call_args=self.split_top(call_at+2,end-1,K::Comma);
        if call_args.len()!=count || call_args.iter().any(|arg|arg.end!=arg.start+1){
            return Ok(None);
        }
        let mut sources=Vec::with_capacity(count);
        for (arg,formal) in call_args.iter().zip(&summary.parameters) {
            let Some(K::Ident(name))=self.kind(arg.start)else{return Ok(None)};
            let Some(source)=self.lookup(name)else{return Ok(None)};
            if !self.same_type(&source.ty,formal){return Ok(None);}
            sources.push(source);
        }
        let joined=from[0];
        let Some(join_block)=self.blocks.get(joined)else{return Ok(None)};
        if join_block.statements.is_empty() || join_block.statements.iter().any(|statement|
            !matches!(statement,Statement::ValuePhi{..})){
            return Ok(None);
        }
        let mut predecessors=Vec::<usize>::new();
        let mut phi_sources=Vec::<(SymbolId,Vec<RefOption>)>::new();
        //An older shared PHI may be an unrelated read-only parameter, but a returned parameter must have a PHI
        //at this exact merge
        for (index,source) in sources.iter().enumerate() {
            if source.alternatives.is_empty(){
                if source.reference.is_none() || source.loan.is_none(){return Ok(None);}
                continue;
            }
            let local_phi=join_block.statements.iter().find(|statement|
                matches!(statement,Statement::ValuePhi{check,..}
                    if check.path==Path::root(source.id)));
            let Some(Statement::ValuePhi{ty:source_ty,predecessors:incoming,
                alternatives,generation:Some(generation),..})=local_phi else{
                if origins.iter().any(|origin|origin.parameter==index) ||
                    source.phi_generation.is_none() ||
                    !matches!(&summary.parameters[index],
                        ConstType::Ref(_)|ConstType::RefMut(_)) ||
                    summary.parameter_effects.iter().any(|effect|
                        effect.parameter==index &&
                        (effect.kind!=VerifiedEffectKind::Write ||
                         !matches!(&summary.parameters[index],ConstType::RefMut(_)) ||
                         effect.fields.is_empty())) ||
                    summary.field_writes.iter().any(|effect|
                        effect.parameter==index &&
                        (!matches!(&summary.parameters[index],ConstType::RefMut(_)) ||
                         effect.fields.is_empty())) ||
                    summary.path_cases.iter().any(|case|
                        case.uninitialized.iter().any(|path|path.parameter==index)) ||
                    source.alternatives.is_empty() ||
                    source.alternatives.len()>32 ||
                    source.alternatives.iter().any(|option|
                        option.exclusive!=matches!(&summary.parameters[index],ConstType::RefMut(_)) ||
                        self.loans.get(&option.loan)!=Some(&option.path)) {
                    return Ok(None);
                }
                continue;
            };
            if source.phi_generation!=Some(*generation) ||
                &source.ty!=source_ty || alternatives!=&source.alternatives ||
                incoming.len()!=alternatives.len() || incoming.len()<2 ||
                incoming.len()>4 ||
                (!predecessors.is_empty() && predecessors.as_slice()!=incoming.as_slice()) {
                return Ok(None);
            }
            if predecessors.is_empty(){predecessors=incoming.clone();}
            phi_sources.push((source.id,alternatives.clone()));
        }
        if predecessors.is_empty() ||
            !origins.iter().any(|origin|phi_sources.iter().any(|(id,_)|
                *id==sources[origin.parameter].id)) ||
            origins.iter().any(|origin|sources[origin.parameter].alternatives.len()>0 &&
                !phi_sources.iter().any(|(id,_)|*id==sources[origin.parameter].id)) ||
            predecessors.len().saturating_mul(origins.len())>16 {
            return Ok(None);
        }
        //Every existing reference PHI at this node must be tracked and rebuilt; otherwise changing predecessors
        //would silently erase an independent binding's loan generation
        for statement in &join_block.statements {
            if let Statement::ValuePhi{ty:phi_ty,predecessors:incoming,
                check,alternatives,..}=statement {
                if incoming!=&predecessors ||
                    (matches!(phi_ty,ConstType::Ref(_)|ConstType::RefMut(_)) &&
                        (alternatives.len()!=incoming.len() ||
                         !phi_sources.iter().any(|(id,_)|*id==check.path.owner))) {
                    return Ok(None);
                }
            }
        }
        for (position,&pred) in predecessors.iter().enumerate() {
            let Some(block)=self.blocks.get(pred)else{return Ok(None)};
            if !matches!(&block.terminator,Terminator::Goto(targets)
                if targets.as_slice()==[joined]) {return Ok(None);}
            for (_,options) in &phi_sources {
                let option=&options[position];
                let op=if option.exclusive{Access::BorrowMut}else{Access::BorrowShared};
                if self.loans.get(&option.loan)!=Some(&option.path) ||
                    !block.statements.iter().any(|statement|matches!(statement,
                        Statement::Access(event) if event.op==op &&
                            event.loan==Some(option.loan) && event.path==option.path)) {
                    return Ok(None);
                }
            }
        }
        let mut expanded_predecessors=Vec::new();
        let mut output_options=Vec::new();
        let mut expanded_sources=HashMap::<SymbolId,Vec<RefOption>>::new();
        for (position,&pred) in predecessors.iter().enumerate() {
            let mut outgoing=Vec::new();
            for (origin_index,origin) in origins.iter().enumerate() {
                let mut case_summary=summary.clone();
                if !Self::restrict_return_origin(&mut case_summary,origin_index){
                    self.unsupported=true;return Ok(Some(Vec::new()));
                }
                case_summary.returned=Some(origin.clone());
                case_summary.returned_alternatives.clear();
                let mut prefix=Vec::<Statement>::new();
                let mut selected=Vec::<(SymbolId,RefOption)>::new();
                for (id,options) in &phi_sources {
                    let original=&options[position];
                    let child_loan=self.temp_id().ok_or("too many relational PHI loans")?;
                    self.loans.insert(child_loan,original.path.clone());
                    prefix.push(Statement::Access(Event{
                        op:if original.exclusive{Access::BorrowMut}else{Access::BorrowShared},
                        path:original.path.clone(),loan:Some(child_loan),
                        parent:Some(original.loan),token:start,
                    }));
                    let child=RefOption{loan:child_loan,path:original.path.clone(),
                        exclusive:original.exclusive,parent:Some(original.loan)};
                    expanded_sources.entry(*id).or_default().push(child.clone());
                    selected.push((*id,child));
                }
                let Some((operations,result,returned))=self.verified_user_call_on_edge(
                    call_at,end,&callee,case_summary,Some(&selected)) else{
                    self.unsupported=true;return Ok(Some(Vec::new()));
                };
                let Some((path,exclusive,parent))=returned else{
                    self.unsupported=true;return Ok(Some(Vec::new()));
                };
                let expected_parent=selected.iter().find_map(|(id,option)|
                    (*id==sources[origin.parameter].id).then_some(option.loan))
                    .or(sources[origin.parameter].loan);
                if result!=ty || exclusive!=matches!(&ty,ConstType::RefMut(_)) ||
                    parent!=expected_parent {
                    self.unsupported=true;return Ok(Some(Vec::new()));
                }
                let loan=self.temp_id().ok_or("too many relational call result loans")?;
                self.loans.insert(loan,path.clone());
                prefix.push(Statement::StorageLive(Event{
                    op:Access::StorageLive,path:Path::root(dest),
                    loan:None,parent:None,token:start,
                }));
                prefix.extend(operations);
                prefix.push(Statement::Access(Event{
                    op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
                    path:path.clone(),loan:Some(loan),parent,token:start,
                }));
                prefix.push(self.event(Access::Initialize,Path::root(dest),None,start));
                let child=self.block()?;
                self.blocks[child].statements=prefix;
                self.blocks[child].terminator=Terminator::Goto(vec![joined]);
                outgoing.push(child);
                expanded_predecessors.push(child);
                output_options.push(RefOption{loan,path,exclusive,parent});
            }
            self.blocks[pred].terminator=Terminator::Goto(outgoing);
        }
        for statement in &mut self.blocks[joined].statements {
            if let Statement::ValuePhi{ty:phi_ty,predecessors,check,
                alternatives,provenance,..}=statement {
                *predecessors=expanded_predecessors.clone();
                if matches!(phi_ty,ConstType::Ref(_)|ConstType::RefMut(_)) {
                    let Some(children)=expanded_sources.get(&check.path.owner)else{
                        self.unsupported=true;return Ok(Some(Vec::new()));
                    };
                    *alternatives=children.clone();
                    *provenance=children.first().and_then(|first|
                        children.iter().all(|next|next.path==first.path &&
                            next.exclusive==first.exclusive && next.parent==first.parent)
                            .then(||(first.path.clone(),first.exclusive,first.parent)));
                }
            }
        }
        for (id,options) in expanded_sources {
            let mut found=false;
            for scope in self.scopes.iter_mut().rev() {
                if let Some(binding)=scope.values_mut().find(|binding|binding.id==id) {
                    binding.alternatives=options;
                    found=true;
                    break;
                }
            }
            if !found {self.unsupported=true;return Ok(Some(Vec::new()));}
        }
        let generation=self.temp_id().ok_or("too many relational result PHI generations")?;
        let uniform=output_options.first().and_then(|first|
            output_options.iter().all(|next|next.path==first.path &&
                next.exclusive==first.exclusive && next.parent==first.parent)
                .then(||(first.path.clone(),first.exclusive,first.parent)));
        self.blocks[joined].statements.push(Statement::ValuePhi{
            ty:ty.clone(),predecessors:expanded_predecessors,
            check:Event{op:Access::Read,path:Path::root(dest),
                loan:None,parent:None,token:start},
            alternatives:output_options.clone(),provenance:uniform,
            generation:Some(generation),
        });
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty,reference:None,loan:None,borrow_parent:None,
            alternatives:output_options,phi_generation:Some(generation),mutable,
        });
        Ok(Some(from.to_vec()))
    }

    fn immediate_phi_forward_call(&mut self,start:usize,end:usize,from:&[usize])
        ->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")) || from.len()!=1 {
            return Ok(None);
        }
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable{i+=1;}
        let Some(K::Ident(dest_name))=self.kind(i)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        let dest=SymbolId(u32::try_from(i+1).map_err(|_|"too many MIR locals")?);
        if self.kind(i+1)!=Some(K::Equal){return Ok(None);}
        let call_at=i+2;
        let Some(K::Ident(callee))=self.kind(call_at)else{return Ok(None)};
        let callee=callee.to_owned();
        if self.kind(call_at+1)!=Some(K::LParen) ||
            self.close(call_at+1,end,K::LParen,K::RParen)!=Some(end-1) {
            return Ok(None);
        }
        let Some(summary)=self.verified_calls.get(&callee).cloned()else{return Ok(None)};
        let Some(origin)=summary.returned.as_ref()else{return Ok(None)};
        let count=summary.parameters.len();
        if count==0 || count>4 || origin.parameter>=count ||
            !summary.returned_alternatives.is_empty() ||
            !summary.field_writes.is_empty() || !summary.parameter_effects.is_empty() ||
            summary.path_cases.iter().any(|case|
                !case.effects.is_empty() || !case.uninitialized.is_empty()) ||
            summary.parameters.iter().any(|ty|
                !matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_))) {
            return Ok(None);
        }
        let call_args=self.split_top(call_at+2,end-1,K::Comma);
        if call_args.len()!=count || call_args.iter().any(|arg|
            arg.end!=arg.start+1) {return Ok(None);}
        let mut sources=Vec::with_capacity(count);
        for (arg,formal) in call_args.iter().zip(&summary.parameters) {
            let Some(K::Ident(source_name))=self.kind(arg.start)else{return Ok(None)};
            let Some(source)=self.lookup(source_name)else{return Ok(None)};
            if !self.same_type(&source.ty,formal){return Ok(None);}
            sources.push(source);
        }
        let joined=from[0];
        //A borrow can be pushed onto the incoming edges only if no other operation has already been performed
        //after the merge
        if self.blocks.get(joined).is_none_or(|block|
            block.statements.iter().any(|statement|
                !matches!(statement,Statement::ValuePhi{..}))) {
            return Ok(None);
        }
        let output_source=&sources[origin.parameter];
        if output_source.alternatives.len()<2 ||
            output_source.alternatives.len()>32 {return Ok(None);}
        let result_ty=origin.ty.clone();
        let exclusive=matches!(&result_ty,ConstType::RefMut(_));
        if !matches!(&result_ty,ConstType::Ref(_)|ConstType::RefMut(_)) ||
            exclusive!=matches!(&summary.parameters[origin.parameter],ConstType::RefMut(_)) {
            return Ok(None);
        }
        let mut predecessors=Vec::<usize>::new();
        let mut phi_sources=Vec::<(SymbolId,Vec<RefOption>)>::new();
        for (parameter,source) in sources.iter().enumerate() {
            if source.alternatives.is_empty(){
                if source.reference.is_none() || source.loan.is_none(){return Ok(None);}
                continue;
            }
            let Some(generation)=source.phi_generation else{return Ok(None)};
            let local_phi=self.blocks[joined].statements.iter().rev().find(|statement|
                matches!(statement,Statement::ValuePhi{check,..}
                    if check.path==Path::root(source.id)));
            if local_phi.is_none() && parameter!=origin.parameter &&
                matches!(&summary.parameters[parameter],ConstType::Ref(_)) &&
                source.alternatives.len()<=32 &&
                source.alternatives.iter().all(|option|!option.exclusive &&
                    self.loans.get(&option.loan)==Some(&option.path)) {
                continue;
            }
            let Some(Statement::ValuePhi{predecessors:incoming,check:_,
                alternatives,generation:Some(actual_generation),..})=local_phi
                else{return Ok(None)};
            if *actual_generation!=generation || alternatives!=&source.alternatives ||
                incoming.len()!=alternatives.len() || incoming.len()<2 ||
                incoming.len()>32 ||
                (!predecessors.is_empty() && predecessors.as_slice()!=incoming.as_slice()) {
                return Ok(None);
            }
            if predecessors.is_empty(){predecessors=incoming.clone();}
            phi_sources.push((source.id,alternatives.clone()));
        }
        if predecessors.is_empty() ||
            phi_sources.len()>count ||
            !phi_sources.iter().any(|(id,_)|*id==output_source.id) {
            return Ok(None);
        }
        for (position,&pred) in predecessors.iter().enumerate() {
            let Some(block)=self.blocks.get(pred)else{return Ok(None)};
            if !matches!(&block.terminator,Terminator::Goto(next)
                if next.as_slice()==[joined]) {return Ok(None);}
            for (_,options) in &phi_sources {
                let option=&options[position];
                let op=if option.exclusive{Access::BorrowMut}else{Access::BorrowShared};
                if self.loans.get(&option.loan)!=Some(&option.path) ||
                    !block.statements.iter().any(|stmt|matches!(stmt,
                        Statement::Access(event) if event.loan==Some(option.loan) &&
                        event.path==option.path && event.op==op)) {
                    return Ok(None);
                }
            }
        }
        //All alternatives must be prepared before mutating the original CFG. An internal failure must never
        //publish a partial certificate
        let mut prepared=Vec::with_capacity(predecessors.len());
        for position in 0..predecessors.len() {
            let selected=phi_sources.iter().map(|(id,options)|
                (*id,options[position].clone())).collect::<Vec<_>>();
            let Some((mut operations,actual,returned))=
                self.verified_user_call_on_edge(call_at,end,&callee,summary.clone(),
                    Some(&selected)) else {
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let Some((path,result_mut,parent))=returned else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let origin_loan=selected.iter().find_map(|(id,option)|
                (*id==output_source.id).then_some(option.loan));
            if actual!=result_ty || result_mut!=exclusive || parent!=origin_loan {
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            let loan=self.temp_id().ok_or("too many forwarded PHI loans")?;
            self.loans.insert(loan,path.clone());
            let root=Path::root(dest);
            operations.insert(0,Statement::StorageLive(Event{
                op:Access::StorageLive,path:root.clone(),loan:None,parent:None,token:start,
            }));
            operations.push(Statement::Access(Event{
                op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
                path:path.clone(),loan:Some(loan),parent,token:start,
            }));
            operations.push(self.event(Access::Initialize,root,None,start));
            prepared.push((operations,RefOption{loan,path,exclusive,parent}));
        }
        let mut results=Vec::with_capacity(prepared.len());
        for (&pred,(operations,option)) in predecessors.iter().zip(prepared) {
            self.blocks[pred].statements.extend(operations);
            results.push(option);
        }
        let uniform=results.first().and_then(|first|results.iter().all(|option|
            option.path==first.path && option.exclusive==first.exclusive &&
            option.parent==first.parent)
            .then(||(first.path.clone(),first.exclusive,first.parent)));
        let phi_generation=self.temp_id().ok_or("too many forwarded PHI generations")?;
        self.blocks[joined].statements.push(Statement::ValuePhi{
            ty:result_ty.clone(),predecessors,provenance:uniform,
            alternatives:results.clone(),generation:Some(phi_generation),
            check:Event{op:Access::Read,path:Path::root(dest),
                loan:None,parent:None,token:start},
        });
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty:result_ty,reference:None,loan:None,borrow_parent:None,
            alternatives:results,phi_generation:Some(phi_generation),mutable,
        });
        Ok(Some(from.to_vec()))
    }

    fn immediate_nested_phi_forward_call(&mut self,start:usize,end:usize,from:&[usize])
        ->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")) || from.len()!=1 {
            return Ok(None);
        }
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable {i+=1;}
        let Some(K::Ident(dest_name))=self.kind(i)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        let dest=SymbolId(u32::try_from(i+1).map_err(|_|"too many MIR locals")?);
        if self.kind(i+1)!=Some(K::Equal) || self.scopes.last()
            .is_some_and(|scope|scope.contains_key(&dest_name)) {return Ok(None);}
        let call_at=i+2;
        let mut at=call_at;
        let mut until=end;
        let mut chain=Vec::<(String,VerifiedCallSummary)>::new();
        let source_name=loop {
            let Some(K::Ident(name))=self.kind(at)else{return Ok(None)};
            if self.kind(at+1)!=Some(K::LParen) ||
                self.close(at+1,until,K::LParen,K::RParen)!=Some(until-1) {
                return Ok(None);
            }
            let Some(summary)=self.verified_calls.get(name).cloned()else{return Ok(None)};
            let Some(origin)=summary.returned.as_ref()else{return Ok(None)};
            if summary.parameters.len()!=1 || origin.parameter!=0 ||
                !summary.returned_alternatives.is_empty() {
                return Ok(None);
            }
            let (ConstType::RefMut(input),ConstType::RefMut(output))=
                (&summary.parameters[0],&origin.ty)else{return Ok(None)};
            //Never derive field offsets or field types from a name-only provenance. Each step must exist in the
            //callee's typed schema
            let Some((_,projected))=self.project_verified(
                &Path::root(SymbolId(0)),input,&origin.fields)else{return Ok(None)};
            if !self.same_type(&projected,output){return Ok(None);}

            let may=summary.parameter_effects.iter().cloned()
                .collect::<HashSet<_>>();
            let witnessed=summary.path_cases.iter().flat_map(|case|
                case.effects.iter().cloned()).collect::<HashSet<_>>();
            let effectful=!may.is_empty() || !summary.field_writes.is_empty();
            if summary.path_cases.len()>8 || summary.parameter_effects.len()>8 ||
                summary.path_cases.iter().any(|case|
                    case.returned!=Some(0) || !case.uninitialized.is_empty()) ||
                (effectful && (summary.path_cases.is_empty() || may.is_empty() ||
                    may!=witnessed ||
                    summary.parameter_effects.iter().any(|effect|
                        effect.parameter!=0 || effect.kind!=VerifiedEffectKind::Write ||
                        effect.fields.is_empty()) ||
                    summary.field_writes.iter().any(|field|
                        field.parameter!=0 || field.fields.is_empty() ||
                        !may.contains(&VerifiedParameterEffect{
                            parameter:field.parameter,fields:field.fields.clone(),
                            kind:VerifiedEffectKind::Write,
                        })) ||
                    summary.path_cases.iter().any(|case|
                        case.effects.iter().any(|effect|!may.contains(effect))))) ||
                (!effectful && summary.path_cases.iter().any(|case|
                    !case.effects.is_empty())) {
                return Ok(None);
            }
            let args=self.split_top(at+2,until-1,K::Comma);
            if args.len()!=1 {return Ok(None);}
            let arg=&args[0];
            chain.push((name.to_owned(),summary));
            if chain.len()>12 {return Ok(None);}
            if arg.end==arg.start+1 {
                let Some(K::Ident(source))=self.kind(arg.start)else{return Ok(None)};
                break source.to_owned();
            }
            at=arg.start;
            until=arg.end;
        };
        if chain.len()<2 {return Ok(None);}
        let Some(source)=self.lookup(&source_name)else{return Ok(None)};
        if source.phi_generation.is_none() || source.alternatives.len()<2 ||
            source.alternatives.len()>32 ||
            !self.same_type(&source.ty,&chain.last().unwrap().1.parameters[0]) ||
            source.alternatives.iter().any(|option|!option.exclusive ||
                self.loans.get(&option.loan)!=Some(&option.path)) {
            return Ok(None);
        }
        for index in 0..chain.len()-1 {
            if !self.same_type(&chain[index].1.parameters[0],
                    &chain[index+1].1.returned.as_ref().unwrap().ty) {
                return Ok(None);
            }
        }
        let joined=from[0];
        let Some(block)=self.blocks.get(joined)else{return Ok(None)};
        if block.statements.iter().any(|statement|
            !matches!(statement,Statement::ValuePhi{..})) {return Ok(None);}
        let generation=source.phi_generation.unwrap();
        let Some(Statement::ValuePhi{predecessors,alternatives,
                generation:Some(actual_generation),..})=block.statements.iter().rev()
                    .find(|statement|matches!(statement,Statement::ValuePhi{check,..}
                        if check.path==Path::root(source.id)))else{return Ok(None)};
        if *actual_generation!=generation || alternatives!=&source.alternatives ||
            predecessors.len()!=alternatives.len(){return Ok(None);}
        let predecessors=predecessors.clone();
        for (pred,option) in predecessors.iter().zip(&source.alternatives) {
            let Some(input)=self.blocks.get(*pred)else{return Ok(None)};
            if !matches!(&input.terminator,Terminator::Goto(next)
                if next.as_slice()==[joined]) ||
                !input.statements.iter().any(|stmt|matches!(stmt,
                    Statement::Access(event) if event.op==Access::BorrowMut &&
                    event.loan==Some(option.loan) && event.path==option.path)) {
                return Ok(None);
            }
        }
        let (outer_name,outer_summary)=chain[0].clone();
        let result_ty=outer_summary.returned.as_ref().unwrap().ty.clone();
        let mut prepared=Vec::with_capacity(predecessors.len());
        for option in &source.alternatives {
            let mut expected_path=option.path.clone();
            let mut expected_ty=source.ty.clone();
            for (_,summary) in chain.iter().rev() {
                if !self.same_type(&expected_ty,&summary.parameters[0]) {
                    self.unsupported=true;return Ok(Some(Vec::new()));
                }
                let ConstType::RefMut(input)=&summary.parameters[0] else {
                    self.unsupported=true;return Ok(Some(Vec::new()));
                };
                let origin=summary.returned.as_ref().expect("checked return origin");
                let Some((next_path,next_ty))=self.project_verified(
                    &expected_path,input,&origin.fields)else{
                    self.unsupported=true;return Ok(Some(Vec::new()));
                };
                if !self.same_type(&ConstType::RefMut(Box::new(next_ty)),&origin.ty) {
                    self.unsupported=true;return Ok(Some(Vec::new()));
                }
                expected_path=next_path;
                expected_ty=origin.ty.clone();
            }
            let selected=[(source.id,option.clone())];
            let Some((mut operations,actual,Some((path,exclusive,parent))))=
                self.verified_user_call_on_edge(call_at,end,&outer_name,
                    outer_summary.clone(),Some(&selected))else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            if !self.same_type(&actual,&result_ty) || !exclusive ||
                path!=expected_path {
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            let mut ancestor=parent;
            let mut required_path=path.clone();
            let mut visited=HashSet::new();
            let mut found=false;
            for _ in 0..=chain.len()*3 {
                let Some(loan)=ancestor else{break};
                if loan==option.loan {
                    found=option.path.ancestor_of(&required_path);
                    break;
                }
                if !visited.insert(loan) {break;}
                let links=operations.iter().flat_map(|stmt|stmt.events())
                    .filter(|event|event.op==Access::BorrowMut &&
                        event.loan==Some(loan))
                    .collect::<Vec<_>>();
                if links.len()!=1 || !links[0].path.ancestor_of(&required_path) {break;}
                //An ancestor ended before this result cannot certify it
                if operations.iter().flat_map(|stmt|stmt.events()).any(|event|
                    event.op==Access::EndLoan && event.loan==Some(loan)) {break;}
                required_path=links[0].path.clone();
                ancestor=links[0].parent;
            }
            if !found {self.unsupported=true;return Ok(Some(Vec::new()));}
            let loan=self.temp_id().ok_or("too many nested PHI loans")?;
            self.loans.insert(loan,path.clone());
            operations.insert(0,Statement::StorageLive(Event{
                op:Access::StorageLive,path:Path::root(dest),loan:None,
                parent:None,token:start,
            }));
            operations.push(Statement::Access(Event{op:Access::BorrowMut,
                path:path.clone(),loan:Some(loan),parent,token:start}));
            operations.push(self.event(Access::Initialize,Path::root(dest),None,start));
            prepared.push((operations,RefOption{loan,path,exclusive,parent}));
        }
        let mut results=Vec::with_capacity(prepared.len());
        for (&pred,(statements,option)) in predecessors.iter().zip(prepared) {
            self.blocks[pred].statements.extend(statements);
            results.push(option);
        }
        let uniform=results.first().and_then(|first|results.iter().all(|option|
            option.path==first.path && option.exclusive==first.exclusive &&
            option.parent==first.parent).then(||(first.path.clone(),true,first.parent)));
        let phi_generation=self.temp_id().ok_or("too many nested PHI generations")?;
        self.blocks[joined].statements.push(Statement::ValuePhi{
            ty:result_ty.clone(),predecessors,provenance:uniform,
            alternatives:results.clone(),generation:Some(phi_generation),
            check:Event{op:Access::Read,path:Path::root(dest),
                loan:None,parent:None,token:start},
        });
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty:result_ty,reference:None,loan:None,borrow_parent:None,
            alternatives:results,phi_generation:Some(phi_generation),mutable,
        });
        Ok(Some(from.to_vec()))
    }

    fn projected_call_let(&mut self,start:usize,end:usize,from:Vec<usize>)
        ->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")){return Ok(None);}
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable{i+=1;}
        let Some(K::Ident(dest_name))=self.kind(i)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        let dest=SymbolId(u32::try_from(i+1).map_err(|_|"too many MIR locals")?);
        i+=1;
        if self.kind(i)!=Some(K::Equal){return Ok(None);}
        i+=1;
        let Some(K::Ident(callee))=self.kind(i)else{return Ok(None)};
        let callee=callee.to_owned();
        if self.kind(i+1)!=Some(K::LParen) ||
            self.close(i+1,end,K::LParen,K::RParen)!=Some(end-1){return Ok(None);}
        let Some(summary)=self.verified_calls.get(&callee).cloned()else{return Ok(None)};
        if summary.returned_alternatives.len()<2{return Ok(None);}
        if !summary.path_cases.is_empty() {
            let expected=summary.parameter_effects.iter().cloned().collect::<HashSet<_>>();
            let proved=summary.path_cases.iter().flat_map(|case|
                case.effects.iter().cloned()).collect::<HashSet<_>>();
            if expected!=proved || summary.field_writes.iter().any(|write|
                !expected.contains(&VerifiedParameterEffect{
                    parameter:write.parameter,fields:write.fields.clone(),
                    kind:VerifiedEffectKind::Write,
                })) {
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
        }
        if summary.returned.is_some() || summary.returned_alternatives.len()>32 {
            self.unsupported=true;return Ok(Some(Vec::new()));
        }
        let first_ty=summary.returned_alternatives[0].ty.clone();
        if !matches!(&first_ty,ConstType::Ref(_)|ConstType::RefMut(_)) ||
            summary.returned_alternatives.iter().any(|o|o.ty!=first_ty) {
            self.unsupported=true;return Ok(Some(Vec::new()));
        }
        let live=self.add(from,vec![Statement::StorageLive(Event{
            op:Access::StorageLive,path:Path::root(dest),loan:None,parent:None,token:start})])?;
        let mut predecessors=Vec::new();
        let mut options=Vec::new();
        for (origin_index,origin) in summary.returned_alternatives.iter().enumerate() {
            let mut individual=summary.clone();
            if !Self::restrict_return_origin(&mut individual,origin_index){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            individual.returned=Some(origin.clone());
            individual.returned_alternatives.clear();
            let Some((mut ops,result,returned))=
                self.verified_user_call(i,end,&callee,individual)else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            if result!=first_ty {self.unsupported=true;return Ok(Some(Vec::new()));}
            let Some((path,exclusive,parent))=returned else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let loan=self.temp_id().ok_or("too many call result loans")?;
            self.loans.insert(loan,path.clone());
            ops.push(Statement::Access(Event{
                op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
                path:path.clone(),loan:Some(loan),parent,token:start,
            }));
            ops.push(self.event(Access::Initialize,Path::root(dest),None,start));
            let tail=self.add(live.clone(),ops)?;
            predecessors.extend(tail);
            options.push(RefOption{loan,path,exclusive,parent});
        }
        let (tails,ty,alternatives)=self.finish_value_phi(
            predecessors,dest,first_ty,options,start)?;
        let generation=self.phi_generation(&tails,dest)
            .ok_or("missing call-PHI generation")?;
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty,reference:None,loan:None,borrow_parent:None,
            alternatives,phi_generation:Some(generation),mutable,
        });
        Ok(Some(tails))
    }
    fn ordered_effectful_phi_return_call(&mut self,start:usize,end:usize,from:&[usize])
        ->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")) || from.len()!=1 {
            return Ok(None);
        }
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable{i+=1;}
        let Some(K::Ident(dest_name))=self.kind(i)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        let dest=SymbolId(u32::try_from(i+1).map_err(|_|"too many MIR locals")?);
        if self.kind(i+1)!=Some(K::Equal) || self.scopes.last()
            .is_some_and(|scope|scope.contains_key(&dest_name)) {return Ok(None);}
        let at=i+2;
        let Some(K::Ident(callee))=self.kind(at)else{return Ok(None)};
        let callee=callee.to_owned();
        if self.kind(at+1)!=Some(K::LParen) ||
            self.close(at+1,end,K::LParen,K::RParen)!=Some(end-1){return Ok(None);}
        let Some(summary)=self.verified_calls.get(&callee).cloned()else{return Ok(None)};
        let args=self.split_top(at+2,end-1,K::Comma);
        let count=summary.parameters.len();
        if count<2 || count>4 || args.len()!=count{return Ok(None);}
        let later_nested=args.iter().skip(1).any(|arg|
            matches!(self.kind(arg.start),Some(K::Ident(_))) &&
            self.kind(arg.start+1)==Some(K::LParen) &&
            self.close(arg.start+1,arg.end,K::LParen,K::RParen)==Some(arg.end-1));
        if !later_nested{return Ok(None);}
        let origins=if let Some(origin)=&summary.returned {
            if !summary.returned_alternatives.is_empty(){return Ok(None);}
            vec![origin.clone()]
        }else{summary.returned_alternatives.clone()};
        if origins.is_empty(){return Ok(None);}
        if !origins.iter().all(|origin|{
            let Some(arg)=args.get(origin.parameter)else{return false};
            if arg.end!=arg.start+1{return false;}
            let Some(K::Ident(name))=self.kind(arg.start)else{return false};
            self.lookup(name).is_some_and(|source|
                source.phi_generation.is_some() && !source.alternatives.is_empty())
        }) {return Ok(None);}
        if summary.parameter_effects.is_empty() && summary.field_writes.is_empty(){
            return Ok(None);
        }
        let first_ty=origins[0].ty.clone();
        if !matches!(&first_ty,ConstType::RefMut(_)) || origins.len()>4 ||
            origins.iter().any(|origin|origin.ty!=first_ty ||
                origin.parameter>=count || origin.fields.len()>16) {
            return Ok(None);
        }
        //The complete, fully verified callee certificate is a prerequisite for pruning by case. Never create a
        //case from a mere MAY summary
        let may=summary.parameter_effects.iter().cloned().collect::<HashSet<_>>();
        let witnessed=summary.path_cases.iter().flat_map(|case|
            case.effects.iter().cloned()).collect::<HashSet<_>>();
        let valid=!may.is_empty() && may==witnessed &&
            !summary.path_cases.is_empty() && summary.path_cases.len()<=16 &&
            summary.parameters.iter().all(|formal|
                matches!(formal,ConstType::Ref(_)|ConstType::RefMut(_))) &&
            summary.parameter_effects.iter().all(|effect|
                effect.kind==VerifiedEffectKind::Write && !effect.fields.is_empty() &&
                matches!(summary.parameters.get(effect.parameter),Some(ConstType::RefMut(_)))) &&
            summary.field_writes.iter().all(|write|may.contains(&VerifiedParameterEffect{
                parameter:write.parameter,fields:write.fields.clone(),
                kind:VerifiedEffectKind::Write,
            })) &&
            summary.path_cases.iter().all(|case|
                case.returned.is_some_and(|origin|origin<origins.len()) &&
                case.uninitialized.is_empty() &&
                case.effects.iter().all(|effect|may.contains(effect))) &&
            (0..origins.len()).all(|index|summary.path_cases.iter()
                .any(|case|case.returned==Some(index)));
        if !valid {self.unsupported=true;return Ok(Some(Vec::new()));}
        //Every returned parameter must be exactly a pre-existing reference PHI
        let mut sources=Vec::<Binding>::with_capacity(origins.len());
        let mut total=0usize;
        for origin in &origins {
            let arg=&args[origin.parameter];
            if arg.end!=arg.start+1 ||
                !matches!(summary.parameters.get(origin.parameter),Some(ConstType::RefMut(_))) {
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            let Some(K::Ident(name))=self.kind(arg.start)else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let Some(source)=self.lookup(name)else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            if !self.same_type(&source.ty,&summary.parameters[origin.parameter]) ||
                source.reference.is_some() || source.loan.is_some() ||
                source.phi_generation.is_none() ||
                source.alternatives.len()<2 || source.alternatives.len()>32 ||
                source.alternatives.iter().any(|candidate|
                    !candidate.exclusive ||
                    self.loans.get(&candidate.loan)!=Some(&candidate.path)) {
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            let cases=summary.path_cases.iter().filter(|case|
                case.returned==Some(sources.len())).count();
            total=total.saturating_add(cases.saturating_mul(source.alternatives.len()));
            sources.push(source);
        }
        if total==0 || total>32 {self.unsupported=true;return Ok(Some(Vec::new()));}
        let mut direct=Vec::<Option<(bool,Vec<Path>)>>::with_capacity(count);
        for (arg,formal) in args.iter().zip(&summary.parameters) {
            let exclusive=matches!(formal,ConstType::RefMut(_));
            let paths=if self.kind(arg.start)==Some(K::Amp) {
                let mut at=arg.start+1;
                if self.kind(at)==Some(K::Ident("mut")){at+=1;}
                self.resolve_path(at,arg.end).map(|(path,_,_)|vec![path])
            }else if arg.end==arg.start+1 {
                match self.kind(arg.start) {
                    Some(K::Ident(name))=>self.lookup(name).and_then(|binding|{
                        if !binding.alternatives.is_empty(){
                            Some(binding.alternatives.iter().map(|o|o.path.clone()).collect())
                        }else{binding.reference.map(|(path,_)|vec![path])}
                    }),
                    _=>None,
                }
            }else{None};
            direct.push(paths.map(|paths|(exclusive,paths)));
        }
        for a in 0..count {for b in a+1..count {
            let (Some((exclusive_a,paths_a)),Some((exclusive_b,paths_b)))=
                (&direct[a],&direct[b])else{continue};
            if !*exclusive_a && !*exclusive_b {continue;}
            if paths_a.iter().any(|x|paths_b.iter().any(|y|
                x.ancestor_of(y) || y.ancestor_of(x))) {
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
        }}
        let live=self.add(from.to_vec(),vec![Statement::StorageLive(Event{
            op:Access::StorageLive,path:Path::root(dest),loan:None,parent:None,token:start,
        })])?;
        let mut predecessors=Vec::with_capacity(summary.path_cases.len());
        let mut options=Vec::<RefOption>::with_capacity(total);
        //A separate successor represents each possible return-origin AND each correlated callee effect case,
        //never a Cartesian product of unrelated effects
        for case in &summary.path_cases {
            let index=case.returned.expect("certified return index");
            let origin=&origins[index];
            let source=&sources[index];
            let mut restricted=summary.clone();
            restricted.returned=None;
            restricted.returned_alternatives.clear();
            restricted.parameter_effects=case.effects.clone();
            restricted.field_writes.retain(|write|case.effects.contains(
                &VerifiedParameterEffect{parameter:write.parameter,
                    fields:write.fields.clone(),kind:VerifiedEffectKind::Write}));
            restricted.path_cases=vec![VerifiedPathCase{
                effects:case.effects.clone(),returned:None,uninitialized:Vec::new(),
            }];
            let Some((mut operations,ConstType::Unit,None))=
                self.verified_user_call(at,end,&callee,restricted)else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let ConstType::RefMut(inner)=&summary.parameters[origin.parameter]else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let mut pointee=(**inner).clone();
            let mut generation=source.phi_generation.expect("checked PHI generation");
            let mut parents=source.alternatives.clone();
            let stages=origin.fields.len().max(1);
            for depth in 0..stages {
                let step=origin.fields.get(depth).copied();
                if let Some(field)=step {
                    if self.ty_id(&pointee)!=Some(field.aggregate){
                        self.unsupported=true;return Ok(Some(Vec::new()));
                    }
                    let Some(name)=self.schema.type_names.get(field.aggregate.0 as usize)else{
                        self.unsupported=true;return Ok(Some(Vec::new()));
                    };
                    let Some((_,next))=self.schema.types.get(name)
                        .and_then(|fields|fields.get(field.field.0 as usize))else{
                        self.unsupported=true;return Ok(Some(Vec::new()));
                    };
                    pointee=next.clone();
                }
                let last=depth+1==stages;
                let owner=if last{dest}else{
                    self.temp_id().ok_or("too many ordered PHI stage locals")?
                };
                if !last {operations.push(Statement::StorageLive(Event{
                    op:Access::StorageLive,path:Path::root(owner),
                    loan:None,parent:None,token:start,
                }));}
                operations.push(self.event(Access::Initialize,Path::root(owner),None,start));
                let next_generation=self.temp_id().ok_or("too many ordered PHI generations")?;
                let mut children=Vec::with_capacity(parents.len());
                for parent in &parents {
                    let loan=self.temp_id().ok_or("too many ordered PHI child loans")?;
                    let path=step.map_or_else(||parent.path.clone(),|field|
                        parent.path.child(field));
                    self.loans.insert(loan,path.clone());
                    children.push(RefOption{
                        loan,path,exclusive:true,parent:Some(parent.loan),
                    });
                }
                operations.push(Statement::LatePhiReborrow{
                    ty:ConstType::RefMut(Box::new(pointee.clone())),
                    source_generation:generation,generation:next_generation,
                    projection:step,children:children.clone(),
                    event:Event{op:Access::BindPhiMut,path:Path::root(owner),
                        loan:Some(next_generation),parent:Some(generation),token:start},
                });
                generation=next_generation;
                parents=children;
            }
            if !self.same_type(&ConstType::RefMut(Box::new(pointee)),&first_ty){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            predecessors.extend(self.add(live.clone(),operations)?);
            options.extend(parents);
        }
        let (tails,ty,alternatives)=self.finish_value_phi(
            predecessors,dest,first_ty,options,start)?;
        let generation=self.phi_generation(&tails,dest)
            .ok_or("missing ordered effectful return PHI generation")?;
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty,reference:None,loan:None,borrow_parent:None,
            alternatives,phi_generation:Some(generation),mutable,
        });
        Ok(Some(tails))
    }

    fn symbolic_multi_origin_effectful_call(&mut self,start:usize,end:usize,from:&[usize])
        ->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")) || from.len()!=1{return Ok(None);}
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable{i+=1;}
        let Some(K::Ident(dest_name))=self.kind(i)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        let dest=SymbolId(u32::try_from(i+1).map_err(|_|"too many MIR locals")?);
        if self.kind(i+1)!=Some(K::Equal) || self.scopes.last()
            .is_some_and(|scope|scope.contains_key(&dest_name)){return Ok(None);}
        let at=i+2;
        let Some(K::Ident(callee))=self.kind(at)else{return Ok(None)};
        let callee=callee.to_owned();
        if self.kind(at+1)!=Some(K::LParen) ||
            self.close(at+1,end,K::LParen,K::RParen)!=Some(end-1){return Ok(None);}
        let Some(summary)=self.verified_calls.get(&callee).cloned()else{return Ok(None)};
        if summary.returned.is_some() || summary.returned_alternatives.len()<2 {
            return Ok(None);
        }
        let args=self.split_top(at+2,end-1,K::Comma);
        let count=summary.parameters.len();
        if count==0 || count>4 || args.len()!=count ||
            args.iter().any(|arg|arg.end!=arg.start+1){return Ok(None);}
        let mut sources=Vec::<Binding>::with_capacity(count);
        for (arg,formal) in args.iter().zip(&summary.parameters){
            let Some(K::Ident(name))=self.kind(arg.start)else{return Ok(None)};
            let Some(binding)=self.lookup(name)else{return Ok(None)};
            if !self.same_type(&binding.ty,formal){return Ok(None);}
            sources.push(binding);
        }
        //This is the dedicated runtime-selected path only when at least two independent PHI generations
        //participate
        let symbolic=sources.iter().enumerate().filter(|(index,binding)|
            binding.phi_generation.is_some() && !binding.alternatives.is_empty() &&
            matches!(&summary.parameters[*index],ConstType::Ref(_)|ConstType::RefMut(_)))
            .map(|(_,binding)|binding.phi_generation.expect("checked generation"))
            .collect::<HashSet<_>>();
        if symbolic.len()<2 {return Ok(None);}
        let origins=&summary.returned_alternatives;
        let result_ty=origins[0].ty.clone();
        let may=summary.parameter_effects.iter().cloned().collect::<HashSet<_>>();
        let proved=summary.path_cases.iter().flat_map(|case|
            case.effects.iter().cloned()).collect::<HashSet<_>>();
        //This path never speculates by-value effects or uncertain recursion Missing or forged witnesses make
        //the *entire* MIR incomplete
        let valid=origins.len()<=4 && summary.path_cases.len()>0 &&
            summary.path_cases.len()<=128 &&
            matches!(&result_ty,ConstType::RefMut(_)) &&
            summary.parameters.iter().all(|formal|
                matches!(formal,ConstType::Ref(_)|ConstType::RefMut(_))) &&
            origins.iter().all(|origin|origin.parameter<count &&
                origin.fields.len()<=16 && origin.ty==result_ty &&
                matches!(&summary.parameters[origin.parameter],ConstType::RefMut(_)) &&
                sources[origin.parameter].phi_generation.is_some() &&
                !sources[origin.parameter].alternatives.is_empty()) &&
            summary.parameter_effects.iter().all(|effect|
                effect.kind==VerifiedEffectKind::Write && !effect.fields.is_empty() &&
                matches!(summary.parameters.get(effect.parameter),Some(ConstType::RefMut(_)))) &&
            summary.field_writes.iter().all(|write|
                !write.fields.is_empty() && may.contains(&VerifiedParameterEffect{
                    parameter:write.parameter,fields:write.fields.clone(),
                    kind:VerifiedEffectKind::Write})) &&
            summary.path_cases.iter().all(|case|
                case.returned.is_some_and(|index|index<origins.len()) &&
                case.uninitialized.is_empty() &&
                case.effects.iter().all(|effect|may.contains(effect))) &&
            (0..origins.len()).all(|index|summary.path_cases.iter()
                .any(|case|case.returned==Some(index))) && may==proved &&
            sources.iter().enumerate().all(|(index,binding)| {
                if !binding.alternatives.is_empty(){
                    binding.phi_generation.is_some() &&
                    binding.alternatives.len()>=2 && binding.alternatives.len()<=32 &&
                    binding.alternatives.iter().all(|option|
                        option.exclusive==matches!(&summary.parameters[index],ConstType::RefMut(_)) &&
                        self.loans.get(&option.loan)==Some(&option.path))
                }else{binding.reference.is_some() && binding.loan.is_some()}
            });
        if !valid {self.unsupported=true;return Ok(Some(Vec::new()));}
        let total=origins.iter().map(|origin|
            sources[origin.parameter].alternatives.len()).sum::<usize>();
        if total>32 || total==0 {self.unsupported=true;return Ok(Some(Vec::new()));}
        for a in 0..count {for b in a+1..count {
            let exclusive=matches!(&summary.parameters[a],ConstType::RefMut(_)) ||
                matches!(&summary.parameters[b],ConstType::RefMut(_));
            if !exclusive{continue;}
            let paths=|binding:&Binding| -> Vec<Path>{
                if binding.alternatives.is_empty(){
                    binding.reference.iter().map(|(p,_)|p.clone()).collect()
                }else{binding.alternatives.iter().map(|o|o.path.clone()).collect()}
            };
            let pa=paths(&sources[a]);let pb=paths(&sources[b]);
            if pa.iter().any(|x|pb.iter().any(|y|
                x.ancestor_of(y) || y.ancestor_of(x))){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
        }}
        let root=Path::root(dest);
        let live=self.add(from.to_vec(),vec![Statement::StorageLive(Event{
            op:Access::StorageLive,path:root.clone(),loan:None,parent:None,token:start,
        })])?;
        let mut predecessors=Vec::with_capacity(origins.len());
        let mut options=Vec::<RefOption>::with_capacity(total);
        for (index,origin) in origins.iter().enumerate(){
            let mut restricted=summary.clone();
            if !Self::restrict_return_origin(&mut restricted,index){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            restricted.returned=None;
            restricted.returned_alternatives.clear();
            for case in &mut restricted.path_cases{case.returned=None;}
            let Some((mut operations,ConstType::Unit,None))=
                self.verified_user_call(at,end,&callee,restricted)else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let source=&sources[origin.parameter];
            let mut generation=source.phi_generation.expect("checked source PHI");
            let mut parents=source.alternatives.clone();
            let ConstType::RefMut(inner)=&summary.parameters[origin.parameter]else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            let mut pointee=(**inner).clone();
            let stages=origin.fields.len().max(1);
            for depth in 0..stages {
                let step=origin.fields.get(depth).copied();
                if let Some(field)=step {
                    if self.ty_id(&pointee)!=Some(field.aggregate){
                        self.unsupported=true;return Ok(Some(Vec::new()));
                    }
                    let Some(name)=self.schema.type_names.get(field.aggregate.0 as usize)
                        else{self.unsupported=true;return Ok(Some(Vec::new()));};
                    let Some((_,next))=self.schema.types.get(name)
                        .and_then(|fields|fields.get(field.field.0 as usize))
                        else{self.unsupported=true;return Ok(Some(Vec::new()));};
                    pointee=next.clone();
                }
                let last=depth+1==stages;
                let owner=if last{dest}else{
                    self.temp_id().ok_or("too many relational stage locals")?
                };
                if !last {operations.push(Statement::StorageLive(Event{
                    op:Access::StorageLive,path:Path::root(owner),
                    loan:None,parent:None,token:start,
                }));}
                operations.push(self.event(Access::Initialize,Path::root(owner),None,start));
                let stage_generation=self.temp_id().ok_or("too many relational PHI IDs")?;
                let mut children=Vec::with_capacity(parents.len());
                for parent in &parents {
                    let loan=self.temp_id().ok_or("too many relational child loans")?;
                    let path=step.map_or_else(||parent.path.clone(),|field|
                        parent.path.child(field));
                    self.loans.insert(loan,path.clone());
                    children.push(RefOption{loan,path,exclusive:true,parent:Some(parent.loan)});
                }
                operations.push(Statement::LatePhiReborrow{
                    ty:ConstType::RefMut(Box::new(pointee.clone())),
                    source_generation:generation,generation:stage_generation,
                    projection:step,children:children.clone(),
                    event:Event{op:Access::BindPhiMut,path:Path::root(owner),
                        loan:Some(stage_generation),parent:Some(generation),token:start},
                });
                generation=stage_generation;
                parents=children;
            }
            if !self.same_type(&ConstType::RefMut(Box::new(pointee)),&result_ty){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            predecessors.extend(self.add(live.clone(),operations)?);
            options.extend(parents);
        }
        let (tails,ty,alternatives)=self.finish_value_phi(
            predecessors,dest,result_ty,options,start)?;
        let generation=self.phi_generation(&tails,dest)
            .ok_or("missing relational late PHI generation")?;
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty,reference:None,loan:None,borrow_parent:None,
            alternatives,phi_generation:Some(generation),mutable,
        });
        Ok(Some(tails))
    }

    fn staged_effectful_multi_return_call(&mut self,start:usize,end:usize,from:&[usize])
        ->Result<Option<Vec<usize>>,String>{
        if self.kind(start)!=Some(K::Ident("let")) || from.len()!=1 {
            return Ok(None);
        }
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable{i+=1;}
        let Some(K::Ident(dest_name))=self.kind(i)else{return Ok(None)};
        let dest_name=dest_name.to_owned();
        let dest=SymbolId(u32::try_from(i+1).map_err(|_|"too many MIR locals")?);
        if self.kind(i+1)!=Some(K::Equal) || self.scopes.last()
            .is_some_and(|scope|scope.contains_key(&dest_name)){return Ok(None);}
        let at=i+2;
        let Some(K::Ident(name))=self.kind(at)else{return Ok(None)};
        let name=name.to_owned();
        if self.kind(at+1)!=Some(K::LParen) ||
            self.close(at+1,end,K::LParen,K::RParen)!=Some(end-1){return Ok(None);}
        let Some(summary)=self.verified_calls.get(&name).cloned()else{return Ok(None)};
        let origins=&summary.returned_alternatives;
        let count=summary.parameters.len();
        if summary.returned.is_some() || origins.len()<2 || origins.len()>4 ||
            count==0 || count>4 || summary.path_cases.is_empty() ||
            summary.path_cases.len()>128 ||
            summary.parameters.iter().any(|ty|
                !matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_))) ||
            origins.iter().any(|origin|
                origin.parameter>=count || origin.fields.is_empty() ||
                origin.fields.len()>16 ||
                !matches!(&origin.ty,ConstType::RefMut(_)) ||
                !matches!(&summary.parameters[origin.parameter],ConstType::RefMut(_))) ||
            summary.parameter_effects.iter().any(|effect|
                effect.kind!=VerifiedEffectKind::Write || effect.fields.is_empty() ||
                !matches!(summary.parameters.get(effect.parameter),Some(ConstType::RefMut(_)))) ||
            summary.field_writes.iter().any(|write|
                write.fields.is_empty() ||
                !matches!(summary.parameters.get(write.parameter),Some(ConstType::RefMut(_)))) {
            return Ok(None);
        }
        let ty=origins[0].ty.clone();
        if origins.iter().any(|origin|origin.ty!=ty){return Ok(None);}
        //Every case is a concrete return branch. The union of exact case effects must equal the certified MAY
        //summary, including field_writes
        let may=summary.parameter_effects.iter().cloned().collect::<HashSet<_>>();
        let proven=summary.path_cases.iter().flat_map(|case|
            case.effects.iter().cloned()).collect::<HashSet<_>>();
        if proven!=may || summary.path_cases.iter().any(|case|
                case.returned.is_none_or(|index|index>=origins.len()) ||
                !case.uninitialized.is_empty() ||
                case.effects.iter().any(|effect|!may.contains(effect))) ||
            (0..origins.len()).any(|index|!summary.path_cases.iter().any(|case|
                case.returned==Some(index))) ||
            summary.field_writes.iter().any(|write|!may.contains(&VerifiedParameterEffect{
                parameter:write.parameter,fields:write.fields.clone(),
                kind:VerifiedEffectKind::Write,
            })) {return Ok(None);}
        let args=self.split_top(at+2,end-1,K::Comma);
        if args.len()!=count {return Ok(None);}
        for arg in &args {
            if arg.end==arg.start+1 {
                if let Some(K::Ident(source))=self.kind(arg.start){
                    if self.lookup(source).is_some_and(|binding|
                        !binding.alternatives.is_empty()){return Ok(None);}
                }
            }
        }
        let root=Path::root(dest);
        let live=self.add(from.to_vec(),vec![Statement::StorageLive(Event{
            op:Access::StorageLive,path:root.clone(),loan:None,parent:None,token:start,
        })])?;
        let mut predecessors=Vec::with_capacity(origins.len());
        let mut options=Vec::with_capacity(origins.len());
        for (index,origin) in origins.iter().enumerate() {
            let mut individual=summary.clone();
            if !Self::restrict_return_origin(&mut individual,index){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            individual.returned=Some(origin.clone());
            individual.returned_alternatives.clear();
            let Some((mut operations,result,returned))=
                self.verified_user_call(at,end,&name,individual)else{
                self.unsupported=true;return Ok(Some(Vec::new()));
            };
            if result!=ty{self.unsupported=true;return Ok(Some(Vec::new()));}
            let Some((target,true,parent))=returned else{self.unsupported=true;return Ok(Some(Vec::new()));};
            let suffix=&origin.fields;
            if target.fields.len()<suffix.len() || !target.fields.ends_with(suffix){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            let base=Path{owner:target.owner,
                fields:target.fields[..target.fields.len()-suffix.len()].to_vec()};
            let ConstType::RefMut(formal_pointee)=&summary.parameters[origin.parameter]
                else{self.unsupported=true;return Ok(Some(Vec::new()));};
            let mut pointee=(**formal_pointee).clone();
            let mut current=base;
            let mut ancestor=parent;
            let mut last_parent=parent;
            for &field in suffix {
                if self.ty_id(&pointee)!=Some(field.aggregate){self.unsupported=true;return Ok(Some(Vec::new()));}
                let Some(type_name)=self.schema.type_names.get(field.aggregate.0 as usize)
                    else{self.unsupported=true;return Ok(Some(Vec::new()));};
                let Some((_,next))=self.schema.types.get(type_name)
                    .and_then(|fields|fields.get(field.field.0 as usize))
                    else{self.unsupported=true;return Ok(Some(Vec::new()));};
                pointee=next.clone();
                current=current.child(field);
                let child=self.temp_id().ok_or("too many staged return loans")?;
                last_parent=ancestor;
                self.loans.insert(child,current.clone());
                operations.push(Statement::Access(Event{op:Access::BorrowMut,
                    path:current.clone(),loan:Some(child),parent:ancestor,token:start}));
                ancestor=Some(child);
            }
            if current!=target ||
                !self.same_type(&ConstType::RefMut(Box::new(pointee)),&ty){
                self.unsupported=true;return Ok(Some(Vec::new()));
            }
            operations.push(self.event(Access::Initialize,root.clone(),None,start));
            predecessors.extend(self.add(live.clone(),operations)?);
            let loan=ancestor.ok_or("missing staged return loan")?;
            options.push(RefOption{loan,path:target,exclusive:true,
                parent:last_parent});
        }
        let (tails,ty,alternatives)=self.finish_value_phi(
            predecessors,dest,ty,options,start)?;
        let generation=self.phi_generation(&tails,dest)
            .ok_or("missing staged return PHI generation")?;
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(dest_name,Binding{
            id:dest,ty,reference:None,loan:None,borrow_parent:None,
            alternatives,phi_generation:Some(generation),mutable,
        });
        Ok(Some(tails))
    }

    fn result_let(&mut self,start:usize,end:usize,from:Vec<usize>)
        ->Result<Option<Vec<usize>>,String>{
        if !matches!(self.kind(start),Some(K::Ident("let"))){return Ok(None)};
        let mut i=start+1;
        let mutable=self.kind(i)==Some(K::Ident("mut"));
        if mutable{i+=1;}
        let Some(K::Ident(name))=self.kind(i)else{return Ok(None)};
        let local_name=name.to_owned();let binding_at=i;i+=1;
        let annotated=if self.kind(i)==Some(K::Colon){
            i+=1;
            let Some(K::Ident(type_name))=self.kind(i)else{return Ok(None)};
            i+=1;
            Some(match type_name {
                "i64"=>ConstType::I64,"u64"=>ConstType::U64,"bool"=>ConstType::Bool,
                _=>self.schema.type_ids.get(type_name).copied().map(ConstType::Resolved)
                    .unwrap_or_else(||ConstType::Named(type_name.to_owned())),
            })
        }else{None};
        if self.kind(i)!=Some(K::Equal){return Ok(None)};
        i+=1;
        if !matches!(self.kind(i),Some(K::Ident("if"|"match"))){return Ok(None)};
        let dest=SymbolId(u32::try_from(binding_at+1).map_err(|_|"too many MIR locals")?);
        self.scopes.last_mut().ok_or("missing MIR scope")?.insert(local_name.clone(),Binding{
            id:dest,ty:annotated.clone().unwrap_or(ConstType::Unit),reference:None,
            loan:None,borrow_parent:None,alternatives:Vec::new(),phi_generation:None,mutable,
        });
        let live=self.add(from,vec![Statement::StorageLive(Event{
            op:Access::StorageLive,path:Path::root(dest),loan:None,parent:None,token:start})])?;
        let Some((tails,ty,alternatives))=self.result_arm(i..end,live,dest,0)? else{
            self.unsupported=true;return Ok(Some(Vec::new()));
        };
        if annotated.as_ref().is_some_and(|expected|expected!=&ty &&
            !matches!((expected,&ty),(ConstType::Named(a),ConstType::Generic(b)) if a==b)) {
            self.unsupported=true;return Ok(Some(Vec::new()));
        }
        let phi_generation=if alternatives.is_empty(){None}else{
            self.phi_generation(&tails,dest)
        };
        if !alternatives.is_empty() && phi_generation.is_none(){
            return Err("missing result PHI generation".into());
        }
        if let Some(binding)=self.scopes.last_mut().and_then(|scope|scope.get_mut(&local_name)){
            binding.ty=ty;
            binding.reference=None;binding.loan=None;binding.borrow_parent=None;
            binding.alternatives=alternatives;
            binding.phi_generation=phi_generation;
        }
        Ok(Some(tails))
    }
    fn parse_seq(&mut self,range:Range<usize>,mut tails:Vec<usize>,loop_target:Option<(usize,usize,usize)>,depth:usize)->Result<Vec<usize>,String>{
        if depth>64{return Err("typed MIR nesting limit exceeded".into());}
        self.scopes.push(HashMap::new());
        let mut i=range.start;
        while i<range.end && !self.unsupported {
            if self.kind(i)==Some(K::Ident("if")){
                if let Some((joined,next))=self.parse_mut_rebind_else_if(i,range.end,&tails)? {
                    tails=joined;i=next;continue;
                }
                if let Some((joined,next))=self.parse_mut_rebind_if(i,range.end,&tails)? {
                    tails=joined;i=next;continue;
                }
                let (joined,next)=self.parse_if(i,range.end,tails,loop_target,depth)?;
                tails=joined;i=next;continue;
            }
            if matches!(self.kind(i),Some(K::Ident("while"|"for"|"loop"))){
                let Some(brace)=(i+1..range.end).find(|&p|self.kind(p)==Some(K::LBrace))else{self.unsupported=true;break;};
                let Some(last)=self.close(brace,range.end,K::LBrace,K::RBrace)else{self.unsupported=true;break;};
                let ops=if self.kind(i)==Some(K::Ident("while")){
                    let Some((ops,ty,_))=self.expr(i+1,brace)else{self.unsupported=true;break;};
                    if ty!=ConstType::Bool {self.unsupported=true;break;}
                    ops
                }else if self.kind(i)==Some(K::Ident("for")) {
                    if !matches!(self.kind(i+1),Some(K::Ident(_))) || self.kind(i+2)!=Some(K::Ident("in")){
                        self.unsupported=true;break;
                    }
                    let Some(separator)=(i+3..brace).find(|&pos|
                        matches!(self.kind(pos),Some(K::DotDot|K::DotDotEq)))else{self.unsupported=true;break;};
                    let Some((mut begin,_,_))=self.expr(i+3,separator)else{self.unsupported=true;break;};
                    let Some((end,_,_))=self.expr(separator+1,brace)else{self.unsupported=true;break;};
                    begin.extend(end);begin
                }else{Vec::new()};
                let incoming = std::mem::take(&mut tails);
                let head = self.add(incoming, ops)?[0];
                let loop_exit = self.block()?;
                self.link(&[head], loop_exit);
                let body = self.block()?;
                self.link(&[head], body);
                let is_for=self.kind(i)==Some(K::Ident("for"));
                let mut body_entry=vec![body];
                if is_for {
                    let Some(K::Ident(name))=self.kind(i+1)else{
                        self.unsupported=true;break;
                    };
                    let symbol=SymbolId(u32::try_from(i+2).map_err(|_|"too many MIR symbols")?);
                    self.scopes.push(HashMap::from([(name.to_owned(),Binding{
                        id:symbol,ty:ConstType::I64,reference:None,loan:None,borrow_parent:None,
                        alternatives:Vec::new(),phi_generation:None,mutable:false})]));
                    let path=Path::root(symbol);
                    let initialized=self.event(Access::Initialize,path,None,i+1);
                    body_entry=self.add(body_entry,vec![
                        Statement::StorageLive(Event{op:Access::StorageLive,
                            path:Path::root(symbol),loan:None,parent:None,token:i+1}),
                        initialized,
                    ])?;
                }
                let loop_depth=self.scopes.len()-usize::from(is_for);
                let finished=self.parse_seq(brace+1..last,body_entry,
                    Some((head,loop_exit,loop_depth)),depth+1)?;
                let finished=if is_for {
                    let cleanup=self.leave_scopes(loop_depth,last);
                    self.scopes.pop();
                    if cleanup.is_empty(){finished}else{self.add(finished,cleanup)?}
                }else{finished};
                self.link(&finished,head);
                tails = vec![loop_exit];
                i=last+1;continue;
            }
            if self.kind(i)==Some(K::Ident("match")){
                if let Some((joined,next))=self.parse_enum_mut_rebind_match(i,range.end,&tails)? {
                    tails=joined;i=next;continue;
                }
                if let Some((joined,next))=self.parse_mut_rebind_match(i,range.end,&tails)? {
                    tails=joined;i=next;continue;
                }
                let Some(brace)=(i+1..range.end).find(|&p|self.kind(p)==Some(K::LBrace))else{self.unsupported=true;break;};
                let Some(last)=self.close(brace,range.end,K::LBrace,K::RBrace)else{self.unsupported=true;break;};
                let borrowed_subject=if self.kind(i+1)==Some(K::Amp) {
                    let exclusive=self.kind(i+2)==Some(K::Ident("mut"));
                    let index=i+2+usize::from(exclusive);
                    if index+1!=brace {self.unsupported=true;break;}
                    let Some(K::Ident(name))=self.kind(index)else{self.unsupported=true;break;};
                    let Some(binding)=self.lookup(name)else{self.unsupported=true;break;};
                    if exclusive && !binding.mutable {self.unsupported=true;break;}
                    if binding.reference.is_some() || !binding.alternatives.is_empty(){
                        self.unsupported=true;break;
                    }
                    Some((binding.id,binding.ty,exclusive))
                }else{None};
                let mut has_ref_pattern=false;
                let mut pattern_at=brace+1;
                while pattern_at<last {
                    let Some((pattern,after))=crate::typed_patterns::parse(
                        self.tokens,pattern_at,last)else{break;};
                    let mut names=Vec::new();
                    crate::typed_patterns::collect_bindings(&pattern,&mut names);
                    has_ref_pattern |= names.iter().any(|(_,_,is_ref,_)|*is_ref);
                    let Some(body_start)=(after..last).find(|&at|
                        self.kind(at)==Some(K::FatArrow)).map(|at|at+1)else{break;};
                    let Some(body_end)=self.close(body_start,last,K::LBrace,K::RBrace)else{break;};
                    pattern_at=body_end+1;
                    if self.kind(pattern_at)==Some(K::Comma){pattern_at+=1;}
                }
                let partial_owner=if borrowed_subject.is_none() && i+2==brace {
                    if let Some(K::Ident(name))=self.kind(i+1) {
                        self.lookup(name).and_then(|binding|{
                            let id=self.ty_id(&binding.ty)?;
                            let type_name=self.schema.type_names.get(id.0 as usize)?;
                            let variants=self.schema.enum_payloads.get(type_name)?;
                            let multi_owned=variants.iter().any(|fields|
                                fields.len()>=2 && fields.iter().any(|ty|!self.is_copy(ty)));
                            ((multi_owned || has_ref_pattern) && binding.reference.is_none() &&
                                binding.alternatives.is_empty()).then_some((binding.id,binding.ty))
                        })
                    }else{None}
                }else{None};
                let (ops,subject_ty)=if let Some((id,ty,_))=&borrowed_subject {
                    (vec![self.event(Access::Read,Path::root(*id),None,i+1)],ty.clone())
                }else if let Some((id,ty))=&partial_owner {
                    //Reading the discriminant does not read a moved payload This synthetic field cannot collide with a
                    //variant payload projection (their low 4 bits are bounded)
                    let type_id=self.ty_id(ty).ok_or("unresolved enum discriminant")?;
                    let tag=Path::root(*id).child(FieldKey{
                        aggregate:type_id,field:FieldId(u32::MAX)});
                    (vec![self.event(Access::Read,tag,None,i+1)],ty.clone())
                }else{
                    let Some((ops,ty,_))=self.expr(i+1,brace)else{self.unsupported=true;break;};
                    (ops,ty)
                };
                let enum_variants=self.ty_id(&subject_ty)
                    .and_then(|id|self.schema.type_names.get(id.0 as usize))
                    .and_then(|name|self.schema.enums.get(name)
                        .map(|variants|(name.clone(),variants.clone())));
                let branch=self.add(tails,ops)?[0];
                let has_owned_payload=enum_variants.as_ref().is_some_and(|(name,_)|
                    self.schema.enum_payloads.get(name).is_some_and(|variants|
                        variants.iter().flatten().any(|ty|!self.is_copy(ty))));
                let enum_temp=if has_owned_payload && borrowed_subject.is_none() &&
                    partial_owner.is_none() {
                    let id=self.temp_id().ok_or("too many owned enum match temporaries")?;
                    let root=Path::root(id);
                    self.blocks[branch].statements.push(Statement::StorageLive(Event{
                        op:Access::StorageLive,path:root.clone(),loan:None,parent:None,token:i,
                    }));
                    let init=self.event(Access::Initialize,root,None,i);
                    self.blocks[branch].statements.push(init);
                    Some(id)
                }else{None};
                let mut joined=Vec::new();let mut arm=brace+1;
                let (mut bool_seen,mut enum_seen,mut wildcard)=(0u8,0u128,false);
                while arm<last {
                    if wildcard{self.unsupported=true;break;}
                    let mut arm_bool=0u8;
                    let mut arm_enum=0u128;
                    let mut arm_wildcard=false;
                    let mut pattern_bindings=Vec::<(String,ConstType,SymbolId)>::new();
                    let mut pattern_references=HashMap::<SymbolId,RefOption>::new();
                    let mut payload_accesses=Vec::<Statement>::new();
                    let arrow=match self.kind(arm) {
                        Some(K::Number(_)) if matches!(&subject_ty,ConstType::I64|ConstType::U64)=>arm+1,
                        _=>{
                            let Some((pattern,after))=crate::typed_patterns::parse(self.tokens,arm,last)
                                else{self.unsupported=true;break;};
                            match &pattern {
                                crate::typed_patterns::Pattern::Wildcard=>{arm_wildcard=true;},
                                crate::typed_patterns::Pattern::Boolean(value) if subject_ty==ConstType::Bool=>{
                                    arm_bool=if *value{1}else{2};
                                },
                                crate::typed_patterns::Pattern::Enum{..} if enum_variants.is_some()=>{
                                    let checked={
                                        let schema=crate::typed_patterns::Schema{
                                            enums:self.schema.enums,payloads:self.schema.enum_payloads,
                                            structs:self.schema.types,type_ids:self.schema.type_ids,
                                        };
                                        crate::typed_patterns::check(&pattern,&subject_ty,
                                            borrowed_subject.as_ref().map(|(_,_,mutable)|*mutable),&schema)
                                    };
                                    let Ok(checked)=checked else{self.unsupported=true;break;};
                                    arm_enum=if checked.covers_variant {
                                        checked.variant.map_or(0u128,|v|1u128<<v)
                                    }else{0};
                                    for binding in checked.bindings {
                                        let id=SymbolId(u32::try_from(binding.token+1)
                                            .map_err(|_|"too many nested enum pattern bindings")?);
                                        let by_ref=binding.by_ref;
                                        let ty=if by_ref==Some(true){ConstType::RefMut(Box::new(binding.ty.clone()))}
                                            else if by_ref==Some(false){ConstType::Ref(Box::new(binding.ty.clone()))}
                                            else{binding.ty.clone()};
                                        pattern_bindings.push((binding.name.to_owned(),ty,id));
                                        if let Some((owner,_,_))=&borrowed_subject {
                                            let mut place=Path::root(*owner);
                                            for key in &binding.path{place=place.child(*key);}
                                            let loan=self.temp_id().ok_or("too many enum payload loans")?;
                                            payload_accesses.push(Statement::Access(Event{
                                                op:if by_ref==Some(true){Access::BorrowMut}else{Access::BorrowShared},
                                                path:place.clone(),loan:Some(loan),parent:None,token:binding.token,
                                            }));
                                            self.loans.insert(loan,place.clone());
                                            pattern_references.insert(id,RefOption{
                                                loan,path:place,exclusive:by_ref==Some(true),parent:None,
                                            });
                                        }else if let Some((owner,_))=&partial_owner {
                                            let mut place=Path::root(*owner);
                                            for key in &binding.path{place=place.child(*key);}
                                            if let Some(exclusive)=by_ref {
                                                //Borrowed and moved siblings share one original owner, with disjoint typed paths Unlike a moved
                                                //temporary, this loan must survive into the arm and end at last use
                                                if exclusive && !self.scopes.iter().rev().flat_map(|scope|scope.values())
                                                    .any(|binding|binding.id==*owner && binding.mutable) {
                                                    self.failure=Some("ref mut pattern requires a mutable enum owner".into());
                                                    self.unsupported=true;break;
                                                }
                                                let loan=self.temp_id().ok_or("too many enum payload loans")?;
                                                payload_accesses.push(Statement::Access(Event{
                                                    op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
                                                    path:place.clone(),loan:Some(loan),parent:None,token:binding.token,
                                                }));
                                                self.loans.insert(loan,place.clone());
                                                pattern_references.insert(id,RefOption{
                                                    loan,path:place,exclusive,parent:None,
                                                });
                                            }else{
                                                payload_accesses.push(self.event(
                                                    if self.is_copy(&binding.ty){Access::Read}else{Access::Move},
                                                    place,None,binding.token));
                                            }
                                        }else if let Some(temp)=enum_temp {
                                            //Ref binders of a temporary have no stable owner/loan provenance in this preview: never certify them
                                            if by_ref.is_some(){self.unsupported=true;break;}
                                            let mut place=Path::root(temp);
                                            for key in &binding.path{place=place.child(*key);}
                                            payload_accesses.push(self.event(
                                                if self.is_copy(&binding.ty){Access::Read}else{Access::Move},
                                                place,None,binding.token));
                                        }else if by_ref.is_some() || !self.is_copy(&binding.ty) {
                                            self.unsupported=true;break;
                                        }
                                    }
                                    if self.unsupported{break;}
                                },
                                _=>{self.unsupported=true;break;},
                            }
                            after
                        },
                    };
                    //A bounded guard may only read one bool variable or literal. Complex/side-effecting guards must not
                    //pass MIR certification by silently skipping their effects
                    let guarded=self.kind(arrow)==Some(K::Ident("if"));
                    let (arrow,guard_ops)=if guarded {
                        if !pattern_bindings.is_empty() || !payload_accesses.is_empty() {
                            self.unsupported=true;break;
                        }
                        let Some((ops,ConstType::Bool,None))=self.expr(arrow+1,arrow+2)else{
                            self.unsupported=true;break;
                        };
                        if !matches!(self.kind(arrow+2),Some(K::FatArrow)) ||
                            !matches!(self.kind(arrow+1),Some(K::Ident(_))) {
                            self.unsupported=true;break;
                        }
                        (arrow+2,ops)
                    }else{(arrow,Vec::new())};
                    if !guarded {
                        if arm_wildcard{wildcard=true;}
                        if bool_seen&arm_bool!=0 || enum_seen&arm_enum!=0{
                            self.unsupported=true;break;
                        }
                        bool_seen|=arm_bool;enum_seen|=arm_enum;
                    }
                    if self.kind(arrow)!=Some(K::FatArrow) ||
                        self.kind(arrow+1)!=Some(K::LBrace){self.unsupported=true;break;}
                    let Some(end)=self.close(arrow+1,last,K::LBrace,K::RBrace)else{
                        self.unsupported=true;break;
                    };
                    let entry=self.block()?;self.link(&[branch],entry);
                    let arm_start=if guard_ops.is_empty(){vec![entry]}
                        else{self.add(vec![entry],guard_ops)?};
                    let mut binds=HashMap::new();
                    let mut init_events=payload_accesses;
                    for (name,ty,id) in pattern_bindings {
                        let path=Path::root(id);
                        init_events.push(Statement::StorageLive(Event{op:Access::StorageLive,
                            path:path.clone(),loan:None,parent:None,token:arm}));
                        init_events.push(self.event(Access::Initialize,path,None,arm));
                        let source=pattern_references.get(&id);
                        binds.insert(name,Binding{id,ty,
                            reference:source.map(|opt|(opt.path.clone(),opt.exclusive)),
                            loan:source.map(|opt|opt.loan),borrow_parent:None,
                            alternatives:Vec::new(),phi_generation:None,mutable:false});
                    }
                    let arm_entry=if init_events.is_empty(){arm_start}
                        else{self.add(arm_start,init_events)?};
                    self.scopes.push(binds);
                    let result=self.parse_seq(arrow+2..end,arm_entry,loop_target,depth+1);
                    self.scopes.pop();
                    let outgoing=result?;
                    if !outgoing.is_empty() && !pattern_references.is_empty() {
                        let end_loans=pattern_references.values().map(|reference|
                            Statement::Access(Event{op:Access::EndLoan,
                                path:reference.path.clone(),loan:Some(reference.loan),
                                parent:None,token:end})).collect();
                        joined.extend(self.add(outgoing,end_loans)?);
                    }else if let Some(temp)=enum_temp {
                        if !outgoing.is_empty(){
                            let root=Path::root(temp);
                            joined.extend(self.add(outgoing,vec![Statement::StorageDead(Event{
                                op:Access::StorageDead,path:root,loan:None,parent:None,token:end,
                            })])?);
                        }
                    }else{joined.extend(outgoing);}
                    arm=end+1;if self.kind(arm)==Some(K::Comma){arm+=1;}
                }
                let exhaustive=if let Some((_,variants))=enum_variants.as_ref(){
                    wildcard || enum_seen.count_ones() as usize==variants.len()
                }else if subject_ty==ConstType::Bool {
                    wildcard || bool_seen==3
                }else{wildcard};
                if !exhaustive || joined.is_empty(){self.unsupported=true;}
                tails=joined;i=last+1;continue;
            }
            if matches!(self.kind(i),Some(K::Ident("break"|"continue"))){
                let Some((head,exit,scope_at_loop))=loop_target else{self.unsupported=true;break;};
                if self.kind(i+1)!=Some(K::Semi){self.unsupported=true;break;}
                let cleanup=self.leave_scopes(scope_at_loop,i);
                let from=if cleanup.is_empty(){tails}else{self.add(tails,cleanup)?};
                self.link(&from,if self.kind(i)==Some(K::Ident("break")){exit}else{head});
                tails=Vec::new();i+=2;continue;
            }
            if self.kind(i)==Some(K::Ident("return")){
                let Some(end)=(i+1..range.end).find(|&p|self.kind(p)==Some(K::Semi))else{self.unsupported=true;break;};
                if end>i+1 {
                    let incoming=std::mem::take(&mut tails);
                    if let Some(joined)=self.projected_return_call(i+1,end,incoming.clone())? {
                        let cleanup=self.leave_scopes(1,i);
                        let returned=if cleanup.is_empty(){joined}
                            else{self.add(joined,cleanup)?};
                        for node in returned {self.blocks[node].terminator=Terminator::Return;}
                        tails=Vec::new();i=end+1;continue;
                    }
                    tails=incoming;
                }
                let ops=if end>i+1 {self.expr(i+1,end).map(|r|r.0)}else{Some(Vec::new())};
                let Some(ops)=ops else{self.unsupported=true;break;};
                let mut ops=ops;
                ops.extend(self.leave_scopes(1,i));
                for id in self.add(tails,ops)?{self.blocks[id].terminator=Terminator::Return;}
                tails=Vec::new();i=end+1;continue;
            }
            if self.kind(i)==Some(K::LBrace){
                let Some(end)=self.close(i,range.end,K::LBrace,K::RBrace)else{self.unsupported=true;break;};
                tails=self.parse_seq(i+1..end,tails,loop_target,depth+1)?;i=end+1;continue;
            }
            let mut end=i;let(mut par,mut brace)=(0usize,0usize);
            while end<range.end {match self.kind(end){
                Some(K::LParen)=>par+=1,Some(K::RParen)=>par=par.saturating_sub(1),
                Some(K::LBrace)=>brace+=1,Some(K::RBrace)=>brace=brace.saturating_sub(1),
                Some(K::Semi) if par==0&&brace==0=>break,_=>(),}end+=1;}
            if end>=range.end {
                let incoming=std::mem::take(&mut tails);
                if let Some(joined)=self.projected_return_call(i,range.end,incoming.clone())? {
                    tails=joined;i=range.end;continue;
                }
                tails=incoming;
                let Some((ops,_,_))=self.expr(i,range.end)else{
                    self.unsupported=true;break;
                };
                tails=self.add(tails,ops)?;
                i=range.end;
                continue;
            }
            if self.kind(i)==Some(K::Ident("let")) &&
                (i..end).any(|at|matches!(self.kind(at),Some(K::Ident("if"|"match")))) {
                let incoming=std::mem::take(&mut tails);
                if let Some(value_tails)=self.result_let(i,end,incoming)? {
                    tails=value_tails;i=end+1;continue;
                }
                self.unsupported=true;break;
            }
            if self.kind(i)==Some(K::Ident("let")) {
                let incoming=std::mem::take(&mut tails);
                if let Some(call_tails)=self.immediate_phi_multi_return_call(i,end,&incoming)? {
                    tails=call_tails;i=end+1;continue;
                }
                if let Some(call_tails)=self.immediate_nested_phi_forward_call(i,end,&incoming)? {
                    tails=call_tails;i=end+1;continue;
                }
                if let Some(call_tails)=self.immediate_phi_forward_call(i,end,&incoming)? {
                    tails=call_tails;i=end+1;continue;
                }
                if let Some(call_tails)=self.ordered_effectful_phi_return_call(i,end,&incoming)? {
                    tails=call_tails;i=end+1;continue;
                }
                if let Some(call_tails)=self.symbolic_multi_origin_effectful_call(i,end,&incoming)? {
                    tails=call_tails;i=end+1;continue;
                }
                if let Some(call_tails)=self.staged_effectful_multi_return_call(i,end,&incoming)? {
                    tails=call_tails;i=end+1;continue;
                }
                if let Some(call_tails)=self.projected_call_let(i,end,incoming.clone())? {
                    tails=call_tails;i=end+1;continue;
                }
                tails=incoming;
            }
            if let Some(bound)=self.late_independent_mut_phi_bind(i,end,&tails)? {
                tails=bound;i=end+1;continue;
            }
            if let Some(unchanged)=self.immediate_phi_mut_reborrow(i,end,&tails)? {
                tails=unchanged;i=end+1;continue;
            }
            let Some(ops)=self.analyze_stmt(i,end)else{self.unsupported=true;break;};
            tails=self.add(tails,ops)?;i=end+1;
        }
        let events=if !tails.is_empty() && !self.unsupported{
            self.leave_scopes(self.scopes.len()-1,range.end)
        }else{Vec::new()};
        self.scopes.pop();
        if !events.is_empty(){tails=self.add(tails,events)?;}
        Ok(tails)
    }
    fn lower(mut self,range:Range<usize>)->Result<Option<FunctionMir>,String>{
        let entry=self.block()?;
        let tails=self.parse_seq(range,vec![entry],None,0)?;
        if let Some(reason)=self.failure.take(){return Err(reason);}
        if self.unsupported{return Ok(None);}
        let exit=self.block()?;self.link(&tails,exit);
        self.blocks[exit].terminator=Terminator::Return;
        Ok(Some(FunctionMir{blocks:self.blocks,entry,loans:self.loans}))
    }
}
impl FunctionMir {
    //An interprocedural effect may use a PHI capability only if its definition dominates that call
    fn call_can_bypass_phi_definition(&self,definition:usize,call:usize)->bool {
        if self.entry==definition {return false;}
        let mut seen=HashSet::new();
        let mut pending=VecDeque::from([self.entry]);
        while let Some(node)=pending.pop_front() {
            if node==definition || !seen.insert(node){continue;}
            if node==call{return true;}
            if let Some(block)=self.blocks.get(node) {
                if let Terminator::Goto(next)=&block.terminator {
                    pending.extend(next.iter().copied());
                }
            }
        }
        false
    }

    //A call-boundary loan witness includes its exact parent edge
    fn update_staged_call_loans(
        staged:&mut HashMap<SymbolId,(Path,Option<SymbolId>,bool)>,
        event:&Event,allow_new_borrows:bool) {
        if matches!(event.op,Access::Move|Access::Drop|
            Access::StorageDead|Access::StorageLive) {
            staged.retain(|_,(base,_,_)|!(event.path.ancestor_of(base) ||
                base.ancestor_of(&event.path)));
        }
        match event.op {
            Access::BorrowMut|Access::BorrowShared if allow_new_borrows=>{
                if let Some(id)=event.loan {
                    staged.insert(id,(event.path.clone(),event.parent,
                        event.op==Access::BorrowMut));
                }
            }
            Access::BorrowShared|Access::EndLoan=>{
                if let Some(id)=event.loan {staged.remove(&id);}
            }
            _=>(),
        }
    }

    fn write_has_ordered_loan(events:&[Event],write_at:usize,
        staged:&HashMap<SymbolId,(Path,Option<SymbolId>,bool)>)->bool {
        let write=&events[write_at];
        if write.op!=Access::Write{return false;}
        let Some(id)=write.loan else{return false;};
        let mut active=staged.clone();
        for event in &events[..write_at] {
            Self::update_staged_call_loans(&mut active,event,true);
        }
        let Some((base,_,exclusive))=active.get(&id)else{return false;};
        if !*exclusive || !base.ancestor_of(&write.path){return false;}
        //Other independently active loans must not overlap the effect's actual MovePath; an unrelated owner or
        //a sibling field does not revoke this witness
        if active.len()==1 {return true;}
        for (&other,(other_path,_,_)) in &active {
            if other==id {continue;}
            let mut cursor=other;
            let mut visited=HashSet::new();
            while let Some((_,Some(parent),_))=active.get(&cursor) {
                if !visited.insert(cursor){return false;}
                if *parent==id{return false;}
                cursor=*parent;
            }
            let mut cursor=id;
            visited.clear();
            let mut is_ancestor=false;
            while let Some((_,Some(parent),_))=active.get(&cursor) {
                if !visited.insert(cursor){return false;}
                if *parent==other {is_ancestor=true;break;}
                cursor=*parent;
            }
            if is_ancestor {continue;}
            if other_path.ancestor_of(&write.path) ||
                write.path.ancestor_of(other_path) {return false;}
        }
        true
    }

    //This is independent of the dataflow checker: a forged/mismatched case cannot merely *claim* to write a
    //field for which the call has no exclusive loan
    fn validate_interprocedural_alias_proofs(&self)->Result<(),String>{
        let mut phi_witnesses=HashMap::<(Path,SymbolId),Vec<(usize,usize,Vec<RefOption>)>>::new();
        for (node,block) in self.blocks.iter().enumerate() {
            for (position,statement) in block.statements.iter().enumerate() {
                match statement {
                    Statement::ValuePhi{ty:ConstType::RefMut(_),check,
                        generation:Some(id),alternatives,..} => {
                        phi_witnesses.entry((check.path.clone(),*id)).or_default()
                            .push((node,position,alternatives.clone()));
                    }
                    Statement::LatePhiReborrow{ty:ConstType::RefMut(_),source_generation,
                        generation,children,event,..} if event.op==Access::BindPhiMut &&
                            event.loan==Some(*generation) &&
                            event.parent==Some(*source_generation) => {
                        phi_witnesses.entry((event.path.clone(),*generation))
                            .or_default().push((node,position,children.clone()));
                    }
                    _=>(),
                }
            }
        }
        let mut dominance_cache=HashMap::<(usize,usize),bool>::new();
        for (call_node,block) in self.blocks.iter().enumerate() {
            let mut staged_mut=HashMap::<SymbolId,(Path,Option<SymbolId>,bool)>::new();
            for (call_position,statement) in block.statements.iter().enumerate() {
                if let Statement::Access(event)=statement {
                    Self::update_staged_call_loans(&mut staged_mut,event,true);
                    continue;
                }
                let Statement::Call{events,effects,path_cases,..}=statement else{
                    for event in statement.events() {
                        Self::update_staged_call_loans(&mut staged_mut,event,false);
                    }
                    continue;
                };
                if !path_cases.is_empty() {
                    //Every possible effect must be witnessed in a case, and no case may invent an effect not in the MAY set
                    if effects.iter().any(|effect|!path_cases.iter().any(|case|
                        case.effects.contains(effect))) ||
                        path_cases.iter().any(|case|case.effects.iter().any(|effect|
                            !effects.contains(effect))) {
                        return Err("incomplete interprocedural alias case effects".into());
                    }
                    for case in path_cases {
                        //An uninitialized postcondition has to follow an actual move or drop of its ancestor in this case; it
                        //cannot appear merely from an arbitrary path ID
                        for moved in &case.uninitialized {
                            if !case.effects.iter().any(|effect|
                                matches!(effect.kind,VerifiedEffectKind::Move|VerifiedEffectKind::Drop) &&
                                effect.path.ancestor_of(moved)) {
                                return Err("unproven interprocedural partial move".into());
                            }
                        }
                    }
                }
                for effect in effects {
                    let owned=events.iter().any(|event|
                        matches!(event.op,Access::Move|Access::Read) &&
                        event.loan.is_none() && event.path.ancestor_of(&effect.path));
                    if owned {continue;}
                    //All effects through a borrowed actual MUST be writes authorized by a typed exclusive temporary loan
                    if effect.kind!=VerifiedEffectKind::Write {return Err(
                        "interprocedural move/drop lacks an owned argument".into());}
                    let authorized=events.iter().enumerate().any(|(at,write)|
                        write.op==Access::Write && write.path==effect.path &&
                        Self::write_has_ordered_loan(events,at,&staged_mut));
                    let disjunctive=if effect.kind==VerifiedEffectKind::Write &&
                        effect.path.fields.is_empty() && !effect.alternatives.is_empty() {
                        events.iter().filter(|e|e.op==Access::Write &&
                            e.path==effect.path).filter_map(|e|e.loan).any(|generation|{
                            phi_witnesses.get(&(effect.path.clone(),generation))
                                .is_some_and(|candidates|candidates.iter().any(
                                    |(def_node,def_position,alternatives)| {
                                if alternatives.len()!=effect.alternatives.len() {
                                    return false;
                                }
                                //In the same block, the PHI must precede this Call. On other blocks it must dominate *every* way of
                                //reaching the call
                                if *def_node==call_node {
                                    if *def_position>=call_position{return false;}
                                }else{
                                    let bypass=*dominance_cache.entry(
                                        (*def_node,call_node)).or_insert_with(||
                                        self.call_can_bypass_phi_definition(*def_node,call_node));
                                    if bypass{return false;}
                                }
                                let mut suffix:Option<Vec<FieldKey>>=None;
                                for (candidate,target) in alternatives.iter()
                                    .zip(&effect.alternatives) {
                                    if !candidate.path.ancestor_of(target){return false;}
                                    let fields=target.fields[candidate.path.fields.len()..].to_vec();
                                    if suffix.as_ref().is_some_and(|s|s!=&fields){
                                        return false;
                                    }
                                    suffix=Some(fields);
                                }
                                true
                            }))
                        })
                    }else{false};
                    //No disjunctive metadata may hide behind an ordinary owned or single-loan call proof
                    if !effect.alternatives.is_empty() && !disjunctive {
                        return Err("invalid disjunctive interprocedural alias proof".into());
                    }
                    if !authorized && !disjunctive {return Err(
                        "interprocedural field write lacks exclusive alias proof".into());}
                }
                //A Call can end a loan started by an earlier argument. It must not remain a proof witness for any later
                //call
                for event in events {
                    Self::update_staged_call_loans(&mut staged_mut,event,false);
                }
            }
        }
        Ok(())
    }
    pub fn verify(&self)->Result<Vec<cfg_borrow::Conflict>,String>{
        self.validate_interprocedural_alias_proofs()?;
        let mut phi_groups=HashMap::<SymbolId,(SymbolId,Vec<SymbolId>)>::new();
        for (node,block) in self.blocks.iter().enumerate() {
            for statement in &block.statements {
                if let Statement::ValuePhi{ty,predecessors,check,provenance,alternatives,generation}=statement {
                    let mut actual=predecessors.clone();actual.sort_unstable();
                    if actual.is_empty() || actual.windows(2).any(|w|w[0]==w[1]) ||
                        matches!(ty,ConstType::Unit) ||
                        check.op!=Access::Read || !check.path.fields.is_empty() ||
                        check.loan.is_some() {
                        return Err("invalid typed MIR result PHI".into());
                    }
                    let mut expected=self.blocks.iter().enumerate().filter_map(|(i,source)|
                        match &source.terminator {
                            Terminator::Goto(next) if next.contains(&node)=>Some(i),
                            _=>None,
                        }).collect::<Vec<_>>();
                    expected.sort_unstable();
                    if actual!=expected {return Err("incomplete typed MIR result PHI predecessors".into());}
                    let reference=matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_));
                    if reference==alternatives.is_empty() || alternatives.len()>32 ||
                        reference!=generation.is_some() {
                        return Err("invalid typed MIR reference PHI provenance".into());
                    }
                    if !reference {
                        if provenance.is_some(){return Err("non-reference PHI has provenance".into());}
                        continue;
                    }
                    let exclusive=matches!(ty,ConstType::RefMut(_));
                    let unique=alternatives.iter().map(|option|option.loan)
                        .collect::<HashSet<_>>();
                    if unique.len()!=alternatives.len() || alternatives.iter().any(|option|
                        option.exclusive!=exclusive ||
                        self.loans.get(&option.loan)!=Some(&option.path)) {
                        return Err("invalid reference PHI candidate loan".into());
                    }
                    let expected_uniform=alternatives.first().and_then(|first|{
                        alternatives.iter().all(|option|option.path==first.path &&
                            option.parent==first.parent && option.exclusive==first.exclusive)
                            .then(||(first.path.clone(),first.exclusive,first.parent))
                    });
                    if &expected_uniform!=provenance {
                        return Err("reference PHI provenance summary does not match alternatives".into());
                    }
                    let mut observed=HashSet::new();
                    for &pred in predecessors {
                        let mut providers=0usize;
                        for source in &self.blocks[pred].statements {
                            match source {
                                Statement::Access(ev) if matches!(ev.op,Access::BorrowShared|Access::BorrowMut) => {
                                    if let Some(option)=alternatives.iter().find(|option|
                                        Some(option.loan)==ev.loan && option.path==ev.path &&
                                        option.parent==ev.parent && option.exclusive==(ev.op==Access::BorrowMut)) {
                                        observed.insert(option.loan);providers+=1;
                                    }
                                }
                                Statement::LatePhiReborrow{ty:provided,children,event,..}
                                    if event.path==check.path && provided==ty &&
                                        !children.is_empty() &&
                                        children.iter().all(|child|alternatives.contains(child)) => {
                                    for child in children{observed.insert(child.loan);}
                                    providers+=1;
                                }
                                Statement::ValuePhi{check:inner,alternatives:inner_options,..}
                                    if inner.path==check.path && !inner_options.is_empty() => {
                                    if inner_options.iter().all(|candidate|alternatives.contains(candidate)) {
                                        for candidate in inner_options{observed.insert(candidate.loan);}
                                        providers+=1;
                                    }
                                }
                                _=>(),
                            }
                        }
                        if providers!=1{return Err("unproven typed MIR reference PHI predecessor".into());}
                    }
                    if observed!=unique {
                        return Err("reference PHI contains missing or phantom alternatives".into());
                    }
                    let generation=generation.ok_or("missing PHI generation ID")?;
                    if generation==check.path.owner || alternatives.iter().any(|o|o.loan==generation){
                        return Err("PHI generation aliases another identity".into());
                    }
                    if phi_groups.insert(generation,(check.path.owner,
                            alternatives.iter().map(|o|o.loan).collect())).is_some(){
                        return Err("PHI generation reused for different values".into());
                    }
                }
            }
        }
        let mut late_reborrows=Vec::<(SymbolId,SymbolId,Vec<(SymbolId,SymbolId,Path)>)>::new();
        //The output of a staged projection is the input type of the next reborrow; never trust a
        //caller-supplied type on its own
        let mut phi_types=HashMap::<SymbolId,ConstType>::new();
        for block in &self.blocks {for statement in &block.statements {
            if let Statement::ValuePhi{ty,generation:Some(id),..}=statement {
                if phi_types.insert(*id,ty.clone()).is_some(){
                    return Err("PHI generation has conflicting reference types".into());
                }
            }
        }}
        for block in &self.blocks {
            for statement in &block.statements {
                let Statement::LatePhiReborrow{ty,source_generation,generation,
                    children,event,projection}=statement else{continue};
                let Some((source_owner,parents))=phi_groups.get(source_generation)else{
                    return Err("late PHI source is not a verified generation".into());
                };
                let Some(source_ty)=phi_types.get(source_generation)else{
                    return Err("late PHI stage references an untyped source".into());
                };
                if !matches!(source_ty,ConstType::RefMut(_)) ||
                    (projection.is_none() && ty!=source_ty) ||
                    *generation==*source_generation || children.len()!=parents.len() ||
                    children.len()<2 || children.len()>32 ||
                    event.op!=Access::BindPhiMut || event.loan!=Some(*generation) ||
                    event.parent!=Some(*source_generation) || !event.path.fields.is_empty() ||
                    *source_owner==event.path.owner ||
                    children.iter().zip(parents).any(|(child,parent)|
                        !child.exclusive || child.parent!=Some(*parent) ||
                        child.loan==*parent ||
                        self.loans.get(&child.loan)!=Some(&child.path) ||
                        self.loans.get(parent).is_none_or(|base|{
                            let expected=match projection {
                                Some(field)=>base.child(*field),None=>base.clone(),
                            };
                            expected!=child.path
                        })) {
                    return Err("invalid conditional PHI reborrow proof".into());
                }
                if phi_types.insert(*generation,ty.clone()).is_some(){
                    return Err("late PHI output generation has conflicting types".into());
                }
                let unique=children.iter().map(|o|o.loan).collect::<HashSet<_>>();
                if unique.len()!=children.len() ||
                    phi_groups.insert(*generation,(event.path.owner,
                        children.iter().map(|o|o.loan).collect())).is_some() {
                    return Err("reused or forged late PHI generation".into());
                }
                late_reborrows.push((*generation,*source_generation,children.iter()
                    .map(|child|(child.parent.expect("validated parent"),
                        child.loan,child.path.clone())).collect()));
            }
        }
        let successors=self.blocks.iter().map(|b|match &b.terminator{
            Terminator::Goto(next)=>next.clone(),Terminator::Return=>Vec::new(),
        }).collect();
        let mut graph=cfg_borrow::Graph::new(self.entry,successors)?;
        for (&generation,(owner,loans)) in &phi_groups {
            graph.register_phi_group_for_binding(generation,*owner,loans.clone())?;
        }
        for (generation,source,children) in late_reborrows {
            graph.register_phi_reborrow(generation,source,children)?;
        }
        let n=self.blocks.len();
        let mut use_sets:Vec<Option<Box<HashSet<SymbolId>>>>=vec![None;n];
        let mut def_sets:Vec<Option<Box<HashSet<SymbolId>>>>=vec![None;n];
        let mut parents=HashMap::<SymbolId,SymbolId>::new();
        for event in self.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events) {
            if event.op==Access::BindPhiMut{continue;}
            let (Some(child),Some(parent))=(event.loan,event.parent)else{continue};
            if child==parent {return Err("cyclic MIR reborrow parent loan".into());}
            if let Some(previous)=parents.insert(child,parent) {
                if previous!=parent {
                    return Err("reborrow loan has conflicting parent origins".into());
                }
            }
            let Some(parent_path)=self.loans.get(&parent) else {
                return Err("reborrow references an unknown parent loan".into());
            };
            if let Some(child_path)=self.loans.get(&child) {
                if !parent_path.ancestor_of(child_path) {
                    return Err("reborrow child path escapes parent provenance".into());
                }
            }
        }
        for statement in self.blocks.iter().flat_map(|block|block.statements.iter()) {
            if let Statement::LatePhiReborrow{children,..}=statement {
                for child in children {
                    let Some(parent)=child.parent else{
                        return Err("late PHI child has no parent".into());
                    };
                    if parents.insert(child.loan,parent).is_some() {
                        return Err("late PHI child parent is not unique".into());
                    }
                    let Some(base)=self.loans.get(&parent)else{
                        return Err("late PHI reborrow references a missing parent".into());
                    };
                    if !base.ancestor_of(&child.path) ||
                        child.path.fields.len()>base.fields.len()+1 {
                        return Err("late PHI child escapes borrowed MovePath".into());
                    }
                }
            }
        }
        let mut complete=HashSet::new();
        let mut visiting=HashSet::new();
        for &start in parents.keys() {
            if complete.contains(&start){continue;}
            visiting.clear();
            let mut next=start;
            while let Some(&parent)=parents.get(&next) {
                if complete.contains(&next){break;}
                if !visiting.insert(next) {
                    return Err("cyclic MIR reborrow parent loans".into());
                }
                next=parent;
            }
            complete.extend(visiting.iter().copied());
        }
        let mut ancestor_cache:HashMap<SymbolId,Vec<SymbolId>>=HashMap::new();
        for &id in self.loans.keys().filter(|&&id|parents.contains_key(&id)) {
            let mut ids=Vec::new();let mut current=Some(id);
            for _ in 0..=parents.len(){
                let Some(next)=current else{break;};
                ids.push(next);current=parents.get(&next).copied();
            }
            ancestor_cache.insert(id,ids);
        }
        let keep_ancestors=|slot:&mut Option<Box<HashSet<SymbolId>>>,id:SymbolId|{
            let set=slot.get_or_insert_with(||Box::new(HashSet::new()));
            if let Some(chain)=ancestor_cache.get(&id){
                set.extend(chain.iter().copied());
            }else if !parents.contains_key(&id){
                set.insert(id);
            }else{
                //Some temporary reborrows do not enter FunctionMir.loans
                let mut current=Some(id);
                for _ in 0..=parents.len(){
                    let Some(loan)=current else{break;};
                    set.insert(loan);current=parents.get(&loan).copied();
                }
            }
        };
        for (i,block) in self.blocks.iter().enumerate(){
            for statement in &block.statements {
                if let Statement::LatePhiReborrow{children,..}=statement {
                    for child in children {
                        def_sets[i].get_or_insert_with(||Box::new(HashSet::new()))
                            .insert(child.loan);
                        if let Some(parent)=child.parent {
                            keep_ancestors(&mut use_sets[i],parent);
                        }
                    }
                }
            }
            for statement in &block.statements {
                if let Statement::ValuePhi{alternatives,..}=statement {
                    for option in alternatives {
                        keep_ancestors(&mut use_sets[i],option.loan);
                    }
                }
            }
            let events=block.statements.iter().flat_map(Statement::events);
            for ev in events {
                if matches!(ev.op,Access::BorrowShared|Access::BorrowMut|Access::ReserveMut) {
                    if let Some(id)=ev.loan {
                        def_sets[i].get_or_insert_with(||Box::new(HashSet::new())).insert(id);
                    }
                }else if ev.loan.is_some() && !matches!(ev.op,Access::EndLoan|Access::BindPhiMut) {
                    if let Some(id)=ev.loan {
                        if matches!(ev.op,Access::Read|Access::Write) {
                            if let Some((owner,members))=phi_groups.get(&id) {
                                if ev.path!=Path::root(*owner) {
                                    return Err("reference PHI use refers to another binding".into());
                                }
                                //Only this precise PHI generation is live; alternatives from retired generations must not be kept alive
                                //by this read or write
                                for &member in members {
                                    keep_ancestors(&mut use_sets[i],member);
                                }
                            }else{keep_ancestors(&mut use_sets[i],id);}
                        }else{keep_ancestors(&mut use_sets[i],id);}
                    }
                }
                if ev.op!=Access::BindPhiMut {
                    if let Some(parent)=ev.parent{keep_ancestors(&mut use_sets[i],parent);}
                }
                graph.event(i,ev.clone())?;
            }
        }
        let mut escaped_phi_loans=HashSet::<SymbolId>::new();
        for (node,block) in self.blocks.iter().enumerate() {
            let terminal_candidates=block.statements.iter().enumerate()
                .filter_map(|(index,statement)|match statement {
                    Statement::ValuePhi{alternatives,generation:Some(_),..}
                        if !alternatives.is_empty() &&
                        block.statements[index+1..].iter().all(|tail|match tail {
                            Statement::StorageDead(_)=>true,
                            Statement::Access(e) if e.op==Access::EndLoan=>true,
                            _=>false,
                        })=>Some(alternatives),
                    _=>None,
                }).collect::<Vec<_>>();
            if terminal_candidates.is_empty(){continue;}
            let mut cursor=node;
            let mut visited=HashSet::new();
            for _ in 0..=n {
                if !visited.insert(cursor){break;}
                let target=&self.blocks[cursor];
                if cursor!=node && target.statements.iter().any(|statement|match statement {
                    Statement::StorageDead(_)=>false,
                    Statement::Access(e) if e.op==Access::EndLoan=>false,
                    _=>true,
                }){break;}
                match &target.terminator {
                    Terminator::Return=>{
                        for alternatives in &terminal_candidates {
                            for candidate in alternatives.iter() {
                                keep_ancestors(&mut use_sets[cursor],candidate.loan);
                                let mut current=Some(candidate.loan);
                                for _ in 0..=parents.len() {
                                    let Some(loan)=current else{break};
                                    escaped_phi_loans.insert(loan);
                                    current=parents.get(&loan).copied();
                                }
                            }
                        }
                        break;
                    }
                    Terminator::Goto(next) if next.len()==1=>cursor=next[0],
                    _=>break,
                }
            }
        }
        let mut predecessors=vec![Vec::<usize>::new();n];
        for (src,targets) in graph.successors.iter().enumerate(){
            for &dst in targets {predecessors[dst].push(src);}
        }
        let empty_live=Arc::new(HashSet::<SymbolId>::new());
        let mut live_in=vec![Arc::clone(&empty_live);n];
        let mut pending=vec![true;n];
        let mut queue=(0..n).rev().collect::<VecDeque<_>>();
        let mut steps=0usize;
        while let Some(i)=queue.pop_front(){
            pending[i]=false;
            steps+=1;
            if steps>2_000_000{return Err("typed MIR NLL worklist budget exhausted".into());}
            let next_live=if use_sets[i].is_none() && def_sets[i].is_none() &&
                graph.successors[i].len()==1 {
                Arc::clone(&live_in[graph.successors[i][0]])
            }else{
                let mut current=use_sets[i].as_deref().cloned().unwrap_or_default();
                for &to in &graph.successors[i] {current.extend(live_in[to].iter().copied());}
                if let Some(defs)=def_sets[i].as_ref() {
                    for id in defs.iter() {
                        if !use_sets[i].as_ref().is_some_and(|uses|uses.contains(id)) {
                            current.remove(id);
                        }
                    }
                }
                if current.is_empty(){Arc::clone(&empty_live)}else{Arc::new(current)}
            };
            if !Arc::ptr_eq(&live_in[i],&next_live) &&
                live_in[i].as_ref()!=next_live.as_ref() {
                live_in[i]=next_live;
                for &from in &predecessors[i] {
                    if !pending[from]{pending[from]=true;queue.push_back(from);}
                }
            }
        }
        let explicit_ends=self.blocks.iter().flat_map(|block|block.statements.iter())
            .flat_map(Statement::events)
            .filter(|event|event.op==Access::EndLoan)
            .filter_map(|event|event.loan).collect::<HashSet<_>>();
        let mut protected_ends=explicit_ends.clone();
        protected_ends.extend(escaped_phi_loans);
        for &id in &explicit_ends {
            let mut current=id;
            for _ in 0..=parents.len() {
                let Some(&parent)=parents.get(&current) else {break};
                protected_ends.insert(parent);
                current=parent;
            }
        }
        let mut auto_ended=HashMap::<usize,HashSet<SymbolId>>::new();
        if !self.loans.is_empty() {
            for (node,block) in self.blocks.iter().enumerate() {
                //Return may carry an implicit reference value whose escape is certified separately; do not expire it
                //here
                if matches!(&block.terminator,Terminator::Return) ||
                    block.statements.len()<2 {continue;}
                let mut future=HashSet::<SymbolId>::new();
                for &target in &graph.successors[node] {
                    future.extend(live_in[target].iter().copied());
                }
                let total=block.statements.iter().map(|s|s.events().len()).sum::<usize>();
                let mut boundary=total;
                let mut insertions=Vec::<(usize,Vec<SymbolId>)>::new();
                for stmt in block.statements.iter().rev() {
                    let after=boundary;
                    boundary-=stmt.events().len();
                    let mut used=HashSet::<SymbolId>::new();
                    let mut defined=HashSet::<SymbolId>::new();
                    let mut require=|id:SymbolId| {
                        let mut current=Some(id);
                        for _ in 0..=parents.len() {
                            let Some(loan)=current else{break};
                            used.insert(loan);
                            current=parents.get(&loan).copied();
                        }
                    };
                    match stmt {
                        Statement::LatePhiReborrow{children,..}=>{
                            for child in children {
                                defined.insert(child.loan);
                                if let Some(parent)=child.parent {require(parent);}
                            }
                        }
                        Statement::ValuePhi{alternatives,..}=>{
                            for option in alternatives {require(option.loan);}
                        }
                        _=>(),
                    }
                    for event in stmt.events() {
                        if matches!(event.op,Access::BorrowShared|Access::BorrowMut|
                            Access::ReserveMut) {
                            if let Some(id)=event.loan {defined.insert(id);}
                        }else if !matches!(event.op,Access::EndLoan|Access::BindPhiMut) {
                            if let Some(id)=event.loan {
                                if matches!(event.op,Access::Read|Access::Write) {
                                    if let Some((_,members))=phi_groups.get(&id) {
                                        for &member in members {require(member);}
                                    }else{require(id);}
                                }else{require(id);}
                            }
                        }
                        if event.op!=Access::BindPhiMut {
                            if let Some(parent)=event.parent {require(parent);}
                        }
                    }
                    if after<total {
                        let mut ending=used.iter().chain(defined.iter()).filter(|id|
                            !future.contains(*id) && !protected_ends.contains(*id) &&
                            self.loans.contains_key(*id)).copied().collect::<Vec<_>>();
                        ending.sort_unstable_by_key(|id|{
                            let mut depth=0usize;
                            let mut current=*id;
                            for _ in 0..=parents.len() {
                                let Some(&parent)=parents.get(&current) else{break};
                                depth+=1;current=parent;
                            }
                            (std::cmp::Reverse(depth),id.0)
                        });
                        ending.dedup();
                        if !ending.is_empty(){
                            auto_ended.entry(node).or_default().extend(ending.iter().copied());
                            insertions.push((after,ending));
                        }
                    }
                    for id in defined {future.remove(&id);}
                    future.extend(used);
                }
                for (at,ending) in insertions {
                    for id in ending.iter().rev() {
                        let path=self.loans.get(id).expect("validated inferred NLL loan");
                        graph.event_at(node,at,Event{op:Access::EndLoan,
                            path:path.clone(),loan:Some(*id),parent:None,token:0})?;
                    }
                }
            }
        }
        //Bridge NLL may-liveness to region outlives constraints
        if !parents.is_empty() {
            use crate::cfg_nll::{CfgPointId,LocalRegion};
            use crate::ir::Place;
            use crate::region_infer::{LocalRegionInference,LoanKind};
            let mut local=LocalRegionInference::default();
            let mut region_ids=HashMap::new();
            let involved=parents.keys().copied().chain(parents.values().copied())
                .collect::<HashSet<_>>();
            for loan in involved {
                let Some(path)=self.loans.get(&loan)else{continue};
                let field_ids=path.fields.iter().map(|key|key.field).collect::<Vec<_>>();
                let place=Place::from_fields(&field_ids)
                    .ok_or("MIR reborrow projection exceeds maximum depth")?;
                let points=(0..n).filter(|&point|{
                    live_in[point].contains(&loan) ||
                    def_sets[point].as_ref().is_some_and(|defs|defs.contains(&loan))
                }).map(|point|CfgPointId(point as u32)).collect();
                let id=local.add_loan(LocalRegion{
                    binding:loan,owner:path.owner,place,points,
                },LoanKind::Exclusive);
                region_ids.insert(loan,id);
            }
            for (&child,&parent) in &parents {
                let (Some(&child_region),Some(&parent_region))=
                    (region_ids.get(&child),region_ids.get(&parent))else{continue};
                //This is an outlives constraint to SOLVE, not a pointwise check of the unsolved may-live approximation
                local.require_outlives(parent_region,child_region);
            }
            local.solve()?;
        }
        for (node,_block) in self.blocks.iter().enumerate(){
            if live_in[node].is_empty() && use_sets[node].is_none() && def_sets[node].is_none(){
                continue;
            }
            let mut active=live_in[node].as_ref().clone();
            if let Some(defs)=def_sets[node].as_ref() {active.extend(defs.iter().copied());}
            if let Some(uses)=use_sets[node].as_ref() {active.extend(uses.iter().copied());}
            let outgoing: &[usize]=match &self.blocks[node].terminator {
                Terminator::Goto(next)=>next.as_slice(),
                Terminator::Return=>&[],
            };
            for &next in outgoing {
                let mut ending=active.iter().filter(|id|
                    !live_in[next].contains(*id) &&
                    !auto_ended.get(&node).is_some_and(|ends|ends.contains(*id)))
                    .copied().collect::<Vec<_>>();
                ending.sort_by_key(|id|{
                    let mut depth=0usize;
                    let mut current=*id;
                    for _ in 0..=parents.len(){
                        let Some(parent)=parents.get(&current)else{break;};
                        depth+=1;current=*parent;
                    }
                    std::cmp::Reverse(depth)
                });
                for loan in ending {
                    if let Some(path)=self.loans.get(&loan){
                        graph.event_on_edge(node,next,Event{op:Access::EndLoan,path:path.clone(),loan:Some(loan),parent:None,token:0})?;
                    }
                }
            }
        }
        let mut errors=graph.check()?;
        if !errors.is_empty() {
            for conflict in &mut errors {
                if let Some(method)=self.blocks.iter().flat_map(|b|b.statements.iter())
                    .find_map(|statement|match statement {
                        Statement::Call{name,token,..} if *token==conflict.token=>Some(name.as_str()),
                        Statement::HostOperation{name,events}|Statement::QuantumOperation{name,events}
                            if events.iter().any(|e|e.token==conflict.token)=>Some(name.as_str()),
                        _=>None,
                    }) {
                    conflict.message.push_str(&format!(" (in method call '{method}')"));
                }
            }
        }
        Ok(errors)
    }
}
#[derive(Default)]
struct CaseNllBoundaries {
    after: HashMap<(usize,usize),Vec<SymbolId>>,
    edges: HashMap<(usize,usize),Vec<SymbolId>>,
}

impl FunctionMir {
    //It never specializes by a guessed return origin or a callee's path-case index
    fn case_nll_boundaries(&self,
        parents:&HashMap<SymbolId,SymbolId>)
        ->Option<CaseNllBoundaries> {
        let n=self.blocks.len();
        if n==0 || self.entry>=n {return None;}
        if self.loans.is_empty(){return Some(CaseNllBoundaries::default());}
        let mut use_sets=vec![HashSet::<SymbolId>::new();n];
        let mut def_sets=vec![HashSet::<SymbolId>::new();n];
        let mut successors=Vec::with_capacity(n);
        let mut predecessors=vec![Vec::new();n];
        let mut explicit=HashSet::new();
        let mut escaped=HashSet::new();
        let mut last_use_witnesses=HashSet::<SymbolId>::new();
        let mut phi_members=HashMap::<SymbolId,Vec<SymbolId>>::new();
        for stmt in self.blocks.iter().flat_map(|b|b.statements.iter()) {
            let pair=match stmt {
                Statement::ValuePhi{generation:Some(id),alternatives,..}
                    if !alternatives.is_empty()=>Some((*id,alternatives.iter()
                        .map(|candidate|candidate.loan).collect::<Vec<_>>())),
                Statement::LatePhiReborrow{generation,children,..}=>
                    Some((*generation,children.iter().map(|child|child.loan)
                        .collect::<Vec<_>>())),
                _=>None,
            };
            if let Some((id,loans))=pair {
                if phi_members.insert(id,loans).is_some(){return None;}
            }
        }
        let expand=|set:&mut HashSet<SymbolId>,id:SymbolId|->Option<()> {
            let mut current=id;
            let mut seen=HashSet::new();
            loop {
                if !seen.insert(current){return None;}
                set.insert(current);
                match parents.get(&current) {
                    Some(parent)=>current=*parent,
                    None=>break,
                }
            }
            Some(())
        };
        for (node,block) in self.blocks.iter().enumerate() {
            let outgoing=match &block.terminator {
                Terminator::Goto(next)=>next.clone(),
                Terminator::Return=>Vec::new(),
            };
            for &target in &outgoing {
                if target>=n{return None;}
                predecessors[target].push(node);
            }
            successors.push(outgoing);
            for stmt in &block.statements {
                match stmt {
                    Statement::ValuePhi{alternatives,..}=>{
                        for candidate in alternatives {
                            expand(&mut use_sets[node],candidate.loan)?;
                        }
                    }
                    Statement::LatePhiReborrow{children,..}=>{
                        for child in children {
                            def_sets[node].insert(child.loan);
                            expand(&mut use_sets[node],child.parent?)?;
                        }
                    }
                    _=>(),
                }
                for ev in stmt.events() {
                    if matches!(ev.op,Access::Read|Access::Write) {
                        if let Some(id)=ev.loan {
                            if let Some(options)=phi_members.get(&id) {
                                for &loan in options {
                                    expand(&mut last_use_witnesses,loan)?;
                                }
                            }else if self.loans.contains_key(&id) {
                                expand(&mut last_use_witnesses,id)?;
                            }
                        }
                    }
                    if ev.op==Access::EndLoan {
                        if let Some(id)=ev.loan {explicit.insert(id);}
                    }else if matches!(ev.op,Access::BorrowMut|Access::BorrowShared|
                        Access::ReserveMut) {
                        if let Some(id)=ev.loan {def_sets[node].insert(id);}
                    }else if ev.op!=Access::BindPhiMut {
                        if let Some(id)=ev.loan {
                            if matches!(ev.op,Access::Read|Access::Write) {
                                if let Some(options)=phi_members.get(&id) {
                                    for &loan in options {
                                        expand(&mut use_sets[node],loan)?;
                                    }
                                }else {expand(&mut use_sets[node],id)?;}
                            }else{expand(&mut use_sets[node],id)?;}
                        }
                    }
                    if ev.op!=Access::BindPhiMut {
                        if let Some(parent)=ev.parent {
                            expand(&mut use_sets[node],parent)?;
                        }
                    }
                }
            }
        }
        for (node,block) in self.blocks.iter().enumerate() {
            for (index,stmt) in block.statements.iter().enumerate() {
                let Statement::ValuePhi{alternatives,..}=stmt else{continue};
                if alternatives.is_empty() || !block.statements[index+1..].iter()
                    .all(|s|matches!(s,Statement::StorageDead(_)) ||
                        matches!(s,Statement::Access(e) if e.op==Access::EndLoan)) {
                    continue;
                }
                let mut cursor=node;
                let mut seen=HashSet::new();
                for _ in 0..=n {
                    if !seen.insert(cursor){break;}
                    let current=&self.blocks[cursor];
                    if cursor!=node && current.statements.iter().any(|s|
                        !matches!(s,Statement::StorageDead(_)) &&
                        !matches!(s,Statement::Access(e) if e.op==Access::EndLoan)) {
                        break;
                    }
                    match &current.terminator {
                        Terminator::Return=>{
                            for option in alternatives {
                                expand(&mut use_sets[cursor],option.loan)?;
                                expand(&mut escaped,option.loan)?;
                            }
                            break;
                        }
                        Terminator::Goto(next) if next.len()==1=>cursor=next[0],
                        _=>break,
                    }
                }
            }
        }
        let mut protected=escaped;
        for id in explicit {expand(&mut protected,id)?;}
        let mut live_in=vec![HashSet::<SymbolId>::new();n];
        let mut queue=(0..n).rev().collect::<VecDeque<_>>();
        let mut queued=vec![true;n];
        let mut steps=0usize;
        while let Some(node)=queue.pop_front() {
            queued[node]=false;
            steps+=1;
            if steps>2_000_000{return None;}
            let mut new=use_sets[node].clone();
            for &next in &successors[node] {new.extend(live_in[next].iter().copied());}
            for &id in &def_sets[node] {
                if !use_sets[node].contains(&id){new.remove(&id);}
            }
            if new!=live_in[node] {
                live_in[node]=new;
                for &previous in &predecessors[node] {
                    if !queued[previous] {
                        queued[previous]=true;
                        queue.push_back(previous);
                    }
                }
            }
        }
        let depth=|id:SymbolId|->usize {
            let mut level=0;
            let mut current=id;
            for _ in 0..=parents.len() {
                let Some(&p)=parents.get(&current)else{break};
                level+=1;
                current=p;
            }
            level
        };
        let mut plan=CaseNllBoundaries::default();
        let mut ended_in_block=vec![HashSet::<SymbolId>::new();n];
        for (node,block) in self.blocks.iter().enumerate() {
            if matches!(&block.terminator,Terminator::Return) ||
                block.statements.len()<2 {continue;}
            let mut future=HashSet::new();
            for &next in &successors[node] {future.extend(live_in[next].iter().copied());}
            let total=block.statements.iter().map(|s|s.events().len()).sum::<usize>();
            let mut after_events=total;
            for (index,stmt) in block.statements.iter().enumerate().rev() {
                let after=after_events;
                after_events-=stmt.events().len();
                let mut used=HashSet::new();
                let mut defined=HashSet::new();
                match stmt {
                    Statement::ValuePhi{alternatives,..}=>{
                        for option in alternatives {expand(&mut used,option.loan)?;}
                    }
                    Statement::LatePhiReborrow{children,..}=>{
                        for child in children {
                            defined.insert(child.loan);
                            expand(&mut used,child.parent?)?;
                        }
                    }
                    _=>(),
                }
                for ev in stmt.events() {
                    if matches!(ev.op,Access::BorrowShared|Access::BorrowMut|
                        Access::ReserveMut) {
                        if let Some(id)=ev.loan {defined.insert(id);}
                    }else if !matches!(ev.op,Access::EndLoan|Access::BindPhiMut) {
                        if let Some(id)=ev.loan {
                            if matches!(ev.op,Access::Read|Access::Write) {
                                if let Some(options)=phi_members.get(&id) {
                                    for &loan in options {expand(&mut used,loan)?;}
                                }else {expand(&mut used,id)?;}
                            }else {expand(&mut used,id)?;}
                        }
                    }
                    if ev.op!=Access::BindPhiMut {
                        if let Some(parent)=ev.parent {expand(&mut used,parent)?;}
                    }
                }
                if after<total {
                    let mut dead=used.iter().chain(defined.iter())
                        .filter(|id|last_use_witnesses.contains(*id) &&
                            !future.contains(*id) && !protected.contains(*id) &&
                            self.loans.contains_key(*id)).copied().collect::<Vec<_>>();
                    dead.sort_by_key(|id|(std::cmp::Reverse(depth(*id)),id.0));
                    dead.dedup();
                    if !dead.is_empty() {
                        ended_in_block[node].extend(dead.iter().copied());
                        plan.after.insert((node,index+1),dead);
                    }
                }
                for id in defined {future.remove(&id);}
                future.extend(used);
            }
        }
        for node in 0..n {
            let mut active=live_in[node].clone();
            active.extend(use_sets[node].iter().copied());
            active.extend(def_sets[node].iter().copied());
            for &next in &successors[node] {
                let mut dead=active.iter().filter(|id|last_use_witnesses.contains(*id) &&
                    !live_in[next].contains(*id) && !ended_in_block[node].contains(*id) &&
                    !protected.contains(*id) && self.loans.contains_key(*id))
                    .copied().collect::<Vec<_>>();
                dead.sort_by_key(|id|(std::cmp::Reverse(depth(*id)),id.0));
                dead.dedup();
                if !dead.is_empty(){plan.edges.insert((node,next),dead);}
            }
        }
        Some(plan)
    }
}

impl FunctionMir {
    pub fn solve_path_cases(&self,token_count:usize,formals:&[(String,ConstType)],
        origins:&[VerifiedReturnedReference])->Option<Vec<VerifiedPathCase>> {
        const MAX_CASES:usize=128;
        const MAX_STATES:usize=4096;
        const MAX_STEPS:usize=100_000;
        const MAX_EFFECTS:usize=96;
        #[derive(Clone,Hash,PartialEq,Eq)]
        struct Trace {
            node:usize,
            prev:Option<usize>,
            effects:Vec<VerifiedParameterEffect>,
            selected:Option<usize>,
            //The terminal returned provenance must still be live at Return, including all ancestors of a late
            //conditional reborrow
            returned_loan:Option<SymbolId>,
            phi_choices:Vec<(SymbolId,SymbolId)>,
            uninit:Vec<Path>,
            live_loans:Vec<SymbolId>,
        }
        fn sort_effects(effects:&mut Vec<VerifiedParameterEffect>) {
            effects.sort_by(|a,b| a.parameter.cmp(&b.parameter)
                .then_with(||(a.kind as u8).cmp(&(b.kind as u8)))
                .then_with(||a.fields.iter().map(|k|(k.aggregate.0,k.field.0))
                    .cmp(b.fields.iter().map(|k|(k.aggregate.0,k.field.0)))));
            effects.dedup();
        }
        fn sort_paths(paths:&mut Vec<Path>) {
            paths.sort_by(|a,b|a.owner.0.cmp(&b.owner.0)
                .then_with(||a.fields.iter().map(|k|(k.aggregate.0,k.field.0))
                    .cmp(b.fields.iter().map(|k|(k.aggregate.0,k.field.0)))));
            paths.dedup();
        }
        fn initialized(state:&Trace,path:&Path)->bool {
            !state.uninit.iter().any(|m|m.overlaps(path))
        }
        fn apply_ownership(state:&mut Trace,event:&Event,
            loan_paths:&HashMap<SymbolId,Path>,
            parents:&HashMap<SymbolId,SymbolId>)->Option<()> {
            let path=&event.path;
            match event.op {
                Access::StorageLive|Access::StorageDead => {
                    if !path.fields.is_empty(){return None;}
                    state.uninit.retain(|m|m.owner!=path.owner);
                    state.uninit.push(path.clone());
                    sort_paths(&mut state.uninit);
                }
                Access::Move|Access::Drop => {
                    if !initialized(state,path){return None;}
                    if state.live_loans.iter().any(|id|loan_paths.get(id)
                        .is_none_or(|referent|referent.overlaps(path))){return None;}
                    state.uninit.push(path.clone());
                    sort_paths(&mut state.uninit);
                }
                Access::Read|Access::BorrowShared|Access::BorrowMut|Access::ReserveMut => {
                    if !initialized(state,path){return None;}
                    if matches!(event.op,Access::BorrowShared|Access::BorrowMut|Access::ReserveMut) {
                        let id=event.loan?;
                        if state.live_loans.contains(&id) ||
                            loan_paths.get(&id)!=Some(path){return None;}
                        if let Some(parent)=event.parent {
                            if parents.get(&id)!=Some(&parent) ||
                                !state.live_loans.contains(&parent) ||
                                !loan_paths.get(&parent)?.ancestor_of(path) {
                                return None;
                            }
                        }
                        state.live_loans.push(id);
                        state.live_loans.sort_unstable_by_key(|id|id.0);
                    }
                }
                Access::Initialize|Access::Write => {
                    //A field cannot be initialized through a previously moved whole owner. Its ancestor must still exist
                    if state.uninit.iter().any(|m|m.ancestor_of(path) && m!=path){
                        return None;
                    }
                    state.uninit.retain(|m|!path.ancestor_of(m));
                }
                Access::EndLoan=>{
                    let id=event.loan?;
                    //A fabricated EndLoan is not an NLL certificate. Even when a loan is absent on the current conditional
                    //arm, its identity must exist in this MIR function
                    if !loan_paths.contains_key(&id) {return None;}
                    if state.live_loans.contains(&id) {
                        if loan_paths.get(&id)!=Some(path){return None;}
                        for &live in &state.live_loans {
                            if live==id{continue;}
                            let mut cursor=live;
                            let mut visited=HashSet::new();
                            while let Some(&parent)=parents.get(&cursor) {
                                if !visited.insert(cursor) || parent==id{return None;}
                                cursor=parent;
                            }
                        }
                        state.live_loans.retain(|live|*live!=id);
                    }
                }
                Access::ActivateMut|Access::QuantumRequireConsumed=>(),
                Access::BindPhiMut=>return None,
            }
            Some(())
        }
        fn terminal_return_phi(mir:&FunctionMir,from:usize)->bool {
            let mut node=from;
            let mut seen=HashSet::new();
            for _ in 0..16 {
                if !seen.insert(node){return false;}
                let Some(block)=mir.blocks.get(node)else{return false};
                if node!=from && block.statements.iter().any(|s|match s {
                    Statement::StorageDead(_)=>false,
                    Statement::Access(e) if e.op==Access::EndLoan=>false,
                    _=>true,
                }){return false;}
                match &block.terminator {
                    Terminator::Return=>return true,
                    Terminator::Goto(next) if next.len()==1=>node=next[0],
                    _=>return false,
                }
            }
            false
        }
        fn map_event(event:&Event,token_count:usize,params:usize)
            ->Option<VerifiedParameterEffect> {
            let start=token_count.checked_add(1)?;
            let parameter=(event.path.owner.0 as usize).checked_sub(start)?;
            if parameter>=params{return None;}
            let kind=match event.op {
                Access::Move=>VerifiedEffectKind::Move,
                Access::Drop=>VerifiedEffectKind::Drop,
                Access::Write|Access::Initialize=>VerifiedEffectKind::Write,
                _=>return None,
            };
            Some(VerifiedParameterEffect{parameter,fields:event.path.fields.clone(),kind})
        }
        fn map_applied(effect:&VerifiedAppliedEffect,token_count:usize,params:usize)
            ->Option<VerifiedParameterEffect> {
            let start=token_count.checked_add(1)?;
            let parameter=(effect.path.owner.0 as usize).checked_sub(start)?;
            (parameter<params).then(||VerifiedParameterEffect{
                parameter,fields:effect.path.fields.clone(),kind:effect.kind,
            })
        }
        fn record(state:&mut Trace,effect:VerifiedParameterEffect)->Option<()> {
            state.effects.push(effect);
            sort_effects(&mut state.effects);
            (state.effects.len()<=MAX_EFFECTS).then_some(())
        }
        //An effect recorded in a callee's exact path-case must also update the caller's ownership state
        fn apply_exact_effect(state:&mut Trace,effect:&VerifiedAppliedEffect,
            events:&[Event],loan_paths:&HashMap<SymbolId,Path>,
            parents:&HashMap<SymbolId,SymbolId>)->Option<()> {
            let op=match effect.kind {
                VerifiedEffectKind::Move=>Access::Move,
                VerifiedEffectKind::Drop=>Access::Drop,
                VerifiedEffectKind::Write=>Access::Write,
            };
            let transferred=events.iter().any(|event|
                matches!(event.op,Access::Move|Access::Drop) &&
                    event.path.ancestor_of(&effect.path));
            if transferred {
                return (!initialized(state,&effect.path)).then_some(());
            }
            apply_ownership(state,&Event{op,path:effect.path.clone(),
                loan:None,parent:None,token:0},loan_paths,parents)
        }
        fn live_chain(state:&Trace,id:SymbolId,
            parents:&HashMap<SymbolId,SymbolId>)->bool {
            let mut current=id;
            let mut visited=HashSet::new();
            loop {
                if !state.live_loans.contains(&current) || !visited.insert(current){
                    return false;
                }
                match parents.get(&current){
                    Some(parent)=>current=*parent,
                    None=>break,
                }
            }
            //An exclusive parent is suspended while any descendant remains live, even though NLL must keep that
            //parent itself alive
            for &other in &state.live_loans {
                if other==id{continue;}
                let mut cursor=other;
                let mut visited=HashSet::new();
                while let Some(parent)=parents.get(&cursor) {
                    if !visited.insert(cursor){return false;}
                    if *parent==id{return false;}
                    cursor=*parent;
                }
            }
            true
        }
        fn resolve_effect(effect:&VerifiedAppliedEffect,events:&[Event],state:&Trace,
            declarations:&HashMap<(Path,SymbolId),Vec<RefOption>>,
            parents:&HashMap<SymbolId,SymbolId>)
            ->Option<VerifiedAppliedEffect> {
            if effect.alternatives.is_empty(){return Some(effect.clone());}
            if effect.kind!=VerifiedEffectKind::Write ||
                !effect.path.fields.is_empty(){return None;}
            let generations=events.iter().filter(|e|e.op==Access::Write &&
                e.path==effect.path).filter_map(|e|e.loan)
                .collect::<HashSet<_>>();
            if generations.len()!=1{return None;}
            let generation=*generations.iter().next()?;
            let options=declarations.get(&(effect.path.clone(),generation))?;
            if options.len()!=effect.alternatives.len() || options.len()<2 ||
                options.len()>32{return None;}
            let mut suffix:Option<Vec<FieldKey>>=None;
            for (candidate,target) in options.iter().zip(&effect.alternatives){
                if !candidate.exclusive || !candidate.path.ancestor_of(target){return None;}
                let fields=target.fields[candidate.path.fields.len()..].to_vec();
                if suffix.as_ref().is_some_and(|old|old!=&fields){
                    return None;
                }
                suffix=Some(fields);
            }
            let selected=state.phi_choices.iter()
                .find(|(id,_)|*id==generation).map(|(_,loan)|*loan)?;
            if !live_chain(state,selected,parents){return None;}
            let index=options.iter().position(|option|option.loan==selected)?;
            if !initialized(state,&effect.alternatives[index]) {return None;}
            Some(VerifiedAppliedEffect{path:effect.alternatives[index].clone(),
                kind:effect.kind,alternatives:Vec::new()})
        }
        if self.blocks.is_empty() || self.entry>=self.blocks.len(){return None;}
        let mut declarations=HashMap::<(Path,SymbolId),Vec<RefOption>>::new();
        let mut groups=HashMap::<SymbolId,(ConstType,Vec<RefOption>)>::new();
        let mut group_roots=HashMap::<SymbolId,SymbolId>::new();
        let mut unique_generations=HashSet::<SymbolId>::new();
        let mut stages=Vec::new();
        for block in &self.blocks {for statement in &block.statements {
            match statement {
                Statement::ValuePhi{ty,check,generation:Some(id),
                    alternatives,..} if matches!(ty,ConstType::RefMut(_))=>{
                    if !unique_generations.insert(*id) || alternatives.len()<2 ||
                        alternatives.len()>32 ||
                        declarations.insert((check.path.clone(),*id),
                            alternatives.clone()).is_some(){return None;}
                    if self.loans.contains_key(id){return None;}
                    groups.insert(*id,(ty.clone(),alternatives.clone()));
                    group_roots.insert(*id,check.path.owner);
                }
                Statement::LatePhiReborrow{ty,source_generation,generation,
                    children,event,projection}=>{
                    if !unique_generations.insert(*generation) ||
                        self.loans.contains_key(generation){return None;}
                    stages.push((ty,source_generation,generation,children,event,projection));
                }
                _=>(),
            }
        }}
        let direct_loan_ids=self.blocks.iter().flat_map(|block|
            block.statements.iter()).filter_map(|statement|match statement {
                Statement::Access(event) if event.parent.is_none() &&
                    matches!(event.op,Access::BorrowMut|Access::BorrowShared|Access::ReserveMut)
                    =>event.loan,
                _=>None,
            }).collect::<HashSet<_>>();
        let mut parents=HashMap::<SymbolId,SymbolId>::new();
        let mut unresolved=stages;
        for _ in 0..=unresolved.len() {
            if unresolved.is_empty(){break;}
            let mut remaining=Vec::new();
            let mut progress=false;
            for (ty,source,generation,children,event,projection) in unresolved {
                let Some((source_ty,options))=groups.get(source) else {
                    remaining.push((ty,source,generation,children,event,projection));
                    continue;
                };
                if !matches!(source_ty,ConstType::RefMut(_)) ||
                    !matches!(ty,ConstType::RefMut(_)) ||
                    (projection.is_none() && ty!=source_ty) ||
                    group_roots.get(source)==Some(&event.path.owner) ||
                    event.op!=Access::BindPhiMut || event.loan!=Some(*generation) ||
                    event.parent!=Some(*source) || !event.path.fields.is_empty() ||
                    children.len()!=options.len() || children.len()<2 ||
                    children.len()>32 || children.iter().map(|c|c.loan)
                        .collect::<HashSet<_>>().len()!=children.len() {
                    return None;
                }
                for (child,original) in children.iter().zip(options) {
                    let expected=match projection {
                        Some(field)=>original.path.child(*field),
                        None=>original.path.clone(),
                    };
                    if !child.exclusive || child.parent!=Some(original.loan) ||
                        child.path!=expected || direct_loan_ids.contains(&child.loan) ||
                        options.iter().any(|option|option.loan==child.loan) ||
                        self.loans.get(&child.loan)!=Some(&child.path) ||
                        self.loans.get(&original.loan)!=Some(&original.path) ||
                        parents.insert(child.loan,original.loan).is_some() {return None;}
                }
                if declarations.insert((event.path.clone(),*generation),
                    children.clone()).is_some(){return None;}
                groups.insert(*generation,(ty.clone(),children.clone()));
                group_roots.insert(*generation,event.path.owner);
                progress=true;
            }
            if !progress && !remaining.is_empty(){return None;}
            unresolved=remaining;
        }
        if !unresolved.is_empty(){return None;}
        for event in self.blocks.iter().flat_map(|block|block.statements.iter())
            .flat_map(Statement::events) {
            if !matches!(event.op,Access::BorrowMut|Access::BorrowShared|Access::ReserveMut){
                continue;
            }
            let Some(parent)=event.parent else{continue;};
            let child=event.loan?;
            if child==parent || self.loans.get(&child)!=Some(&event.path) ||
                !self.loans.get(&parent)?.ancestor_of(&event.path) ||
                parents.get(&child).is_some_and(|previous|*previous!=parent){return None;}
            parents.insert(child,parent);
        }
        let mut completed=HashSet::new();
        for &start in parents.keys() {
            if completed.contains(&start){continue;}
            let mut cursor=start;
            let mut visiting=HashSet::new();
            while let Some(&parent)=parents.get(&cursor) {
                if completed.contains(&cursor){break;}
                if !visiting.insert(cursor){return None;}
                cursor=parent;
            }
            completed.extend(visiting);
        }
        let nll=self.case_nll_boundaries(&parents)?;
        let mut pending=VecDeque::new();
        pending.push_back(Trace{node:self.entry,prev:None,
            effects:Vec::new(),selected:None,returned_loan:None,
            phi_choices:Vec::new(),uninit:Vec::new(),live_loans:Vec::new()});
        let mut seen=HashSet::<Trace>::new();
        let mut results=Vec::<VerifiedPathCase>::new();
        let mut steps=0usize;
        while let Some(state)=pending.pop_front() {
            steps+=1;
            if steps>MAX_STEPS || state.node>=self.blocks.len() ||
                seen.len()+pending.len()>MAX_STATES{return None;}
            if !seen.insert(state.clone()){continue;}
            let block_index=state.node;
            let block=&self.blocks[state.node];
            let mut states=vec![state];
            for (position,statement) in block.statements.iter().enumerate() {
                let mut next=Vec::new();
                for mut state in states {
                    if let Statement::ValuePhi{ty,predecessors,alternatives,
                            generation,..}=statement {
                        if !alternatives.is_empty() {
                            if predecessors.len()!=alternatives.len() ||
                                !matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_)) {
                                return None;
                            }
                            let pred=state.prev?;
                            if predecessors.iter().filter(|&&p|p==pred).count()!=1 {
                                return None;
                            }
                            let at=predecessors.iter().position(|p|*p==pred)?;
                            let alternative=&alternatives[at];
                            if alternative.exclusive!=matches!(ty,ConstType::RefMut(_)) ||
                                self.loans.get(&alternative.loan)!=Some(&alternative.path) ||
                                !initialized(&state,&alternative.path) ||
                                !state.live_loans.contains(&alternative.loan) {return None;}
                            if let Some(id)=generation {
                                if state.phi_choices.iter().any(|(prior,loan)|
                                    *prior==*id && *loan!=alternative.loan){return None;}
                                if !state.phi_choices.iter().any(|(prior,_)|prior==id){
                                    state.phi_choices.push((*id,alternative.loan));
                                    state.phi_choices.sort_unstable_by_key(|(id,_)|id.0);
                                    if state.phi_choices.len()>32{return None;}
                                }
                            }
                            let terminal=terminal_return_phi(self,state.node) &&
                                block.statements[position+1..].iter().all(|s|match s {
                                    Statement::StorageDead(_)=>true,
                                    Statement::Access(e) if e.op==Access::EndLoan=>true,
                                    _=>false,
                                });
                            if terminal {
                                //Without a certified return-origin set, a terminal reference PHI cannot be silently treated as a
                                //unit-returning call
                                if origins.is_empty() || block.statements.iter()
                                    .filter(|stmt|matches!(stmt,
                                        Statement::ValuePhi{alternatives,..}
                                            if !alternatives.is_empty())).count()!=1 {
                                    return None;
                                }
                                let matches=origins.iter().enumerate().filter(|(_,origin)|{
                                    let owner=token_count.checked_add(1)
                                        .and_then(|base|base.checked_add(origin.parameter));
                                    origin.parameter<formals.len() &&
                                        owner==Some(alternative.path.owner.0 as usize) &&
                                        alternative.path.fields==origin.fields && &origin.ty==ty
                                }).map(|(i,_)|i).collect::<Vec<_>>();
                                if matches.len()!=1{return None;}
                                if state.selected.is_some_and(|prior|prior!=matches[0]){
                                    return None;
                                }
                                state.selected=Some(matches[0]);
                                state.returned_loan=Some(alternative.loan);
                            }
                        }
                    }
                    if let Statement::LatePhiReborrow{source_generation,generation,
                            children,event,projection,..}=statement {
                        let source=state.phi_choices.iter().find(|(id,_)|
                            id==source_generation).map(|(_,loan)|*loan)?;
                        if !live_chain(&state,source,&parents) {return None;}
                        let options=&groups.get(source_generation)?.1;
                        let index=options.iter().position(|option|option.loan==source)?;
                        let child=children.get(index)?;
                        let expected=match projection {
                            Some(field)=>options[index].path.child(*field),
                            None=>options[index].path.clone(),
                        };
                        if event.op!=Access::BindPhiMut ||
                            event.loan!=Some(*generation) ||
                            event.parent!=Some(*source_generation) ||
                            child.parent!=Some(source) || child.path!=expected ||
                            !initialized(&state,&expected) ||
                            state.live_loans.contains(&child.loan) ||
                            state.phi_choices.iter().any(|(id,_)|id==generation) {
                            return None;
                        }
                        state.live_loans.push(child.loan);
                        state.live_loans.sort_unstable_by_key(|id|id.0);
                        state.phi_choices.push((*generation,child.loan));
                        state.phi_choices.sort_unstable_by_key(|(id,_)|id.0);
                        if state.phi_choices.len()>32{return None;}
                        next.push(state);
                        continue;
                    }
                    if let Statement::Call{path_cases,events,effects,..}=statement {
                        let has_symbolic=effects.iter().any(|effect|
                            !effect.alternatives.is_empty()) ||
                            path_cases.iter().any(|case|case.effects.iter().any(|effect|
                                !effect.alternatives.is_empty()));
                        //A disjunctive PHI Write requires complete, exact callee cases. Never manufacture per-branch effects
                        //from a MAY union or accept an omitted witness
                        if has_symbolic && (path_cases.is_empty() ||
                            path_cases.iter().any(|case|!case.uninitialized.is_empty()) ||
                            effects.iter().any(|effect|!path_cases.iter()
                                .any(|case|case.effects.contains(effect))) ||
                            path_cases.iter().any(|case|case.effects.iter()
                                .any(|effect|!effects.contains(effect)))){return None;}
                        for event in events {
                            if matches!(event.op,Access::Write|Access::Initialize) &&
                                !path_cases.is_empty(){continue;}
                            apply_ownership(&mut state,event,&self.loans,&parents)?;
                            if matches!(event.op,Access::Write|Access::Initialize) &&
                                !path_cases.is_empty(){continue;}
                            if let Some(effect)=map_event(event,token_count,formals.len()){
                                record(&mut state,effect)?;
                            }
                        }
                        if path_cases.is_empty() {
                            for effect in effects {
                                let actual=resolve_effect(effect,events,&state,&declarations,&parents)?;
                                //Without exact cases, a MAY-Write must not manufacture initialization
                                if matches!(actual.kind,VerifiedEffectKind::Move|
                                    VerifiedEffectKind::Drop) {
                                    //A missing exact case cannot silently excuse a second Move/Drop of an already consumed caller place
                                    let transferred=events.iter().any(|event|
                                        matches!(event.op,Access::Move|Access::Drop) &&
                                            event.path.ancestor_of(&actual.path));
                                    if !transferred && !initialized(&state,&actual.path){
                                        return None;
                                    }
                                    apply_exact_effect(&mut state,&actual,events,&self.loans,&parents)?;
                                }
                                if let Some(mapped)=map_applied(&actual,token_count,formals.len()){
                                    record(&mut state,mapped)?;
                                }
                            }
                            next.push(state);
                        }else{
                            for case in path_cases {
                                let mut variant=state.clone();
                                for effect in &case.effects {
                                    let actual=resolve_effect(effect,events,&variant,&declarations,&parents)?;
                                    apply_exact_effect(&mut variant,&actual,events,&self.loans,&parents)?;
                                    if let Some(mapped)=map_applied(&actual,token_count,formals.len()){
                                        record(&mut variant,mapped)?;
                                    }
                                }
                                //The callee's exact uninitialized paths cannot be accepted as a mere annotation Verify that this case
                                //actually consumed each one before publishing a certificate
                                for path in &case.uninitialized {
                                    if initialized(&variant,path){return None;}
                                }
                                next.push(variant);
                                if next.len()>MAX_CASES{return None;}
                            }
                        }
                        continue;
                    }
                    for event in statement.events() {
                        //The latter may legitimately write through a live &mut capability and is checked by the independent
                        //ordered-call proof
                        if event.op==Access::Write && event.loan.is_none() &&
                            state.live_loans.iter().any(|loan|
                                self.loans.get(loan).is_none_or(|referent|
                                    referent.overlaps(&event.path))) {
                            return None;
                        }
                        apply_ownership(&mut state,event,&self.loans,&parents)?;
                        if let Some(effect)=map_event(event,token_count,formals.len()){
                            record(&mut state,effect)?;
                        }
                    }
                    next.push(state);
                }
                if let Some(dead)=nll.after.get(&(block_index,position+1)) {
                    for state in &mut next {
                        for id in dead {
                            if state.live_loans.contains(id) {
                                apply_ownership(state,&Event{op:Access::EndLoan,
                                    path:self.loans.get(id)?.clone(),loan:Some(*id),
                                    parent:None,token:0},&self.loans,&parents)?;
                            }
                        }
                    }
                }
                states=next;
                if states.len()>MAX_CASES{return None;}
            }
            for state in states {
                match &block.terminator {
                    Terminator::Return=>{
                        let returned=if origins.is_empty(){None}else{
                            let index=if origins.len()==1{0}else{state.selected?};
                            let origin=origins.get(index)?;
                            let loan=state.returned_loan?;
                            if !live_chain(&state,loan,&parents){return None;}
                            if origin.parameter>=formals.len(){return None;}
                            let owner=token_count.checked_add(1)?
                                .checked_add(origin.parameter)?;
                            let owner=SymbolId(u32::try_from(owner).ok()?);
                            let referent=Path{owner,fields:origin.fields.clone()};
                            //The selected reference must still refer to a initialized MovePath at the actual return, not merely
                            //when its predecessor created it
                            if !initialized(&state,&referent){return None;}
                            Some(index)
                        };
                        let mut uninitialized=Vec::new();
                        for path in &state.uninit {
                            let Some(parameter)=(path.owner.0 as usize)
                                .checked_sub(token_count.saturating_add(1)) else{continue};
                            if parameter>=formals.len(){continue;}
                            let proof=VerifiedParameterPath{parameter,fields:path.fields.clone()};
                            if !uninitialized.contains(&proof){uninitialized.push(proof);}
                        }
                        uninitialized.sort_by(|a,b|a.parameter.cmp(&b.parameter)
                            .then_with(||a.fields.iter().map(|k|(k.aggregate.0,k.field.0))
                                .cmp(b.fields.iter().map(|k|(k.aggregate.0,k.field.0)))));
                        let case=VerifiedPathCase{effects:state.effects,returned,uninitialized};
                        if !results.contains(&case){results.push(case);}
                        if results.len()>MAX_CASES{return None;}
                    }
                    Terminator::Goto(next)=>{
                        if next.is_empty(){return None;}
                        for &id in next {
                            if id>=self.blocks.len(){return None;}
                            let mut successor=state.clone();
                            //This is an edge-local EndLoan: it must never terminate a loan on another CFG successor
                            if let Some(dead)=nll.edges.get(&(state.node,id)) {
                                for loan in dead {
                                    if successor.live_loans.contains(loan) {
                                        apply_ownership(&mut successor,&Event{
                                            op:Access::EndLoan,
                                            path:self.loans.get(loan)?.clone(),
                                            loan:Some(*loan),parent:None,token:0,
                                        },&self.loans,&parents)?;
                                    }
                                }
                            }
                            successor.prev=Some(state.node);
                            successor.node=id;
                            pending.push_back(successor);
                            if pending.len()+seen.len()>MAX_STATES{return None;}
                        }
                    }
                }
            }
        }
        (!results.is_empty()).then_some(results)
    }
}

#[cfg_attr(not(test), allow(dead_code))]
pub fn lower<'a>(tokens:&'a [Token<'a>],range:Range<usize>,params:&[(String,ConstType)],schema:&Schema<'_>)
    ->Result<Option<FunctionMir>,String>{
    lower_with_copy_bounds(tokens,range,params,schema,&[])
}
#[cfg_attr(not(test), allow(dead_code))]
pub fn lower_with_copy_bounds<'a>(tokens:&'a [Token<'a>],range:Range<usize>,
    params:&[(String,ConstType)],schema:&Schema<'_>,copy_bounds:&[String])
    ->Result<Option<FunctionMir>,String>{
    let no_verified_calls=HashMap::new();
    lower_with_verified_calls(tokens,range,params,schema,copy_bounds,&no_verified_calls)
}
//Only trusted, already-checked bodies can be summarized at a call site A missing or recursively
//unproven callee never receives a MIR certificate
pub fn lower_with_verified_calls<'a>(tokens:&'a [Token<'a>],range:Range<usize>,
    params:&[(String,ConstType)],schema:&Schema<'_>,copy_bounds:&[String],
    verified_calls:&HashMap<String,VerifiedCallSummary>)->Result<Option<FunctionMir>,String>{
    let mut scope=HashMap::new();
    for (i,(name,ty)) in params.iter().enumerate(){
        let id=SymbolId(u32::try_from(tokens.len()+i+1).map_err(|_|"too many tokens")?);
        scope.insert(name.clone(),Binding{id,ty:ty.clone(),reference:None,
            loan:None,borrow_parent:None,alternatives:Vec::new(),phi_generation:None,mutable:false});
    }
    let start=u32::try_from(tokens.len()+params.len()+128).map_err(|_|"too many tokens")?;
    Builder{tokens,schema,verified_calls,blocks:Vec::new(),scopes:vec![scope],loans:HashMap::new(),
        next_temp:start,unsupported:false,nested_call_depth:0,
        copy_generics:copy_bounds.iter().cloned().collect(),failure:None}.lower(range)
}

#[cfg(test)]mod tests {
    use super::*;
    fn check(src:&str)->Option<Vec<cfg_borrow::Conflict>>{
        let tokens=crate::syntax::lex(src).unwrap();let range=0..tokens.len();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();let methods=HashMap::new();
        let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        lower(&tokens,range,&[],&schema).unwrap().map(|mir|mir.verify().unwrap())
    }
    #[test]fn all_if_arms_are_in_mir(){
        let mir=check("let mut x:i64=1; if true {x=2;} else {x=3;} let n:i64=x;").unwrap();
        assert!(mir.is_empty());
    }
    #[test]fn normal_local_borrow_is_checked(){
        assert!(check("let x:i64=1; let r=&x; let y:i64=x;").unwrap().is_empty());
    }
    #[test]fn method_call_has_explicit_two_phase_receiver(){
        let src="let mut p:Pair=Pair { value:1 }; p.set(p.value);";
        let tokens=crate::syntax::lex(src).unwrap();
        let mut types=HashMap::new();types.insert("Pair".into(),vec![("value".into(),ConstType::I64)]);
        let mut ids=HashMap::new();ids.insert("Pair".into(),TypeId(0));
        let names=vec!["Pair".into()];
        let mut methods=HashMap::new();methods.insert((TypeId(0),"set".into()),(true,2,ConstType::Unit));
        let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let mir=lower(&tokens,0..tokens.len(),&[],&schema).unwrap().unwrap();
        assert!(mir.blocks.iter().any(|b|b.statements.iter().any(|s|matches!(s,Statement::Call{..}))));
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]fn untaken_arm_keeps_a_live_reference_protected(){
        let errors=check("let mut x:i64=1; let r=&x; if true {let a:i64=*r;} else {x=3;} let b:i64=*r;").unwrap();
        assert!(!errors.is_empty(),"the unselected arm must still be checked");
    }
    #[test]fn nll_ends_unused_borrow_before_write(){
        assert!(check("let mut x:i64=1; let r=&x; x=3;").unwrap().is_empty());
    }
    #[test]fn unknown_operation_is_not_certified(){
        assert!(check("unknown_magic(x);").is_none());
    }
    #[test]fn match_has_all_arm_successors(){
        assert!(check("let mut x:i64=1;match true{true=>{x=2;},false=>{x=3;}}let z:i64=x;").unwrap().is_empty());
    }
    #[test]fn shared_reference_copy_preserves_both_loans(){
        let result=check("let x:i64=1; let r=&x; let s=r; let a:i64=*r; let b:i64=*s;").unwrap();
        assert!(result.is_empty(),"{result:?}");
    }
    #[test]fn mutable_reborrow_preserves_provenance(){
        let result=check("let mut x:i64=1; let r=&mut x; let s=&mut *r; *s;").unwrap();
        assert!(result.is_empty(),"{result:?}");
    }
    #[test]fn shared_ref_cannot_create_exclusive_reborrow(){
        assert!(check("let x:i64=1; let r=&x; let s=&mut *r;").is_none());
    }
    #[test]fn local_storage_live_and_dead_are_emitted(){
        let src="let x:i64=1; { let y:i64=x; }";
        let tokens=crate::syntax::lex(src).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();let methods=HashMap::new();
        let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let mir=lower(&tokens,0..tokens.len(),&[],&schema).unwrap().unwrap();
        let events=mir.blocks.iter().flat_map(|b|b.statements.iter()).flat_map(Statement::events)
            .map(|e|e.op).collect::<Vec<_>>();
        assert!(events.contains(&Access::StorageLive));
        assert!(events.contains(&Access::StorageDead));
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]fn destructuring_moves_independent_noncopy_fields(){
        let src="let p:Pair=Pair{left:Boxed{v:1},right:Boxed{v:2}}; let Pair{left,right}=p;";
        let tokens=crate::syntax::lex(src).unwrap();
        let mut types=HashMap::new();
        types.insert("Boxed".to_owned(),vec![("v".to_owned(),ConstType::I64)]);
        types.insert("Pair".to_owned(),vec![("left".to_owned(),ConstType::Named("Boxed".into())),
            ("right".to_owned(),ConstType::Named("Boxed".into()))]);
        let mut ids=HashMap::new();ids.insert("Pair".into(),TypeId(0));ids.insert("Boxed".into(),TypeId(1));
        let names=vec!["Pair".into(),"Boxed".into()];let methods=HashMap::new();
        let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let mir=lower(&tokens,0..tokens.len(),&[],&schema).unwrap().unwrap();
        let moves=mir.blocks.iter().flat_map(|b|b.statements.iter()).flat_map(Statement::events)
            .filter(|e|e.op==Access::Move).count();
        assert_eq!(moves,2);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]fn return_unwinds_live_local_storage(){
        let src="let x:i64=1; {let y:i64=x;return;}";
        let tokens=crate::syntax::lex(src).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();let methods=HashMap::new();
        let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let mir=lower(&tokens,0..tokens.len(),&[],&schema).unwrap().unwrap();
        let drops=mir.blocks.iter().flat_map(|b|b.statements.iter()).flat_map(Statement::events)
            .filter(|e|e.op==Access::StorageDead).count();
        assert_eq!(drops,2);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]fn host_loan_blocks_conflicting_quantum_access(){
        let path=Path::root(SymbolId(77));
        let loan=SymbolId(100);
        let mir=FunctionMir{entry:0,loans:HashMap::from([(loan,path.clone())]),blocks:vec![
            BasicBlock{terminator:Terminator::Return,statements:vec![
                Statement::HostOperation{name:"host shared borrow".into(),events:vec![
                    Event{op:Access::BorrowShared,path:path.clone(),loan:Some(loan),parent:None,token:0}]},
                Statement::QuantumOperation{name:"quantum write".into(),events:vec![
                    Event{op:Access::Write,path:path.clone(),loan:None,parent:None,token:1}]},
            ]},
        ]};
        assert!(mir.verify().unwrap().iter().any(|e|e.message.contains("loan conflict")));
    }
    #[test]fn trusted_host_and_quantum_effects_share_one_cfg_checker(){
        let src="let mut q:i64=1; host_borrow(q); quantum_write(q);";
        let tokens=crate::syntax::lex(src).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();let methods=HashMap::new();
        let mut effects=HashMap::new();
        effects.insert("host_borrow".into(),(false,vec![Access::Read]));
        effects.insert("quantum_write".into(),(true,vec![Access::Write]));
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let mir=lower(&tokens,0..tokens.len(),&[],&schema).unwrap().unwrap();
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter())
            .any(|s|matches!(s,Statement::QuantumOperation{..})));
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter())
            .any(|s|matches!(s,Statement::HostOperation{..})));
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]fn explicit_drop_from_trusted_summary_invalidates_value(){
        let src="let x:i64=1; drop(x); let y:i64=x;";
        let tokens=crate::syntax::lex(src).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();let methods=HashMap::new();
        let mut effects=HashMap::new();effects.insert("drop".into(),(false,vec![Access::Drop]));
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let mir=lower(&tokens,0..tokens.len(),&[],&schema).unwrap().unwrap();
        assert!(!mir.verify().unwrap().is_empty());
    }
    #[test]fn unknown_quantum_operation_is_not_certified(){
        assert!(check("unverified_quantum_gate(q);").is_none());
    }
    #[test]fn while_and_for_generate_backedges(){
        assert!(check("let mut x:i64=1; while true {x=2;} let n:i64=x;").unwrap().is_empty());
        assert!(check("let mut x:i64=1; for i in 0..3 {x=2;} let n:i64=x;").unwrap().is_empty());
    }
}

#[cfg(test)]
mod typed_mir_generic_0619_tests {
    use super::*;
    fn generic(body:&str,copy:bool)->Vec<cfg_borrow::Conflict> {
        let tokens=crate::syntax::lex(body).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();let methods=HashMap::new();
        let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let copy_bounds=if copy {vec!["T".to_owned()]}else{Vec::new()};
        let mir=lower_with_copy_bounds(&tokens,0..tokens.len(),
            &[("value".into(),ConstType::Generic("T".into()))],
            &schema,&copy_bounds).unwrap().expect("complete MIR expected");
        mir.verify().unwrap()
    }
    #[test]fn tail_expression_is_a_move_not_an_ignored_suffix(){
        assert!(!generic("let first=value;value",false).is_empty());
    }
    #[test]fn copy_bound_is_honored_only_when_declared(){
        assert!(generic("let first=value;value",true).is_empty());
    }
    #[test]fn parenthesized_tail_is_still_checked(){
        assert!(!generic("let first=value;(value)",false).is_empty());
    }
}

#[cfg(test)]
mod mir_cfg_join_0620_tests {
    use super::*;
    fn mir(source:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(source).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
    }
    #[test]
    fn following_statements_join_all_else_if_paths(){
        let src="let x:i64=3; if true {let a:i64=x;} else if false {} let b:i64=x;";
        let checked=mir(src).expect("the complete conditional must be lowered");
        assert!(checked.verify().unwrap().is_empty());
        let last=checked.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).filter(|e|e.op==Access::Initialize).count();
        assert_eq!(last,3);
    }
    #[test]
    fn else_if_join_detects_move_on_first_arm(){
        let src="let item:Payload=Payload { }; if true {let a=item;} else if false {} let b=item;";
        let tokens=crate::syntax::lex(src).unwrap();
        let mut types=HashMap::new();types.insert("Payload".into(),Vec::new());
        let mut ids=HashMap::new();ids.insert("Payload".into(),TypeId(0));
        let names=vec!["Payload".into()];let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let checked=lower(&tokens,0..tokens.len(),&[],&schema).unwrap().unwrap();
        assert!(!checked.verify().unwrap().is_empty(),
            "the post-conditional move must be checked on the first arm");
    }
    #[test]
    fn else_if_join_detects_move_on_intermediate_arm(){
        let src="let item:Payload=Payload { }; if false {} else if true {let a=item;} else if false {} let b=item;";
        let tokens=crate::syntax::lex(src).unwrap();
        let mut types=HashMap::new();types.insert("Payload".into(),Vec::new());
        let mut ids=HashMap::new();ids.insert("Payload".into(),TypeId(0));
        let names=vec!["Payload".into()];let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let checked=lower(&tokens,0..tokens.len(),&[],&schema).unwrap().unwrap();
        assert!(!checked.verify().unwrap().is_empty());
    }
    #[test]
    fn while_break_reaches_explicit_loop_exit(){
        let checked=mir("let mut x:i64=0; while true {x=1;break;} let y:i64=x;")
            .expect("while/break must have a complete MIR");
        assert!(checked.verify().unwrap().is_empty());
        assert!(checked.blocks.iter().any(|block|
            matches!(&block.terminator,Terminator::Goto(targets) if targets.len()==2)),
            "while condition must retain its body and exit successors");
    }
    #[test]
    fn for_continue_preserves_loop_exit_and_next_statement(){
        let checked=mir("let mut sum:i64=0; for i in 0..3 {sum=i;continue;} let r:i64=sum;")
            .expect("for/continue must have a complete MIR");
        assert!(checked.verify().unwrap().is_empty());
        assert!(checked.blocks.iter().any(|block|
            matches!(&block.terminator,Terminator::Goto(targets) if targets.len()==2)),
            "for condition must retain its body and exit successors");
    }
    #[test]
    fn for_binding_is_initialized_when_body_reads_it(){
        let checked=mir("let mut sum:i64=0;for i in 0..3 {sum=i;} let result:i64=sum;")
            .expect("numeric loop must be represented");
        assert!(checked.verify().unwrap().is_empty());
    }
    #[test]
    fn for_binding_has_storage_start_init_and_end(){
        let checked=mir("for i in 0..2 {let seen:i64=i;}").unwrap();
        let operations=checked.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).map(|e|(e.op,e.token)).collect::<Vec<_>>();
        assert!(operations.contains(&(Access::StorageLive,1)));
        assert!(operations.contains(&(Access::Initialize,1)));
        assert!(operations.iter().any(|(op,_)|*op==Access::StorageDead));
        assert!(checked.verify().unwrap().is_empty());
    }
    #[test]
    fn if_condition_must_be_boolean(){
        assert!(mir("let x:i64=1; if x {let y:i64=2;}").is_none());
        assert!(mir("let x:bool=true; if x {let y:i64=2;}").is_some());
    }
}

#[cfg(test)]
mod mir_boolean_control_0620_tests {
    use super::*;
    #[test]
    fn non_boolean_while_condition_is_not_certified(){
        let tokens=crate::syntax::lex("let x:i64=2; while x {let y:i64=1;}").unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        assert!(lower(&tokens,0..tokens.len(),&[],&schema).unwrap().is_none());
    }
}

#[cfg(test)]
mod mir_memory_nll_0621_tests {
    use super::*;

    fn long_borrow_chain(write_at:usize)->FunctionMir {
        const N:usize=192;
        let path=Path::root(SymbolId(310));
        let loan=SymbolId(311);
        let mut blocks=(0..N).map(|i|BasicBlock{
            statements:Vec::new(),
            terminator:if i+1==N{Terminator::Return}else{Terminator::Goto(vec![i+1])},
        }).collect::<Vec<_>>();
        blocks[0].statements.push(Statement::Access(Event{
            op:Access::BorrowShared,path:path.clone(),loan:Some(loan),parent:None,token:0,
        }));
        blocks[150].statements.push(Statement::Access(Event{
            op:Access::Read,path:path.clone(),loan:Some(loan),parent:None,token:150,
        }));
        blocks[write_at].statements.push(Statement::Access(Event{
            op:Access::Write,path:path.clone(),loan:None,parent:None,token:write_at,
        }));
        FunctionMir{entry:0,loans:HashMap::from([(loan,path)]),blocks}
    }

    #[test]
    fn shared_nll_sets_keep_last_use_and_release_before_later_write(){
        let errors=long_borrow_chain(175).verify().unwrap();
        assert!(errors.is_empty(),"the last read must end the loan: {errors:?}");
    }

    #[test]
    fn shared_nll_sets_do_not_release_borrow_before_last_use(){
        let errors=long_borrow_chain(100).verify().unwrap();
        assert!(errors.iter().any(|c|c.token==100 && c.message.contains("loan conflict")),
            "early write must conflict with a still-live loan: {errors:?}");
    }
}

#[cfg(test)]
mod mir_sparse_nll_0622_tests {
    use super::*;

    #[test]
    fn large_mir_with_no_reference_events_needs_no_loan_sets() {
        let total=1024usize;
        let blocks=(0..total).map(|i|BasicBlock{
            statements:Vec::new(),
            terminator:if i+1==total {Terminator::Return}
                else {Terminator::Goto(vec![i+1])},
        }).collect();
        let program=FunctionMir{blocks,entry:0,loans:HashMap::new()};
        assert!(program.verify().unwrap().is_empty());
    }
}

#[cfg(test)]
mod mir_result_phi_0623_tests {
    use super::*;
    fn lower_source(src:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(src).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
    }
    fn generic(src:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(src).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[("value".into(),ConstType::Generic("T".into()))],
            &schema).unwrap()
    }
    #[test]
    fn scalar_if_value_has_two_arm_initializations_and_a_phi(){
        let mir=lower_source("let x:i64=if true {1}else{2}; let y:i64=x;").unwrap();
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::ValuePhi{ty,predecessors,..}=s {Some((ty,predecessors))}
            else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),1);
        assert_eq!(phis[0].0,&ConstType::I64);
        assert_eq!(phis[0].1.len(),2);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn nested_if_value_preserves_all_branches(){
        let mir=lower_source("let result=if true {3}else if false {4}else{5};let end=result;").unwrap();
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter(|s|matches!(s,Statement::ValuePhi{..})).count(),2);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn generic_move_in_if_result_cannot_be_reused(){
        let mir=generic("let result=if true {value}else{value};let again=value;").unwrap();
        assert!(mir.verify().unwrap().iter().any(|c|c.message.contains("moved")));
    }
    #[test]
    fn match_result_requires_exhaustive_paths(){
        let mir=lower_source("let x=match true{true=>{4},false=>{5}};let y=x;").unwrap();
        assert!(mir.verify().unwrap().is_empty());
        assert!(lower_source("let x=match 1{1=>{4}};").is_none());
        assert!(lower_source("let x=match 1{1=>{4},_=>{5}};").is_some());
    }
    #[test]
    fn non_uniform_results_rejected_while_distinct_references_are_checked(){
        assert!(lower_source("let x=if true{4}else{false};").is_none());
        assert!(lower_source("let x=if true{4};").is_none());
        let mir=lower_source("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let v=*r;").unwrap();
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter()).any(|s|
            matches!(s,Statement::ValuePhi{ty:ConstType::Ref(_),provenance:None,
                alternatives,..} if alternatives.len()==2 &&
                alternatives[0].loan!=alternatives[1].loan &&
                alternatives[0].path!=alternatives[1].path)));
        assert!(mir.verify().unwrap().is_empty());
    }
}

#[cfg(test)]
mod reference_phi_and_sparse_nll_0624_tests {
    use super::*;

    fn lower_source(src:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(src).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
    }

    #[test]
    fn shared_reference_phi_tracks_same_and_distinct_owners(){
        let mir=lower_source("let n:i64=7;let r=if true{&n}else{&n};let value=*r;").unwrap();
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter()).any(|s|
            matches!(s,Statement::ValuePhi{ty:ConstType::Ref(_),provenance:Some(_),..})));
        assert!(mir.verify().unwrap().is_empty());
        let distinct=lower_source("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let v=*r;").unwrap();
        assert!(distinct.blocks.iter().flat_map(|b|b.statements.iter()).any(|s|
            matches!(s,Statement::ValuePhi{ty:ConstType::Ref(_),provenance:None,
                alternatives,..} if alternatives.len()==2)));
        assert!(distinct.verify().unwrap().is_empty());
    }

    #[test]
    fn mutable_reference_phi_requires_identical_exclusive_origin(){
        let mir=lower_source("let mut n:i64=7;let r=if true{&mut n}else{&mut n};let v=*r;").unwrap();
        assert!(mir.verify().unwrap().is_empty());
        assert!(lower_source("let mut n:i64=7;let r=if true{&n}else{&mut n};").is_none());
    }

    #[test]
    fn matching_reference_phi_preserves_each_arm_source_loan(){
        let mir=lower_source("let n:i64=7;let r=match true{true=>{&n},false=>{&n}};let v=*r;").unwrap();
        assert!(mir.verify().unwrap().is_empty());
        let distinct=lower_source("let a:i64=1;let b:i64=2;let r=match true{true=>{&a},false=>{&b}};let v=*r;").unwrap();
        assert!(distinct.blocks.iter().flat_map(|b|b.statements.iter()).any(|s|
            matches!(s,Statement::ValuePhi{ty:ConstType::Ref(_),provenance:None,
                alternatives,..} if alternatives.len()==2 &&
                alternatives[0].loan!=alternatives[1].loan)));
        assert!(distinct.verify().unwrap().is_empty());
    }

    #[test]
    fn nested_reference_phis_keep_identical_provenance(){
        let mir=lower_source("let n:i64=5;let r=if true{&n}else if false{&n}else{&n};let v=*r;").unwrap();
        assert!(mir.verify().unwrap().is_empty());
    }

    #[test]
    fn phi_missing_or_duplicate_predecessors_is_rejected(){
        let baseline=lower_source("let x=if true{1}else{2};let y=x;").unwrap();
        let index=baseline.blocks.iter().position(|b|b.statements.iter().any(|s|
            matches!(s,Statement::ValuePhi{..}))).unwrap();
        let mut missing=baseline;
        for stmt in &mut missing.blocks[index].statements {
            if let Statement::ValuePhi{predecessors,..}=stmt {predecessors.pop();break;}
        }
        assert!(missing.verify().unwrap_err().contains("predecessors"));
        let mut duplicate=lower_source("let x=if true{1}else{2};let y=x;").unwrap();
        for stmt in &mut duplicate.blocks[index].statements {
            if let Statement::ValuePhi{predecessors,..}=stmt {
                predecessors.push(predecessors[0]);break;
            }
        }
        assert!(duplicate.verify().is_err());
    }

    #[test]
    fn blocks_without_loans_still_verify_moves(){
        let mir=lower_source("let x:i64=1;let y:i64=x;let z:i64=y;").unwrap();
        assert!(mir.verify().unwrap().is_empty());
    }
}

#[cfg(test)]
mod region_alternatives_0625_tests {
    use super::*;

    fn lower_source(src:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(src).unwrap();
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
    }
    #[test]
    fn alternative_shared_referents_are_valid_after_if_join(){
        let mir=lower_source("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let v=*r;").unwrap();
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter()).any(|s|
            matches!(s,Statement::ValuePhi{ty:ConstType::Ref(_),provenance:None,
                alternatives,..} if alternatives.len()==2)));
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn alternative_mutable_loans_allow_a_read_of_the_selected_referent(){
        let mir=lower_source("let mut a:i64=1;let mut b:i64=2;let r=if true{&mut a}else{&mut b};let v=*r;").unwrap();
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn alternative_referents_work_in_exhaustive_match(){
        let mir=lower_source("let a:i64=1;let b:i64=2;let r=match true{true=>{&a},false=>{&b}};let v=*r;").unwrap();
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn nested_alternatives_remain_branch_specific(){
        let mir=lower_source("let a:i64=1;let b:i64=2;let c:i64=3;let r=if true{&a}else if false{&b}else{&c};let v=*r;").unwrap();
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn a_write_that_might_violate_one_branch_is_not_approved(){
        let mir=lower_source("let mut a:i64=1;let b:i64=2;let r=if true{&a}else{&b};a=3;let v=*r;").unwrap();
        assert!(!mir.verify().unwrap().is_empty());
    }
    #[test]
    fn reference_phi_alternatives_are_checked_against_real_loans(){
        let mut mir=lower_source("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let v=*r;").unwrap();
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()) {
            if let Statement::ValuePhi{alternatives,..}=stmt {
                alternatives.pop();break;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn phi_rejects_forged_loan_path_even_when_both_referents_are_live(){
        let mut mir=lower_source("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let v=*r;").unwrap();
        for statement in mir.blocks.iter_mut().flat_map(|block|block.statements.iter_mut()) {
            if let Statement::ValuePhi{alternatives,..}=statement {
                let forged=alternatives[0].path.clone();
                alternatives[1].path=forged;
                break;
            }
        }
        assert!(mir.verify().is_err(),"a forged provenance must fail MIR verification");
    }
    #[test]
    fn phi_rejects_forged_mutability_in_one_branch(){
        let mut mir=lower_source("let mut a:i64=1;let mut b:i64=2;let r=if true{&mut a}else{&mut b};let v=*r;").unwrap();
        for statement in mir.blocks.iter_mut().flat_map(|block|block.statements.iter_mut()) {
            if let Statement::ValuePhi{alternatives,..}=statement {
                alternatives[0].exclusive=false;
                break;
            }
        }
        assert!(mir.verify().is_err(),"a shared loan cannot impersonate &mut");
    }
    #[test]
    fn alternative_mutable_phi_does_not_erase_conflicting_writes(){
        let mir=lower_source("let mut a:i64=1;let mut b:i64=2;let r=if true{&mut a}else{&mut b};a=4;let v=*r;").unwrap();
        assert!(!mir.verify().unwrap().is_empty(),
            "write to a possibly mutably borrowed referent must be rejected");
    }
    #[test]
    fn reference_phi_reborrow_is_not_guessed_from_multiple_origins(){
        assert!(lower_source("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let s=&*r;").is_none());
    }
}

#[cfg(test)]
mod mutable_reference_rebinding_0632_tests {
    use super::*;

    fn lower_source(source:&str)->Result<Option<FunctionMir>,String> {
        let tokens=crate::syntax::lex(source).expect("test source must tokenize");
        let types=HashMap::new();
        let ids=HashMap::new();
        let names=Vec::new();
        let methods=HashMap::new();
        let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema)
    }
    fn verify(source:&str)->Vec<cfg_borrow::Conflict>{
        lower_source(source).expect("MIR builder failed")
            .expect("a supported reference expression was not lowered")
            .verify().expect("borrow graph invariant failed")
    }

    #[test]
    fn mutable_reference_rebinding_uses_a_new_loan_identity() {
        let mir=lower_source("let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;r=&mut b;*r=7;")
            .unwrap().expect("rebind must be lowered");
        let mut loans=HashSet::new();
        for event in mir.blocks.iter().flat_map(|block|block.statements.iter())
            .flat_map(Statement::events) {
            if event.op==Access::BorrowMut {loans.insert(event.loan.unwrap());}
        }
        assert_eq!(loans.len(),2,"a retargeted borrow must never reuse its old ID");
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn old_referent_is_writable_after_rebinding() {
        assert!(verify("let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;r=&mut b;a=7;*r=8;").is_empty());
    }
    #[test]
    fn mutable_alias_move_consumes_the_old_binding() {
        assert!(!verify("let mut a:i64=1;let r=&mut a;let next=r;*r=3;*next=4;").is_empty());
    }
    #[test]
    fn mutable_alias_move_preserves_the_parent_loan() {
        assert!(verify("let mut a:i64=1;let r=&mut a;let child=&mut *r;let moved=child;*moved=5;").is_empty());
    }
    #[test]
    fn live_grandchild_suspends_both_mutable_ancestors() {
        assert!(!verify("let mut a:i64=1;let r=&mut a;let child=&mut *r;let grand=&mut *child;*r=5;let value=*grand;").is_empty());
    }
    #[test]
    fn existing_shared_loan_blocks_rebinding_to_the_same_owner() {
        let diagnostics=verify("let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;let shared=&b;r=&mut b;let value=*shared;");
        assert!(!diagnostics.is_empty(),"rebind must not bypass a live shared loan");
    }
    #[test]
    fn last_use_of_child_allows_parent_write() {
        assert!(verify("let mut a:i64=1;let r=&mut a;let child=&mut *r;let value=*child;*r=6;").is_empty());
    }
    #[test]
    fn live_child_blocks_parent_rebinding() {
        assert!(!verify("let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;let child=&mut *r;r=&mut b;let value=*child;").is_empty());
    }
    #[test]
    fn dead_child_allows_parent_rebinding() {
        assert!(verify("let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;let child=&mut *r;let value=*child;r=&mut b;*r=8;").is_empty());
    }
    #[test]
    fn reassignment_reinitializes_a_moved_mutable_binding() {
        assert!(verify("let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;let moved=r;r=&mut b;*moved=9;*r=8;").is_empty());
    }
    #[test]
    fn branch_specific_rebinding_cannot_invent_uniform_provenance() {
        let result=lower_source("let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;if true{r=&mut b;}*r=7;");
        assert!(result.is_err(),"reassignment through one arm requires a provenance PHI");
    }
    #[test]
    fn reborrowing_a_shared_reference_as_mutable_is_not_certified() {
        assert!(lower_source("let mut a:i64=1;let r=&a;let child=&mut *r;").unwrap().is_none());
    }
}


#[cfg(test)]
mod mutable_branch_phi_0633_tests {
    use super::*;

    fn lower_source(src:&str)->Result<Option<FunctionMir>,String>{
        let tokens=crate::syntax::lex(src).expect("test input must lex");
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema)
    }
    fn check(src:&str)->Vec<cfg_borrow::Conflict>{
        lower_source(src).expect("supported MIR syntax").expect("full MIR")
            .verify().expect("valid graph and identities")
    }
    const PREFIX:&str="let mut a:i64=1;let mut b:i64=2;let mut c:i64=3;let mut r=&mut a;";

    #[test]
    fn both_if_arms_rebind_existing_mutable_reference_through_distinct_loans(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}*r=4;");
        let mir=lower_source(&src).unwrap().unwrap();
        assert!(mir.verify().unwrap().is_empty());
        let groups=mir.blocks.iter().flat_map(|b|&b.statements).filter_map(|stmt|{
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=stmt {
                Some(alternatives)
            }else{None}
        }).collect::<Vec<_>>();
        assert_eq!(groups.len(),1);
        assert_eq!(groups[0].len(),2);
        assert_ne!(groups[0][0].loan,groups[0][1].loan);
        assert_ne!(groups[0][0].path,groups[0][1].path);
    }
    #[test]
    fn branch_rebind_preserves_original_owner_after_retirement(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}a=9;*r=7;");
        assert!(check(&src).is_empty());
    }
    #[test]
    fn overlapping_writes_to_a_possible_referent_remain_conflicts(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}b=9;*r=7;");
        assert!(!check(&src).is_empty());
    }
    #[test]
    fn shared_borrow_of_one_possible_referent_blocks_phi_write(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}let shared=&b;*r=7;let v=*shared;");
        assert!(!check(&src).is_empty());
    }
    #[test]
    fn phi_write_requires_exact_mutable_alternatives(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}*r=7;");
        let mut mir=lower_source(&src).unwrap().unwrap();
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()){
            if let Statement::ValuePhi{alternatives,..}=stmt {
                alternatives[0].exclusive=false;
                break;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn live_child_of_previous_loan_blocks_branch_rebinding(){
        let src=format!("{PREFIX}let child=&mut *r;if true{{r=&mut b;}}else{{r=&mut c;}}let v=*child;");
        assert!(!check(&src).is_empty(),"old parent cannot end while child lives");
    }
    #[test]
    fn ended_child_allows_branch_rebinding(){
        let src=format!("{PREFIX}let child=&mut *r;let v=*child;if true{{r=&mut b;}}else{{r=&mut c;}}*r=8;");
        assert!(check(&src).is_empty(),"NLL must release an unused child");
    }
    #[test]
    fn missing_else_does_not_certify_reassignment(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}*r=7;");
        assert!(lower_source(&src).is_err());
    }
    #[test]
    fn mismatched_reassignment_targets_do_not_become_one_phi(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{a=&mut c;}}*r=7;");
        assert!(lower_source(&src).is_err());
    }
    #[test]
    fn merged_reference_can_be_reassigned_after_retiring_alternative_loans(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}r=&mut a;*r=7;");
        let mir=lower_source(&src).unwrap().unwrap();
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn immediate_child_reborrow_of_phi_is_certified_with_exact_parents(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}let child=&mut *r;*child=1;");
        assert!(check(&src).is_empty());
    }
    #[test]
    fn loan_provenance_path_tampering_is_rejected(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}*r=7;");
        let mut mir=lower_source(&src).unwrap().unwrap();
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()){
            if let Statement::ValuePhi{alternatives,..}=stmt {
                let forged=alternatives[0].path.clone();
                alternatives[1].path=forged;
                break;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn loan_alternatives_cannot_have_duplicate_ids(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}*r=7;");
        let mut mir=lower_source(&src).unwrap().unwrap();
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()){
            if let Statement::ValuePhi{alternatives,..}=stmt {
                let forged=alternatives[0].loan;
                alternatives[1].loan=forged;
                break;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn completing_only_one_cfg_predecessor_cannot_certify_phi(){
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}*r=7;");
        let mut mir=lower_source(&src).unwrap().unwrap();
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()){
            if let Statement::ValuePhi{predecessors,..}=stmt {
                predecessors.pop();break;
            }
        }
        assert!(mir.verify().is_err());
    }
}

#[cfg(test)]
mod mutable_match_reborrow_phi_0634_tests {
    use super::*;
    fn lower_source(src:&str)->Result<Option<FunctionMir>,String> {
        let tokens=crate::syntax::lex(src).expect("valid test tokens");
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema)
    }
    fn errors(src:&str)->Vec<cfg_borrow::Conflict> {
        lower_source(src).expect("MIR lowering").expect("complete MIR")
            .verify().expect("consistent loan and PHI metadata")
    }
    const PREFIX:&str="let mut a:i64=1;let mut b:i64=2;let mut c:i64=3;let mut r=&mut a;";

    #[test]
    fn exhaustive_bool_match_reassigns_distinct_exclusive_loans() {
        let src=format!("{PREFIX}match true{{true=>{{r=&mut b;}},false=>{{r=&mut c;}}}}*r=12;");
        let mir=lower_source(&src).unwrap().unwrap();
        assert!(mir.verify().unwrap().is_empty());
        let groups=mir.blocks.iter().flat_map(|block|&block.statements).filter_map(|stmt|{
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=stmt {
                Some(alternatives)
            } else {None}
        }).collect::<Vec<_>>();
        assert_eq!(groups.len(),1);
        assert_eq!(groups[0].len(),2);
        assert_ne!(groups[0][0].loan,groups[0][1].loan);
        assert_ne!(groups[0][0].path,groups[0][1].path);
    }
    #[test]
    fn reversed_match_arm_order_retains_exhaustive_phi() {
        let src=format!("{PREFIX}match false{{false=>{{r=&mut c;}},true=>{{r=&mut b;}}}}*r=8;");
        assert!(errors(&src).is_empty());
    }
    #[test]
    fn nested_reborrows_preserve_branch_specific_parent_loans() {
        let src=format!("{PREFIX}let ra=&mut b;let rb=&mut c;\
            match true{{true=>{{r=&mut *ra;}},false=>{{r=&mut *rb;}}}}*r=7;");
        let mir=lower_source(&src).unwrap().unwrap();
        let options=mir.blocks.iter().flat_map(|block|&block.statements).find_map(|stmt|{
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=stmt {
                Some(alternatives)
            }else{None}
        }).unwrap();
        assert!(options.iter().all(|option|option.parent.is_some()));
        assert_ne!(options[0].parent,options[1].parent);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn if_branch_reborrows_keep_independent_parents() {
        let src=format!("{PREFIX}let ra=&mut b;let rb=&mut c;\
            if true{{r=&mut *ra;}}else{{r=&mut *rb;}}*r=7;");
        assert!(errors(&src).is_empty());
    }
    #[test]
    fn already_live_child_prevents_retirement_in_match() {
        let src=format!("{PREFIX}let child=&mut *r;\
            match true{{true=>{{r=&mut b;}},false=>{{r=&mut c;}}}}let n=*child;");
        assert!(!errors(&src).is_empty());
    }
    #[test]
    fn old_child_last_used_before_match_does_not_block_rebinding() {
        let src=format!("{PREFIX}let child=&mut *r;let n=*child;\
            match true{{true=>{{r=&mut b;}},false=>{{r=&mut c;}}}}*r=7;");
        assert!(errors(&src).is_empty());
    }
    #[test]
    fn conflicting_write_after_match_still_rejected() {
        let src=format!("{PREFIX}match true{{true=>{{r=&mut b;}},false=>{{r=&mut c;}}}}b=19;*r=7;");
        assert!(!errors(&src).is_empty());
    }
    #[test]
    fn match_requires_two_unique_exhaustive_bool_arms() {
        let partial=format!("{PREFIX}match true{{true=>{{r=&mut b;}}}}*r=7;");
        let duplicate=format!("{PREFIX}match true{{true=>{{r=&mut b;}},true=>{{r=&mut c;}}}}*r=7;");
        for src in [partial,duplicate] {
            assert!(!matches!(lower_source(&src),Ok(Some(ref mir)) if mir.verify().is_ok_and(|e|e.is_empty())));
        }
    }
    #[test]
    fn tampered_branch_parent_is_not_verified() {
        let src=format!("{PREFIX}let ra=&mut b;let rb=&mut c;\
            match true{{true=>{{r=&mut *ra;}},false=>{{r=&mut *rb;}}}}*r=7;");
        let mut mir=lower_source(&src).unwrap().unwrap();
        for stmt in mir.blocks.iter_mut().flat_map(|block|block.statements.iter_mut()) {
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=stmt {
                alternatives[1].parent=alternatives[0].parent;
                break;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn match_phi_reborrow_proves_all_branch_specific_parents() {
        let src=format!("{PREFIX}match true{{true=>{{r=&mut b;}},false=>{{r=&mut c;}}}}\
            let child=&mut *r;*child=7;");
        assert!(errors(&src).is_empty());
    }
}

#[cfg(test)]
mod immediate_mutable_phi_reborrow_0635_tests {
    use super::*;
    fn lower_source(src:&str)->Result<Option<FunctionMir>,String>{
        let tokens=crate::syntax::lex(src).expect("valid test tokens");
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema)
    }
    fn conflicts(src:&str)->Vec<cfg_borrow::Conflict>{
        lower_source(src).expect("MIR lowering").expect("complete MIR")
            .verify().expect("structurally valid MIR")
    }
    const PREFIX:&str="let mut a:i64=1;let mut b:i64=2;let mut c:i64=3;let mut r=&mut a;";

    #[test]
    fn if_phi_can_be_mutably_reborrowed_by_exact_branch_loan(){
        let source=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}let child=&mut *r;*child=8;");
        let mir=lower_source(&source).unwrap().unwrap();
        assert!(mir.verify().unwrap().is_empty());
        let refs=mir.blocks.iter().flat_map(|b|&b.statements).filter_map(|s|
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=s {
                Some(alternatives)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(refs.len(),2);
        assert_eq!(refs[0].len(),refs[1].len());
        for (old,new) in refs[0].iter().zip(refs[1].iter()) {
            assert_eq!(new.parent,Some(old.loan));
            assert_eq!(new.path,old.path);
            assert_ne!(new.loan,old.loan);
        }
    }
    #[test]
    fn match_phi_can_be_mutably_reborrowed(){
        let source=format!("{PREFIX}match false{{false=>{{r=&mut c;}},true=>{{r=&mut b;}}}}let child=&mut *r;*child=6;");
        assert!(conflicts(&source).is_empty());
    }
    #[test]
    fn two_nested_reborrows_preserve_each_parent_chain(){
        let source=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}let child=&mut *r;let grand=&mut *child;*grand=5;");
        let mir=lower_source(&source).unwrap().unwrap();
        let phis=mir.blocks.iter().flat_map(|b|&b.statements).filter_map(|s|
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=s {
                Some(alternatives)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),3);
        for pair in phis.windows(2){
            for (older,child) in pair[0].iter().zip(pair[1].iter()){
                assert_eq!(child.parent,Some(older.loan));
            }
        }
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn cannot_use_phi_parent_while_nested_mutable_child_is_live(){
        let source=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}let child=&mut *r;*r=8;*child=5;");
        assert!(!conflicts(&source).is_empty());
    }
    #[test]
    fn after_last_child_use_parent_can_be_used_again(){
        let source=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}let child=&mut *r;*child=5;*r=8;");
        assert!(conflicts(&source).is_empty());
    }
    #[test]
    fn forged_child_parent_loan_is_detected(){
        let source=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}let child=&mut *r;*child=5;");
        let mut mir=lower_source(&source).unwrap().unwrap();
        let mut tampered=false;
        for block in &mut mir.blocks {
            for statement in &mut block.statements {
                if let Statement::Access(event)=statement {
                    if event.op==Access::BorrowMut && event.parent.is_some() {
                        event.parent=Some(SymbolId(u32::MAX));tampered=true;break;
                    }
                }
            }
            if tampered{break;}
        }
        assert!(tampered);
        let result=mir.verify();
        assert!(match result {Err(_)=>true,Ok(errors)=>!errors.is_empty()});
    }
    #[test]
    fn missing_child_candidate_cannot_be_certified(){
        let source=format!("{PREFIX}match true{{true=>{{r=&mut b;}},false=>{{r=&mut c;}}}}let child=&mut *r;*child=5;");
        let mut mir=lower_source(&source).unwrap().unwrap();
        let mut found=0;
        for statement in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()){
            if let Statement::ValuePhi{alternatives,..}=statement {
                found+=1;
                if found==2 {alternatives.pop();break;}
            }
        }
        assert_eq!(found,2);
        assert!(mir.verify().is_err());
    }
    #[test]
    fn intervening_effect_must_not_hoist_a_phi_reborrow(){
        let source=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}*r=3;let child=&mut *r;*child=5;");
        let mir=lower_source(&source).unwrap()
            .expect("a verified late PHI reborrow must retain the intervening effect");
        let (bind_node,source_generation,children)=mir.blocks.iter().enumerate()
            .find_map(|(node,block)|block.statements.iter().find_map(|statement|{
                if let Statement::LatePhiReborrow{source_generation,children,..}=statement {
                    Some((node,*source_generation,children.clone()))
                }else{None}
            })).expect("a late reborrow must not be rewritten as an immediate edge borrow");
        assert_eq!(children.len(),2);
        let source_options=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .find_map(|statement|if let Statement::ValuePhi{
                generation:Some(generation),alternatives,..}=statement {
                (*generation==source_generation).then_some(alternatives)
            }else{None}).expect("the parent PHI generation must be proven");
        assert_eq!(source_options.len(),children.len());
        for (source,child) in source_options.iter().zip(&children) {
            assert_eq!(child.parent,Some(source.loan));
            assert_eq!(child.path,source.path);
            assert_ne!(child.loan,source.loan);
        }
        let writes=mir.blocks.iter().enumerate().filter_map(|(node,block)|{
            block.statements.iter().flat_map(Statement::events).any(|event|
                event.op==Access::Write && event.loan==Some(source_generation))
                .then_some(node)
        }).collect::<Vec<_>>();
        assert_eq!(writes.len(),1,"the intervening source-PHI write must be retained exactly once");
        let write_node=writes[0];
        assert_ne!(write_node,bind_node,"the late borrow must occur after the write");
        let mut pending=vec![mir.entry];
        let mut reachable=HashSet::new();
        while let Some(node)=pending.pop(){
            if !reachable.insert(node){continue;}
            if let Terminator::Goto(successors)=&mir.blocks[node].terminator {
                pending.extend(successors.iter().copied());
            }
        }
        assert!(reachable.contains(&write_node) && reachable.contains(&bind_node),
            "both the intervening write and late reborrow must be reachable");
        let mut stack=vec![mir.entry];
        let mut reached=HashSet::new();
        while let Some(node)=stack.pop(){
            if node==write_node || !reached.insert(node){continue;}
            if let Terminator::Goto(successors)=&mir.blocks[node].terminator {
                stack.extend(successors.iter().copied());
            }
        }
        assert!(!reached.contains(&bind_node),
            "a path reached the child PHI reborrow without its preceding write");
        let errors=mir.verify().expect("valid late PHI proof with an intervening write");
        assert!(errors.is_empty(),"{errors:?}");
    }
    #[test]
    fn effect_after_late_phi_reborrow_cannot_use_suspended_parent(){
        let source=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}*r=3;let child=&mut *r;*r=4;*child=5;");
        match lower_source(&source).expect("MIR lowering") {
            None=>(), //Unsupported forms fail closed
            Some(mir)=>{
                let rejected=mir.verify().map_or(true,|conflicts|!conflicts.is_empty());
                assert!(rejected,"parent write after the late borrow must be rejected");
            }
        }
    }
}

#[cfg(test)]
mod mutable_region_phi_0636_tests {
    use super::*;

    fn lower_source(src:&str,struct_fields:bool)->Result<Option<FunctionMir>,String>{
        let tokens=crate::syntax::lex(src).expect("valid QRust test source");
        let mut types=HashMap::new();
        let mut ids=HashMap::new();
        let mut names=Vec::new();
        if struct_fields {
            types.insert("Point".to_owned(),vec![
                ("x".to_owned(),ConstType::I64),
                ("y".to_owned(),ConstType::I64),
            ]);
            ids.insert("Point".to_owned(),TypeId(0));
            names.push("Point".to_owned());
        }
        let methods=HashMap::new();
        let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema)
    }
    fn check(src:&str,fields:bool)->Result<Vec<cfg_borrow::Conflict>,String>{
        lower_source(src,fields)?.ok_or("incomplete MIR for test")?.verify()
    }
    const PREFIX:&str="let mut a:i64=1;let mut b:i64=2;let mut c:i64=3;let mut r=&mut a;";
    const STRUCTS:&str="let mut p=Point{x:1,y:2};let mut q=Point{x:3,y:4};let mut r=&mut p;";

    #[test]
    fn single_reassignment_after_phi_retires_all_alternatives() {
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}r=&mut a;*r=8;");
        assert!(check(&src,false).unwrap().is_empty());
    }
    #[test]
    fn second_phi_after_first_phi_keeps_distinct_loan_generations() {
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}\
            if false{{r=&mut a;}}else{{r=&mut b;}}*r=9;");
        let mir=lower_source(&src,false).unwrap().unwrap();
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=s{
                Some(alternatives)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),2);
        let ids=phis.iter().flat_map(|alternatives|alternatives.iter().map(|o|o.loan))
            .collect::<HashSet<_>>();
        assert_eq!(ids.len(),4);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn next_phi_cannot_end_live_child_of_previous_phi() {
        let src=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}\
            let child=&mut *r;*child=2;\
            if false{{r=&mut a;}}else{{r=&mut b;}}*child=3;");
        assert!(!matches!(check(&src,false),Ok(ref errors) if errors.is_empty()));
    }
    #[test]
    fn three_way_else_if_has_complete_phi_provenance() {
        let src=format!("{PREFIX}if true{{r=&mut a;}}else if false{{r=&mut b;}}else{{r=&mut c;}}*r=5;");
        let mir=lower_source(&src,false).unwrap().unwrap();
        let choices=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=s{
                Some(alternatives)
            }else{None}).unwrap();
        assert_eq!(choices.len(),3);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn four_way_else_if_checks_all_branches() {
        let src=format!("{PREFIX}if false{{r=&mut a;}}else if false{{r=&mut b;}}\
            else if true{{r=&mut c;}}else{{r=&mut a;}}*r=7;");
        assert!(check(&src,false).unwrap().is_empty());
    }
    #[test]
    fn else_if_without_final_else_cannot_certify_mutable_phi() {
        let src=format!("{PREFIX}if true{{r=&mut b;}}else if false{{r=&mut c;}}*r=5;");
        let result=lower_source(&src,false);
        if let Ok(Some(mir))=result {
            assert!(!mir.blocks.iter().flat_map(|b|&b.statements).any(|s|
                matches!(s,Statement::ValuePhi{alternatives,..} if alternatives.len()==3)));
        }
    }
    #[test]
    fn match_bool_wildcard_in_last_arm_carries_exact_loans(){
        let src=format!("{PREFIX}match true{{true=>{{r=&mut b;}},_=>{{r=&mut c;}}}}*r=7;");
        assert!(check(&src,false).unwrap().is_empty());
    }
    #[test]
    fn match_bool_wildcard_before_specific_arm_not_certified(){
        let src=format!("{PREFIX}match true{{_=>{{r=&mut b;}},false=>{{r=&mut c;}}}}*r=7;");
        assert!(!matches!(check(&src,false),Ok(ref errors) if errors.is_empty()));
    }
    #[test]
    fn field_projection_after_phi_retains_field_path_and_parent(){
        let src=format!("{STRUCTS}if true{{r=&mut q;}}else{{r=&mut p;}}\
            let field=&mut r.x;*field=11;");
        let mir=lower_source(&src,true).unwrap().unwrap();
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}=s{
                Some(alternatives)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),2);
        for (parent,child) in phis[0].iter().zip(phis[1].iter()) {
            assert_eq!(child.parent,Some(parent.loan));
            assert_eq!(child.path.fields.len(),parent.path.fields.len()+1);
            assert!(parent.path.ancestor_of(&child.path));
        }
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn nested_field_reborrow_preserves_parent_chain(){
        let src=format!("{STRUCTS}if true{{r=&mut q;}}else{{r=&mut p;}}\
            let field=&mut r.x;let second=&mut *field;*second=9;");
        assert!(check(&src,true).unwrap().is_empty());
    }
    #[test]
    fn field_child_blocks_parent_write_until_last_use(){
        let src=format!("{STRUCTS}if true{{r=&mut q;}}else{{r=&mut p;}}\
            let field=&mut r.x;*r=Point{{x:10,y:11}};*field=4;");
        assert!(!matches!(check(&src,true),Ok(ref errors) if errors.is_empty()));
    }
    #[test]
    fn wrong_field_id_in_projected_phi_is_rejected(){
        let src=format!("{STRUCTS}if true{{r=&mut q;}}else{{r=&mut p;}}\
            let field=&mut r.x;*field=1;");
        let mut mir=lower_source(&src,true).unwrap().unwrap();
        let mut index=0;
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()) {
            if let Statement::ValuePhi{alternatives,..}=stmt {
                index+=1;
                if index==2 {
                    alternatives[0].path.fields[0].field=FieldId(1);
                    break;
                }
            }
        }
        assert_eq!(index,2);
        assert!(mir.verify().is_err());
    }
}

#[cfg(test)]
mod temporal_phi_enum_0637_tests {
    use super::*;

    fn lower_source(source:&str)->Result<Option<FunctionMir>,String>{
        let tokens=crate::syntax::lex(source).expect("valid test tokens");
        let types=HashMap::new();
        let enums=HashMap::from([("Mode".to_owned(),
            vec!["A".to_owned(),"B".to_owned(),"C".to_owned()])]);
        let ids=HashMap::from([("Mode".to_owned(),TypeId(0))]);
        let names=vec!["Mode".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&enums,types:&types,type_ids:&ids,
            type_names:&names,methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema)
    }
    fn checked(source:&str)->Result<Vec<cfg_borrow::Conflict>,String>{
        lower_source(source)?.ok_or("test needs complete MIR")?.verify()
    }
    const PREFIX:&str="let mut a:i64=1;let mut b:i64=2;let mut c:i64=3;let mut r=&mut a;";
    const MODE:&str="let mode:Mode=Mode::B;";

    #[test]
    fn consecutive_phi_generations_are_separate_and_writable(){
        let code=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}\
            if false{{r=&mut a;}}else{{r=&mut b;}}*r=8;");
        let mir=lower_source(&code).unwrap().unwrap();
        let ids=mir.blocks.iter().flat_map(|b|&b.statements)
            .filter_map(|s|match s {
                Statement::ValuePhi{alternatives,generation,..} if !alternatives.is_empty()=>*generation,
                _=>None,
            }).collect::<Vec<_>>();
        assert_eq!(ids.len(),2);
        assert_ne!(ids[0],ids[1],"generations need independent provenance groups");
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn tampering_a_phi_generation_is_rejected(){
        let code=format!("{PREFIX}if true{{r=&mut b;}}else{{r=&mut c;}}\
            if false{{r=&mut a;}}else{{r=&mut b;}}*r=8;");
        let mut mir=lower_source(&code).unwrap().unwrap();
        let mut first=None;
        for s in mir.blocks.iter_mut().flat_map(|b|&mut b.statements) {
            if let Statement::ValuePhi{alternatives,generation,..}=s {
                if alternatives.is_empty(){continue;}
                if let Some(id)=first{*generation=Some(id);break;}
                first=*generation;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn enum_match_three_variants_merges_three_exclusive_loans(){
        let code=format!("{PREFIX}{MODE}match mode{{Mode::A=>{{r=&mut a;}},\
            Mode::B=>{{r=&mut b;}},Mode::C=>{{r=&mut c;}}}}*r=4;");
        let mir=lower_source(&code).unwrap().unwrap();
        let alts=mir.blocks.iter().flat_map(|b|&b.statements).find_map(|s|match s {
            Statement::ValuePhi{alternatives,..} if !alternatives.is_empty()=>Some(alternatives),
            _=>None,
        }).unwrap();
        assert_eq!(alts.len(),3);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn enum_match_wildcard_covers_remaining_variants(){
        let code=format!("{PREFIX}{MODE}match mode{{Mode::A=>{{r=&mut a;}},\
            _=>{{r=&mut b;}}}}*r=4;");
        assert!(checked(&code).unwrap().is_empty());
    }
    #[test]
    fn enum_match_missing_variant_fails_closed(){
        let code=format!("{PREFIX}{MODE}match mode{{Mode::A=>{{r=&mut a;}},\
            Mode::B=>{{r=&mut b;}}}}*r=4;");
        assert!(!matches!(checked(&code),Ok(ref e) if e.is_empty()));
    }
    #[test]
    fn enum_match_duplicate_variant_fails_closed(){
        let code=format!("{PREFIX}{MODE}match mode{{Mode::A=>{{r=&mut a;}},\
            Mode::A=>{{r=&mut b;}},_=>{{r=&mut c;}}}}*r=4;");
        assert!(!matches!(checked(&code),Ok(ref e) if e.is_empty()));
    }
    #[test]
    fn enum_match_reference_result_is_initialized_on_every_arm(){
        let code=format!("{PREFIX}{MODE}let picked=match mode{{\
            Mode::A=>{{&mut a}},Mode::B=>{{&mut b}},Mode::C=>{{&mut c}}}};*picked=7;");
        assert!(checked(&code).unwrap().is_empty());
    }
    #[test]
    fn enum_reference_result_missing_arm_cannot_be_certified(){
        let code=format!("{PREFIX}{MODE}let picked=match mode{{\
            Mode::A=>{{&mut a}},Mode::B=>{{&mut b}}}};*picked=7;");
        assert!(!matches!(checked(&code),Ok(ref e) if e.is_empty()));
    }
}

#[cfg(test)]
mod parent_region_consistency_0638_tests {
    use super::*;

    fn lowered(code:&str)->FunctionMir {
        let tokens=crate::syntax::lex(code).expect("valid test tokens");
        let enums=HashMap::new();let types=HashMap::new();
        let type_ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&enums,types:&types,type_ids:&type_ids,
            type_names:&names,methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
            .expect("complete typed MIR required")
    }

    #[test]
    fn nested_mutable_reborrow_regions_keep_each_parent_live() {
        let mir=lowered("let mut value:i64=1;let a=&mut value;\
            let b=&mut *a;let c=&mut *b;*c=7;");
        assert!(mir.verify().unwrap().is_empty());
    }

    #[test]
    fn forged_self_parent_cannot_be_certified() {
        let mut mir=lowered("let mut value:i64=1;let a=&mut value;\
            let b=&mut *a;*b=7;");
        let mut found=false;
        for statement in mir.blocks.iter_mut().flat_map(|block|&mut block.statements) {
            if let Statement::Access(event)=statement {
                if event.parent.is_some() {
                    event.parent=event.loan;
                    found=true;
                    break;
                }
            }
        }
        assert!(found,"test must contain an explicit reborrow event");
        assert!(mir.verify().unwrap_err().contains("cyclic MIR reborrow"));
    }

    #[test]
    fn forged_parent_loan_with_disjoint_referent_cannot_be_certified() {
        let mut mir=lowered("let mut value:i64=1;let a=&mut value;\
            let b=&mut *a;*b=7;");
        let mut found=false;
        for statement in mir.blocks.iter().flat_map(|block|&block.statements) {
            if let Statement::Access(event)=statement {
                if event.parent.is_some() {
                    let path=mir.loans.get_mut(&event.loan.expect("child loan"))
                        .expect("registered child loan");
                    path.owner=SymbolId(u32::MAX-1);
                    found=true;
                    break;
                }
            }
        }
        assert!(found,"test must contain an explicit reborrow event");
        assert!(mir.verify().unwrap_err().contains("escapes parent provenance"));
    }

    #[test]
    fn early_parent_end_is_rejected_while_child_loan_is_live() {
        let mut mir=lowered("let mut value:i64=1;let parent=&mut value;\
            let child=&mut *parent;*child=7;");
        let (node,at,parent)=mir.blocks.iter().enumerate().find_map(|(node,block)|{
            block.statements.iter().enumerate().find_map(|(at,statement)|{
                match statement {
                    Statement::Access(Event{op:Access::BorrowMut,parent:Some(id),..})=>
                        Some((node,at,*id)),
                    _=>None,
                }
            })
        }).expect("test requires a reborrow with a parent loan");
        let path=mir.loans.get(&parent).expect("parent loan exists").clone();
        mir.blocks[node].statements.insert(at+1,Statement::Access(Event{
            op:Access::EndLoan,path,loan:Some(parent),parent:None,token:0,
        }));
        let errors=mir.verify().expect("graph must diagnose the forged EndLoan");
        assert!(errors.iter().any(|error|
            error.message.contains("cannot end parent loan with active reborrow")),
            "a live child must prevent ending its parent: {errors:?}");
    }
}

#[cfg(test)]
mod enum_owned_move_paths_0640_tests {
    use super::*;

    fn lowered() -> FunctionMir {
        let src="let a:P=P{n:4};let b:P=P{n:5};let e:E=E::Pair(a,b);\
            match e{E::Pair(left,right)=>{let sum:i64=left.n+right.n;},E::U=>{}}";
        let tokens=crate::syntax::lex(src).expect("typed tokens");
        let types=HashMap::from([("P".to_owned(),vec![("n".to_owned(),ConstType::I64)])]);
        let enums=HashMap::from([("E".to_owned(),vec!["Pair".to_owned(),"U".to_owned()])]);
        let payloads=HashMap::from([("E".to_owned(),vec![
            vec![ConstType::Named("P".to_owned()),ConstType::Named("P".to_owned())],vec![]])]);
        let ids=HashMap::from([("P".to_owned(),TypeId(0)),("E".to_owned(),TypeId(1))]);
        let names=vec!["P".to_owned(),"E".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&payloads,enums:&enums,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
            .expect("owned enum patterns must have complete typed MIR")
    }

    #[test]
    fn distinct_owned_variant_fields_have_distinct_move_paths() {
        let mir=lowered();
        let projections=mir.blocks.iter().flat_map(|block|&block.statements)
            .filter_map(|statement|match statement {
                Statement::Access(Event{op:Access::Move,path,..}) if path.fields.len()==1 &&
                    path.fields[0].field.0 & 0x8000_0000 != 0 =>Some(path.clone()),
                _=>None,
            }).collect::<Vec<_>>();
        assert_eq!(projections.len(),2,"both owned payloads must move separately");
        assert_eq!(projections[0].owner,projections[1].owner);
        assert_ne!(projections[0].fields,projections[1].fields);
        assert!(mir.verify().unwrap().is_empty());
    }

    #[test]
    fn double_move_of_an_owned_variant_field_is_rejected() {
        let mut mir=lowered();
        let mut injected=false;
        for block in &mut mir.blocks {
            let duplicate=block.statements.iter().enumerate().find_map(|(index,stmt)|
                matches!(stmt,Statement::Access(Event{op:Access::Move,path,..})
                    if path.fields.len()==1 && path.fields[0].field.0 & 0x8000_0000 != 0)
                    .then(||(index,stmt.clone())));
            if let Some((index,statement))=duplicate {
                block.statements.insert(index+1,statement);
                injected=true;break;
            }
        }
        assert!(injected,"fixture must contain owned field moves");
        let errors=mir.verify().expect("forged duplicate move must be checked");
        assert!(errors.iter().any(|issue|issue.message.contains("moved") ||
            issue.message.contains("uninitialized")),
            "a duplicate variant-field move must be rejected: {errors:?}");
    }

    #[test]
    fn inferred_and_annotated_aggregate_arguments_have_same_type_identity() {
        let src="let named:P=P{n:4};let inferred=P{n:5};\
            let e:E=E::Pair(named,inferred);\
            match e{E::Pair(left,right)=>{let sum:i64=left.n+right.n;},E::U=>{}}";
        let tokens=crate::syntax::lex(src).expect("typed tokens");
        let types=HashMap::from([("P".to_owned(),vec![("n".to_owned(),ConstType::I64)])]);
        let enums=HashMap::from([("E".to_owned(),vec!["Pair".to_owned(),"U".to_owned()])]);
        let payloads=HashMap::from([("E".to_owned(),vec![
            vec![ConstType::Named("P".to_owned()),ConstType::Named("P".to_owned())],vec![]])]);
        let ids=HashMap::from([("P".to_owned(),TypeId(0)),("E".to_owned(),TypeId(1))]);
        let names=vec!["P".to_owned(),"E".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&payloads,enums:&enums,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let mir=lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
            .expect("Named and Resolved forms of one TypeId must lower");
        assert!(mir.verify().unwrap().is_empty());
    }

    #[test]
    fn enum_constructor_rejects_a_distinct_aggregate_type() {
        let src="let wrong:Q=Q{n:4};let e:E=E::Single(wrong);";
        let tokens=crate::syntax::lex(src).expect("typed tokens");
        let types=HashMap::from([
            ("P".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
            ("Q".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
        ]);
        let enums=HashMap::from([("E".to_owned(),vec!["Single".to_owned()])]);
        let payloads=HashMap::from([("E".to_owned(),vec![vec![ConstType::Named("P".to_owned())]])]);
        let ids=HashMap::from([
            ("P".to_owned(),TypeId(0)),("Q".to_owned(),TypeId(1)),("E".to_owned(),TypeId(2)),
        ]);
        let names=vec!["P".to_owned(),"Q".to_owned(),"E".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&payloads,enums:&enums,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        assert!(lower(&tokens,0..tokens.len(),&[],&schema).unwrap().is_none(),
            "different aggregate TypeIds must not be accepted as one payload type");
    }

    #[test]
    fn partial_enum_move_uses_the_original_owner_without_a_whole_move() {
        let mir=lowered();
        let fields=mir.blocks.iter().flat_map(|block|&block.statements)
            .filter_map(|statement|match statement {
                Statement::Access(Event{op:Access::Move,path,..}) if path.fields.len()==1 &&
                    path.fields[0].field.0 & 0x8000_0000 != 0=>Some(path.clone()),
                _=>None,
            }).collect::<Vec<_>>();
        assert_eq!(fields.len(),2);
        assert_eq!(fields[0].owner,fields[1].owner);
        assert!(!mir.blocks.iter().flat_map(|b|&b.statements).any(|s|
            matches!(s,Statement::Access(Event{op:Access::Move,path,..})
                if path.owner==fields[0].owner && path.fields.is_empty())),
            "a partial match must not move its original root");
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn reading_whole_root_after_a_partial_variant_move_is_not_certified() {
        let mut mir=lowered();
        let mut inserted=false;
        for block in &mut mir.blocks {
            let found=block.statements.iter().enumerate().find_map(|(index,s)|
                match s {Statement::Access(Event{op:Access::Move,path,..})
                    if !path.fields.is_empty() && path.fields[0].field.0 & 0x8000_0000!=0=>
                    Some((index,path.clone())),_=>None});
            if let Some((at,path))=found{
                block.statements.insert(at+1,Statement::Access(Event{
                    op:Access::Read,path:Path::root(path.owner),loan:None,
                    parent:None,token:0,
                }));
                inserted=true;break;
            }
        }
        assert!(inserted);
        let errors=mir.verify().unwrap();
        assert!(errors.iter().any(|issue|issue.message.contains("uninitialized") ||
            issue.message.contains("moved")),"root read must be rejected: {errors:?}");
    }
}

#[cfg(test)]
mod enum_borrowed_mir_0641_tests {
    use super::*;
    fn lower_enum(source:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(source).unwrap();
        let mut names=HashMap::new();
        names.insert("E".to_owned(),TypeId(0));
        let type_names=vec!["E".to_owned()];
        let mut enums=HashMap::new();
        enums.insert("E".to_owned(),vec!["V".to_owned(),"Other".to_owned()]);
        let mut payloads=HashMap::new();
        payloads.insert("E".to_owned(),vec![vec![ConstType::I64,ConstType::I64],vec![]]);
        let types=HashMap::new();let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&names,type_names:&type_names,methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
    }
    #[test]
    fn enum_payload_mut_borrows_are_distinct_typed_paths(){
        let src="let mut e:E=E::V(1,2);
            match &mut e {E::V(ref mut a,ref mut b)=>{*a=3;*b=4;},E::Other=>{}}";
        let mir=lower_enum(src).expect("borrowed payload patterns have complete MIR");
        let mut paths=Vec::new();
        for b in &mir.blocks {for statement in &b.statements {for event in statement.events(){
            if event.op==Access::BorrowMut {paths.push(event.path.clone());}
        }}}
        assert_eq!(paths.len(),2);
        assert_ne!(paths[0],paths[1]);
        assert_eq!(paths[0].owner,paths[1].owner);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn enum_payload_shared_refs_leave_owner_unmoved(){
        let src="let e:E=E::V(1,2);
            match &e {E::V(ref a,ref b)=>{let x:i64=*a;let y:i64=*b;},E::Other=>{}}
            match e {E::V(x,y)=>{},E::Other=>{}}";
        let mir=lower_enum(src).expect("shared enum match lowered");
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn enum_match_without_mutability_cannot_lower_ref_mut(){
        let src="let mut e:E=E::V(1,2);
            match &e {E::V(ref mut a,_)=>{*a=5;},E::Other=>{}}";
        assert!(lower_enum(src).is_none());
    }
}

#[cfg(test)]
mod pure_guard_cfg_0643_tests {
    use super::*;
    fn compile_guarded(src:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(src).unwrap();
        let enums=HashMap::from([("E".to_string(),vec!["A".to_string(),"B".to_string()])]);
        let type_ids=HashMap::from([("E".to_string(),TypeId(0))]);
        let type_names=vec!["E".to_string()];
        let payloads=HashMap::from([("E".to_string(),vec![vec![],vec![]])]);
        let types=HashMap::new();let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&type_ids,type_names:&type_names,methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
    }
    #[test]
    fn guarded_enum_is_lowered_with_all_paths() {
        let mir=compile_guarded("let e:E=E::A;let ready:bool=true;
            match e{E::A if ready=>{},E::A=>{},E::B=>{}}").expect("complete guarded enum MIR");
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn guarded_enum_alone_is_not_exhaustive_for_mir() {
        assert!(compile_guarded("let e:E=E::A;
            match e{E::A if true=>{},E::B=>{}}").is_none());
    }
    #[test]
    fn side_effecting_guard_has_no_mir_certificate() {
        assert!(compile_guarded("let e:E=E::A;
            match e{E::A if side_effect()=>{},E::A=>{},E::B=>{}}").is_none());
    }
}

#[cfg(test)]
mod recursive_enum_movepaths_0644_tests {
    use super::*;
    fn lower_nested(source:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(source).unwrap();
        let names=vec!["P".to_owned(),"Inner".to_owned(),"Outer".to_owned()];
        let ids=names.iter().enumerate().map(|(i,n)|(n.clone(),TypeId(i as u32)))
            .collect::<HashMap<_,_>>();
        let types=HashMap::from([("P".to_owned(),vec![("n".to_owned(),ConstType::I64)])]);
        let enums=HashMap::from([
            ("Inner".to_owned(),vec!["Pair".to_owned(),"Empty".to_owned()]),
            ("Outer".to_owned(),vec!["Wrap".to_owned(),"Nil".to_owned()]),
        ]);
        let payloads=HashMap::from([
            ("Inner".to_owned(),vec![vec![ConstType::Named("P".into()),ConstType::Named("P".into())],vec![]]),
            ("Outer".to_owned(),vec![vec![ConstType::Named("Inner".into())],vec![]]),
        ]);
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        lower(&tokens,0..tokens.len(),&[],&schema).unwrap()
    }
    #[test]
    fn nested_noncopy_fields_move_from_distinct_typed_paths(){
        let src="let a:P=P{n:1};let b:P=P{n:2};let inner:Inner=Inner::Pair(a,b);
            let outer:Outer=Outer::Wrap(inner);
            match outer{Outer::Wrap(Inner::Pair(x,y))=>{let n:i64=x.n+y.n;},_=>{}}";
        let mir=lower_nested(src).expect("complete recursive pattern MIR");
        let fields=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).filter(|e|e.op==Access::Move && e.path.fields.len()==2)
            .map(|e|e.path.clone()).collect::<Vec<_>>();
        assert_eq!(fields.len(),2,"each non-Copy nested field requires a move");
        assert_ne!(fields[0],fields[1]);
        assert_eq!(fields[0].fields[0],fields[1].fields[0]);
        assert_ne!(fields[0].fields[1],fields[1].fields[1]);
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn wildcard_is_required_for_restrictive_nested_discriminant(){
        let src="let a:P=P{n:1};let b:P=P{n:2};let i:Inner=Inner::Pair(a,b);
            let o:Outer=Outer::Wrap(i);
            match o{Outer::Wrap(Inner::Pair(x,y))=>{let n:i64=x.n;},Outer::Nil=>{}}";
        assert!(lower_nested(src).is_none());
    }
    #[test]
    fn deep_borrow_loans_keep_exact_variant_specific_paths(){
        let src="let a:P=P{n:1};let b:P=P{n:2};let i:Inner=Inner::Pair(a,b);
            let mut o:Outer=Outer::Wrap(i);
            match &mut o{Outer::Wrap(Inner::Pair(ref mut x,ref mut y))=>{},_=>{}}";
        let mir=lower_nested(src).expect("deep borrowed patterns have typed MIR");
        let borrowed=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).filter(|e|e.op==Access::BorrowMut)
            .map(|e|e.path.clone()).collect::<Vec<_>>();
        assert_eq!(borrowed.len(),2);
        assert_eq!(borrowed[0].fields.len(),2);
        assert_ne!(borrowed[0],borrowed[1]);
        assert!(mir.verify().unwrap().is_empty());
    }
}

#[cfg(test)]
mod interproc_movepath_boundary_0649_tests {
    use super::*;

    fn run(body:&str)->Option<(FunctionMir,Vec<cfg_borrow::Conflict>)>{
        let tokens=crate::syntax::lex(body).unwrap();
        let mut types=HashMap::new();
        types.insert("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]);
        types.insert("Pair".to_owned(),vec![
            ("left".to_owned(),ConstType::Named("Blob".into())),
            ("right".to_owned(),ConstType::Named("Blob".into()))]);
        let type_ids=HashMap::from([("Pair".to_owned(),TypeId(0)),("Blob".to_owned(),TypeId(1))]);
        let type_names=vec!["Pair".to_owned(),"Blob".to_owned()];
        let methods=HashMap::new();let verified_effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&type_ids,type_names:&type_names,
            methods:&methods,verified_effects:&verified_effects};
        let mut calls=HashMap::new();
        calls.insert("consume".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Named("Blob".into())],field_writes:vec![],returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()});
        calls.insert("inspect".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Ref(Box::new(ConstType::Named("Blob".into())))],field_writes:vec![],returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()});
        calls.insert("change".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::RefMut(Box::new(ConstType::Named("Blob".into())))],field_writes:vec![],returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()});
        calls.insert("both".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::RefMut(Box::new(ConstType::Named("Blob".into()))),
                ConstType::RefMut(Box::new(ConstType::Named("Blob".into())))],field_writes:vec![],returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()});
        calls.insert("mixed".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::RefMut(Box::new(ConstType::Named("Blob".into()))),
                ConstType::Ref(Box::new(ConstType::Named("Blob".into())))],
            field_writes:vec![],returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()});
        calls.insert("two_shared".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Ref(Box::new(ConstType::Named("Blob".into()))),
                ConstType::Ref(Box::new(ConstType::Named("Blob".into())))],
            field_writes:vec![],returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()});
        calls.insert("borrow_owned".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Ref(Box::new(ConstType::Named("Blob".into()))),
                ConstType::Named("Blob".into())],
            field_writes:vec![],returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()});
        let mir=lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .unwrap()?;
        let errors=mir.verify().unwrap();
        Some((mir,errors))
    }
    const SOURCE:&str="let p:Pair=Pair{left:Blob{n:1},right:Blob{n:2}};";
    const MUT_SOURCE:&str="let mut p:Pair=Pair{left:Blob{n:1},right:Blob{n:2}};";

    #[test]
    fn projected_move_keeps_sibling_live(){
        let input=format!("{SOURCE} consume(p.left);let keep:Blob=p.right;");
        let (mir,errors)=run(&input).expect("fully lowered call");
        assert!(errors.is_empty(),"{errors:?}");
        assert!(mir.blocks.iter().flat_map(|b|&b.statements).any(|s|
            matches!(s,Statement::Call{name,events,..} if name=="consume" &&
                events.iter().any(|e|e.op==Access::Move && e.path.fields.len()==1))));
    }
    #[test]
    fn projected_move_twice_fails(){
        let input=format!("{SOURCE} consume(p.left);consume(p.left);");
        assert!(!run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn whole_owner_after_projected_move_fails(){
        let input=format!("{SOURCE} consume(p.left);let whole:Pair=p;");
        assert!(!run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn sibling_borrow_survives_unrelated_partial_move(){
        let input=format!("{SOURCE} consume(p.left);inspect(&p.right);");
        assert!(run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn borrowing_moved_field_fails(){
        let input=format!("{SOURCE} consume(p.left);inspect(&p.left);");
        assert!(!run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn distinct_mutable_field_arguments_have_separate_movepaths(){
        let input=format!("{MUT_SOURCE} both(&mut p.left,&mut p.right);");
        assert!(run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn same_mutable_field_cannot_be_two_exclusive_arguments(){
        let input=format!("{MUT_SOURCE} both(&mut p.left,&mut p.left);");
        assert!(!run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn sequential_shared_then_exclusive_call_releases_temporary_loan(){
        let input=format!("{MUT_SOURCE} inspect(&p.left);change(&mut p.left);");
        assert!(run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn conditionally_moved_field_remains_maybe_uninitialized(){
        let input=format!("{SOURCE} if true {{consume(p.left);}} else {{}} let whole:Pair=p;");
        assert!(!run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn conditional_sibling_borrow_does_not_move_the_owner(){
        let input=format!("{SOURCE} if true {{inspect(&p.left);}} else {{inspect(&p.right);}} let whole:Pair=p;");
        assert!(run(&input).unwrap().1.is_empty());
    }
    #[test]
    fn shared_aliases_are_legal_across_a_verified_call(){
        let input=format!("{SOURCE} two_shared(&p.left,&p.left);");
        assert!(run(&input).expect("typed MIR").1.is_empty());
    }
    #[test]
    fn exclusive_and_shared_alias_across_call_is_rejected(){
        let input=format!("{MUT_SOURCE} mixed(&mut p.left,&p.left);");
        assert!(!run(&input).expect("typed MIR").1.is_empty());
    }
    #[test]
    fn exclusive_and_shared_disjoint_siblings_are_legal(){
        let input=format!("{MUT_SOURCE} mixed(&mut p.left,&p.right);");
        assert!(run(&input).expect("typed MIR").1.is_empty());
    }
    #[test]
    fn moving_the_borrowed_actual_in_one_call_is_rejected(){
        let input=format!("{SOURCE} borrow_owned(&p.left,p.left);");
        assert!(!run(&input).expect("typed MIR").1.is_empty());
    }
    #[test]
    fn moving_an_independent_sibling_in_one_call_is_allowed(){
        let input=format!("{SOURCE} borrow_owned(&p.left,p.right);");
        assert!(run(&input).expect("typed MIR").1.is_empty());
    }
    #[test]
    fn shared_unanimous_phi_can_be_forwarded_to_verified_callee(){
        let input=format!("{SOURCE} let r=if true{{&p.left}}else{{&p.left}};inspect(r);");
        let (mir,errors)=run(&input).expect("shared PHI gets a complete MIR");
        assert!(errors.is_empty(),"{errors:?}");
        let (phi_path,phi_generation)=mir.blocks.iter().flat_map(|b|&b.statements)
            .find_map(|statement|match statement {
                Statement::Call{name,events,..} if name=="inspect"=>events.iter()
                    .find_map(|e|if e.op==Access::Read && e.path.fields.is_empty() {
                        e.loan.map(|loan|(e.path.clone(),loan))
                    }else{None}),
                _=>None,
            }).expect("verified call must read the symbolic PHI generation");
        let alternatives=mir.blocks.iter().flat_map(|b|&b.statements)
            .find_map(|statement|match statement {
                Statement::ValuePhi{check,generation:Some(id),alternatives,..}
                    if *id==phi_generation && check.path==phi_path=>Some(alternatives),
                _=>None,
            }).expect("call generation must belong to an actual reference PHI");
        assert_eq!(alternatives.len(),2,"both CFG arms need loan witnesses");
        assert_ne!(alternatives[0].loan,alternatives[1].loan);
        assert_eq!(alternatives[0].path,alternatives[1].path);
        for option in alternatives {
            assert!(!option.exclusive);
            assert_eq!(option.path.fields.len(),1);
            assert_eq!(mir.loans.get(&option.loan),Some(&option.path));
            assert!(mir.blocks.iter().flat_map(|b|&b.statements).any(|statement|
                matches!(statement,Statement::Access(e) if
                    e.op==Access::BorrowShared && e.path==option.path &&
                    e.loan==Some(option.loan))),
                "PHI alternative must originate from a real shared-borrow event");
        }
    }
    #[test]
    fn forwarded_shared_phi_cannot_read_a_moved_referent(){
        let input=format!("{SOURCE} let r=if true{{&p.left}}else{{&p.left}};consume(p.left);inspect(r);");
        let (_,errors)=run(&input).expect("PHI reference still checked after move");
        assert!(!errors.is_empty(),"a live PHI loan must prevent the move");
    }
    #[test]
    fn non_unanimous_phi_argument_is_not_guessed_from_one_branch(){
        let input=format!("{SOURCE} let r=if true{{&p.left}}else{{&p.right}};inspect(r);");
        let (mir,errors)=run(&input).expect("disjunctive shared PHI is lowered");
        assert!(errors.is_empty(),"{errors:?}");
        assert!(mir.blocks.iter().flat_map(|b|&b.statements).any(|statement|
            matches!(statement,Statement::Call{name,events,..} if name=="inspect" &&
                events.iter().any(|e|e.op==Access::Read && e.loan.is_some()))));
    }
    #[test]
    fn unknown_helper_cannot_invent_a_verified_effect_summary(){
        let input=format!("{SOURCE} unknown_helper(p.left);");
        assert!(run(&input).is_none());
    }
    #[test]
    fn wrong_argument_type_cannot_reuse_a_verified_summary(){
        let input=format!("{SOURCE} consume(p);");
        assert!(run(&input).is_none());
    }
    #[test]
    fn mutable_argument_uses_typed_projection(){
        let input=format!("{MUT_SOURCE} change(&mut p.left);let whole:Pair=p;");
        assert!(run(&input).unwrap().1.is_empty());
    }
}

#[cfg(test)]
mod interproc_alias_soundness_0658_tests {
    use super::*;
    fn left()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn right()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn child(field:FieldKey)->Path{Path::root(SymbolId(25)).child(field)}
    fn borrow(exclusive:bool)->Event{Event{
        op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
        path:child(left()),loan:Some(SymbolId(30)),parent:None,token:1,
    }}
    fn write(path:Path,loan:Option<SymbolId>)->Event{
        Event{op:Access::Write,path,loan,parent:None,token:1}
    }
    fn effect(path:Path,kind:VerifiedEffectKind)->VerifiedAppliedEffect{
        VerifiedAppliedEffect{path,kind,alternatives:Vec::new()}
    }
    fn audit(events:Vec<Event>,effects:Vec<VerifiedAppliedEffect>,
        cases:Vec<VerifiedAppliedPathCase>)->Result<(),String>{
        let statement=Statement::Call{name:"verified".into(),token:1,events,effects,path_cases:cases};
        let mir=FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![
            BasicBlock{statements:vec![statement],terminator:Terminator::Return},
        ]};
        mir.validate_interprocedural_alias_proofs()
    }
    #[test]
    fn exclusive_field_write_with_exact_loan_witness_is_allowed(){
        let path=child(left());
        assert!(audit(vec![borrow(true),write(path.clone(),Some(SymbolId(30)))],
            vec![effect(path,VerifiedEffectKind::Write)],vec![]).is_ok());
    }
    #[test]
    fn shared_reference_cannot_certify_mutation(){
        let path=child(left());
        assert!(audit(vec![borrow(false),write(path.clone(),Some(SymbolId(30)))],
            vec![effect(path,VerifiedEffectKind::Write)],vec![]).is_err());
    }
    #[test]
    fn exclusive_loan_does_not_authorize_a_sibling_field(){
        let target=child(right());
        assert!(audit(vec![borrow(true),write(target.clone(),Some(SymbolId(30)))],
            vec![effect(target,VerifiedEffectKind::Write)],vec![]).is_err());
    }
    #[test]
    fn reference_parameter_cannot_certify_move(){
        let target=child(left());
        assert!(audit(vec![borrow(true)],
            vec![effect(target,VerifiedEffectKind::Move)],vec![]).is_err());
    }
    #[test]
    fn reference_parameter_cannot_certify_drop(){
        let target=child(left());
        assert!(audit(vec![borrow(true)],
            vec![effect(target,VerifiedEffectKind::Drop)],vec![]).is_err());
    }
    #[test]
    fn forged_path_case_cannot_omit_a_possible_effect(){
        let path=child(left());
        assert!(audit(vec![borrow(true),write(path.clone(),Some(SymbolId(30)))],
            vec![effect(path,VerifiedEffectKind::Write)],
            vec![VerifiedAppliedPathCase{effects:vec![],returned:None,
                uninitialized:vec![]}]).is_err());
    }
    #[test]
    fn case_cannot_claim_an_unwitnessed_partial_move(){
        let path=child(left());
        let ev=effect(path.clone(),VerifiedEffectKind::Write);
        assert!(audit(vec![borrow(true),write(path.clone(),Some(SymbolId(30)))],
            vec![ev.clone()],vec![VerifiedAppliedPathCase{effects:vec![ev],
                returned:None,uninitialized:vec![path]}]).is_err());
    }
    #[test]
    fn owned_parameter_move_effect_is_metadata_not_a_second_move(){
        let path=child(left());let root=Path::root(SymbolId(25));
        let actual_move=Event{op:Access::Move,path:root,loan:None,parent:None,token:1};
        assert!(audit(vec![actual_move],vec![effect(path,VerifiedEffectKind::Move)],
            vec![]).is_ok());
    }
}

#[cfg(test)]
mod interproc_projected_effects_0650_tests {
    use super::*;

    fn setup(body:&str)->Option<(FunctionMir,Vec<cfg_borrow::Conflict>)> {
        let tokens=crate::syntax::lex(body).unwrap();
        let types=HashMap::from([
            ("Pair".to_owned(),vec![
                ("left".to_owned(),ConstType::Named("Blob".to_owned())),
                ("right".to_owned(),ConstType::Named("Blob".to_owned())),
            ]),
            ("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
        ]);
        let type_ids=HashMap::from([
            ("Pair".to_owned(),TypeId(0)),
            ("Blob".to_owned(),TypeId(1)),
        ]);
        let type_names=vec!["Pair".to_owned(),"Blob".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{
            enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&type_ids,type_names:&type_names,
            methods:&methods,verified_effects:&effects,
        };
        let pair=ConstType::Named("Pair".to_owned());
        let blob=ConstType::Named("Blob".to_owned());
        let left=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let right=FieldKey{aggregate:TypeId(0),field:FieldId(1)};
        let n=FieldKey{aggregate:TypeId(1),field:FieldId(0)};
        let mut summaries=HashMap::new();
        summaries.insert("get".to_owned(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Ref(Box::new(pair.clone()))],
            field_writes:Vec::new(),returned:Some(VerifiedReturnedReference{
                parameter:0,fields:vec![left],ty:ConstType::Ref(Box::new(blob.clone())),
            }),
            returned_alternatives:Vec::new(),path_cases:Vec::new()});
        summaries.insert("get_mut".to_owned(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::RefMut(Box::new(pair.clone()))],
            field_writes:vec![VerifiedFieldWrite{parameter:0,fields:vec![right,n]}],
            returned:Some(VerifiedReturnedReference{
                parameter:0,fields:vec![left],ty:ConstType::RefMut(Box::new(blob.clone())),
            }),
            returned_alternatives:Vec::new(),path_cases:Vec::new()});
        summaries.insert("set".to_owned(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::RefMut(Box::new(blob.clone()))],
            field_writes:vec![VerifiedFieldWrite{parameter:0,fields:vec![n]}],
            returned:None,
            returned_alternatives:Vec::new(),path_cases:Vec::new()});
        summaries.insert("invalid_mut".to_owned(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Ref(Box::new(pair.clone()))],
            field_writes:vec![VerifiedFieldWrite{parameter:0,fields:vec![left]}],
            returned:None,
            returned_alternatives:Vec::new(),path_cases:Vec::new()});
        summaries.insert("invalid_type".to_owned(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Ref(Box::new(pair.clone()))],
            field_writes:vec![],returned:Some(VerifiedReturnedReference{
                parameter:0,fields:vec![left],ty:ConstType::Ref(Box::new(ConstType::Bool)),
            }),
            returned_alternatives:Vec::new(),path_cases:Vec::new()});
        summaries.insert("forged_field".to_owned(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Ref(Box::new(pair))],
            field_writes:vec![],returned:Some(VerifiedReturnedReference{
                parameter:0,fields:vec![FieldKey{aggregate:TypeId(1),field:FieldId(0)}],
                ty:ConstType::Ref(Box::new(blob)),
            }),
            returned_alternatives:Vec::new(),path_cases:Vec::new()});
        let shared_pair=ConstType::Ref(Box::new(ConstType::Named("Pair".into())));
        let mutable_pair=ConstType::RefMut(Box::new(ConstType::Named("Pair".into())));
        let shared_blob=ConstType::Ref(Box::new(ConstType::Named("Blob".into())));
        let mutable_blob=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        summaries.insert("either".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Bool,shared_pair],
            field_writes:Vec::new(),returned:None,
            returned_alternatives:vec![
                VerifiedReturnedReference{parameter:1,fields:vec![left],ty:shared_blob.clone()},
                VerifiedReturnedReference{parameter:1,fields:vec![right],ty:shared_blob},
            ],path_cases:Vec::new()});
        summaries.insert("either_mut".into(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Bool,mutable_pair],
            field_writes:vec![VerifiedFieldWrite{parameter:1,fields:vec![right,n]}],
            returned:None,returned_alternatives:vec![
                VerifiedReturnedReference{parameter:1,fields:vec![left],ty:mutable_blob.clone()},
                VerifiedReturnedReference{parameter:1,fields:vec![right],ty:mutable_blob},
            ],path_cases:Vec::new()});
        let mir=lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&summaries)
            .unwrap()?;
        let result=mir.verify().unwrap();
        Some((mir,result))
    }
    const OWNER:&str="let p:Pair=Pair{left:Blob{n:1},right:Blob{n:2}};";
    const MUT_OWNER:&str="let mut p:Pair=Pair{left:Blob{n:1},right:Blob{n:2}};";

    #[test]
    fn projected_return_keeps_unrelated_sibling_move_valid() {
        let src=format!("{OWNER} let r=get(&p);let other:Blob=p.right;let x:i64=r.n;");
        assert!(setup(&src).unwrap().1.is_empty());
    }
    #[test]
    fn projected_return_blocks_move_of_live_referent() {
        let src=format!("{OWNER} let r=get(&p);let moved:Blob=p.left;let x:i64=r.n;");
        assert!(!setup(&src).unwrap().1.is_empty());
    }
    #[test]
    fn projected_return_blocks_whole_owner_move() {
        let src=format!("{OWNER} let r=get(&p);let moved:Pair=p;let x:i64=r.n;");
        assert!(!setup(&src).unwrap().1.is_empty());
    }
    #[test]
    fn mutable_field_write_is_sandwiched_by_verified_loan() {
        let src=format!("{MUT_OWNER} let r=get_mut(&mut p);let x:i64=r.n;");
        let (mir,conflicts)=setup(&src).unwrap();
        assert!(conflicts.is_empty(),"{conflicts:?}");
        let events=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|stmt|{
            match stmt{Statement::Call{name,events,..} if name=="get_mut"=>Some(events),_=>None}
        }).expect("call event sequence");
        let mut borrow=None;
        let mut write=None;
        let mut end=None;
        for (i,e) in events.iter().enumerate(){
            if e.op==Access::BorrowMut{borrow=Some(i);}
            if e.op==Access::Write{write=Some(i);assert_eq!(e.path.fields.len(),2);}
            if e.op==Access::EndLoan{end=Some(i);}
        }
        assert!(borrow.unwrap()<write.unwrap() && write.unwrap()<end.unwrap());
    }
    #[test]
    fn changed_sibling_can_be_read_after_returned_mut_borrow() {
        let src=format!("{MUT_OWNER} let r=get_mut(&mut p);let x:i64=r.n;let y:i64=p.right.n;");
        assert!(setup(&src).unwrap().1.is_empty());
    }
    #[test]
    fn two_call_borrows_on_disjoint_fields_are_legal() {
        let src=format!("{MUT_OWNER} let a=&p.left;set(&mut p.right);let x:i64=a.n;");
        assert!(setup(&src).unwrap().1.is_empty());
    }
    #[test]
    fn writing_borrowed_field_is_rejected() {
        let src=format!("{MUT_OWNER} let a=&p.right;set(&mut p.right);let x:i64=a.n;");
        assert!(!setup(&src).unwrap().1.is_empty());
    }
    #[test]
    fn shared_formal_cannot_represent_mutating_callee() {
        let src=format!("{OWNER} invalid_mut(&p);");
        assert!(setup(&src).is_none());
    }
    #[test]
    fn forged_return_field_type_fails_closed() {
        let src=format!("{OWNER} let a=invalid_type(&p);");
        assert!(setup(&src).is_none());
    }
    #[test]
    fn forged_return_aggregate_identity_fails_closed() {
        let src=format!("{OWNER} let a=forged_field(&p);");
        assert!(setup(&src).is_none());
    }
    #[test]
    fn mutable_return_protects_only_its_typed_field() {
        let src=format!("{MUT_OWNER} let r=get_mut(&mut p);let moved:Blob=p.left;let x:i64=r.n;");
        assert!(!setup(&src).unwrap().1.is_empty());
    }
    #[test]
    fn sibling_mutation_does_not_move_affine_owner() {
        let src=format!("{MUT_OWNER} set(&mut p.right);let keep:Blob=p.left;");
        assert!(setup(&src).unwrap().1.is_empty());
    }

    #[test]
    fn multi_origin_call_creates_distinct_phi_loans() {
        let src=format!("{OWNER} let r=either(true,&p);let x:i64=r.n;");
        let (mir,conflicts)=setup(&src).expect("multi-origin call lowering");
        assert!(conflicts.is_empty(),"{conflicts:?}");
        let options=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .find_map(|s|if let Statement::ValuePhi{alternatives,..}=s {
                (alternatives.len()==2).then_some(alternatives)
            }else{None}).expect("call-return PHI with two certified arms");
        assert_ne!(options[0].loan,options[1].loan);
        assert_ne!(options[0].path,options[1].path);
    }
    #[test]
    fn alternative_return_guards_first_field_against_move() {
        let src=format!("{OWNER} let r=either(false,&p);let other:Blob=p.left;let x:i64=r.n;");
        assert!(!setup(&src).expect("complete PHI").1.is_empty());
    }
    #[test]
    fn alternative_return_guards_second_field_against_move() {
        let src=format!("{OWNER} let r=either(true,&p);let other:Blob=p.right;let x:i64=r.n;");
        assert!(!setup(&src).expect("complete PHI").1.is_empty());
    }
    #[test]
    fn mutable_alternative_return_keeps_exact_loan_provenance() {
        let src=format!("{MUT_OWNER} let r=either_mut(true,&mut p);let x:i64=r.n;");
        let (mir,errors)=setup(&src).expect("mutable return arms");
        assert!(errors.is_empty(),"{errors:?}");
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter()).any(|s|
            matches!(s,Statement::ValuePhi{alternatives,..} if alternatives.len()==2 &&
                alternatives.iter().all(|o|o.exclusive))));
    }
    #[test]
    fn mutable_call_phi_field_write_uses_exclusive_alternative_group() {
        let src=format!("{MUT_OWNER} let r=either_mut(true,&mut p);r.n=7;");
        let (mir,conflicts)=setup(&src).expect("mutable field write via return PHI");
        assert!(conflicts.is_empty(),"{conflicts:?}");
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).any(|e|e.op==Access::Write &&
                e.path.fields.is_empty() && e.loan.is_some()));
    }
    #[test]
    fn mutable_return_rejects_partial_move_on_other_possible_arm() {
        let src=format!("{MUT_OWNER} let r=either_mut(true,&mut p);let other:Blob=p.right;let x:i64=r.n;");
        assert!(!setup(&src).expect("all arms must be checked").1.is_empty());
    }
    #[test]
    fn alternate_return_rejects_wrong_selector_type() {
        let src=format!("{OWNER} let r=either(4,&p);let x:i64=r.n;");
        assert!(setup(&src).is_none(),"number cannot satisfy a bool formal");
    }
}

#[cfg(test)]
mod returned_call_phi_forwarding_0652_tests {
    use super::*;

    fn lower_wrapper(body:&str, mutable:bool, three:bool)
        ->Result<Option<FunctionMir>,String>{
        let tokens=crate::syntax::lex(body).expect("valid wrapper tokens");
        let mut types=HashMap::new();
        types.insert("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]);
        types.insert("Tri".to_owned(),vec![
            ("a".to_owned(),ConstType::Named("Blob".to_owned())),
            ("b".to_owned(),ConstType::Named("Blob".to_owned())),
            ("c".to_owned(),ConstType::Named("Blob".to_owned())),
        ]);
        let ids=HashMap::from([("Blob".to_owned(),TypeId(0)),
            ("Tri".to_owned(),TypeId(1))]);
        let names=vec!["Blob".to_owned(),"Tri".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enum_payloads:&HashMap::new(),enums:&HashMap::new(),
            types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let tri=ConstType::Named("Tri".to_owned());
        let arg=if mutable{ConstType::RefMut(Box::new(tri))}
            else{ConstType::Ref(Box::new(tri))};
        let blob=ConstType::Named("Blob".to_owned());
        let result=if mutable{ConstType::RefMut(Box::new(blob))}
            else{ConstType::Ref(Box::new(blob))};
        let origins=(0..(if three {3} else {2})).map(|field|VerifiedReturnedReference{
            parameter:1,
            fields:vec![FieldKey{aggregate:TypeId(1),field:FieldId(field)}],
            ty:result.clone(),
        }).collect();
        let calls=HashMap::from([("choose".to_owned(),VerifiedCallSummary{
            parameter_effects:Vec::new(),
            parameters:vec![ConstType::Bool,arg.clone()],field_writes:Vec::new(),
            returned:None,returned_alternatives:origins,path_cases:Vec::new()})]);
        let params=vec![("flag".to_owned(),ConstType::Bool),
            ("p".to_owned(),arg)];
        lower_with_verified_calls(&tokens,0..tokens.len(),&params,&schema,&[],&calls)
    }
    fn proven(body:&str,mutable:bool,three:bool)->FunctionMir{
        let mir=lower_wrapper(body,mutable,three).expect("MIR lowering")
            .expect("transparent wrapper must be fully MIR-certified");
        assert!(mir.verify().expect("valid PHI graph").is_empty());
        mir
    }
    #[test]
    fn tail_call_preserves_both_returned_fields(){
        let mir=proven("choose(flag,p)",false,false);
        assert!(mir.blocks.iter().flat_map(|b|&b.statements).any(|s|matches!(s,
            Statement::ValuePhi{ty:ConstType::Ref(_),alternatives,..}
                if alternatives.len()==2 && alternatives[0].path!=alternatives[1].path)));
    }
    #[test]
    fn explicit_return_preserves_both_returned_fields(){
        let mir=proven("return choose(flag,p);",false,false);
        assert!(mir.blocks.iter().any(|b|b.terminator==Terminator::Return));
    }
    #[test]
    fn mutable_return_keeps_independent_exclusive_loans(){
        let mir=proven("return choose(flag,p);",true,false);
        assert!(mir.blocks.iter().flat_map(|b|&b.statements).any(|s|matches!(s,
            Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}
                if alternatives.len()==2 && alternatives.iter().all(|o|o.exclusive))));
    }
    #[test]
    fn three_alternatives_are_not_dropped(){
        let mir=proven("choose(flag,p)",false,true);
        assert!(mir.blocks.iter().flat_map(|b|&b.statements).any(|s|matches!(s,
            Statement::ValuePhi{alternatives,..} if alternatives.len()==3)));
    }
    #[test]
    fn unsupported_nested_call_arguments_fail_closed(){
        assert!(lower_wrapper("choose(flag,unknown(p))",false,false).unwrap().is_none());
    }
    #[test]
    fn unknown_callee_is_never_misclassified_as_return_phi(){
        assert!(lower_wrapper("unknown(flag,p)",false,false).unwrap().is_none());
    }
}

#[cfg(test)]
mod transitive_parameter_effects_0654_tests {
    use super::*;

    fn schema_test(source:&str, parameters:&[(String,ConstType)],
        effect:VerifiedCallSummary)->Result<Option<FunctionMir>,String> {
        let tokens=crate::syntax::lex(source).unwrap();
        let mut types=HashMap::new();
        types.insert("Pair".to_owned(),vec![
            ("left".to_owned(),ConstType::Named("Blob".to_owned())),
            ("right".to_owned(),ConstType::Named("Blob".to_owned())),
        ]);
        types.insert("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]);
        let type_ids=HashMap::from([
            ("Pair".to_owned(),TypeId(0)),("Blob".to_owned(),TypeId(1))]);
        let type_names=vec!["Pair".to_owned(),"Blob".to_owned()];
        let methods=HashMap::new();let verified_effects=HashMap::new();
        let enums=HashMap::new();let payloads=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&type_ids,type_names:&type_names,methods:&methods,
            verified_effects:&verified_effects};
        let calls=HashMap::from([("step".to_owned(),effect)]);
        lower_with_verified_calls(&tokens,0..tokens.len(),parameters,&schema,&[],&calls)
    }
    fn left()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn right()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn n()->FieldKey{FieldKey{aggregate:TypeId(1),field:FieldId(0)}}
    fn owned()->ConstType{ConstType::Named("Pair".to_owned())}
    fn mutable()->ConstType{ConstType::RefMut(Box::new(owned()))}
    fn summary(ty:ConstType,effects:Vec<VerifiedParameterEffect>)->VerifiedCallSummary{
        VerifiedCallSummary{parameters:vec![ty],parameter_effects:effects,
            field_writes:Vec::new(),returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()}
    }
    fn effect(kind:VerifiedEffectKind,fields:Vec<FieldKey>)->VerifiedParameterEffect{
        VerifiedParameterEffect{parameter:0,fields,kind}
    }
    #[test]
    fn distinct_owned_move_and_drop_paths_survive_boundary_mapping(){
        let params=vec![("p".to_owned(),owned())];
        let mir=schema_test("step(p);",&params,summary(owned(),vec![
            effect(VerifiedEffectKind::Move,vec![left()]),
            effect(VerifiedEffectKind::Drop,vec![right()]),
        ])).unwrap().expect("fully typed boundary");
        assert!(mir.verify().unwrap().is_empty());
        let effects=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::verified_effects).collect::<Vec<_>>();
        assert_eq!(effects.len(),2);
        assert!(effects.iter().any(|e|e.kind==VerifiedEffectKind::Move &&
            e.path.fields==vec![left()]));
        assert!(effects.iter().any(|e|e.kind==VerifiedEffectKind::Drop &&
            e.path.fields==vec![right()]));
        let root_moves=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).filter(|e|e.op==Access::Move &&
                e.path.fields.is_empty()).count();
        assert_eq!(root_moves,1,"metadata cannot double-consume an actual");
    }
    #[test]
    fn nested_mutable_write_is_qualified_by_both_field_owners(){
        let params=vec![("p".to_owned(),mutable())];
        let mut proven=summary(mutable(),vec![effect(
            VerifiedEffectKind::Write,vec![right(),n()])]);
        proven.field_writes.push(VerifiedFieldWrite{parameter:0,fields:vec![right(),n()]});
        let mir=schema_test("step(p);",&params,proven).unwrap().expect("typed write");
        assert!(mir.verify().unwrap().is_empty());
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::verified_effects).any(|e|
                e.path.fields==vec![right(),n()] &&
                e.kind==VerifiedEffectKind::Write));
    }
    #[test]
    fn drop_through_mutable_reference_is_not_a_verified_effect(){
        let params=vec![("p".to_owned(),mutable())];
        let invalid=summary(mutable(),vec![effect(VerifiedEffectKind::Drop,vec![left()])]);
        assert!(schema_test("step(p);",&params,invalid).unwrap().is_none());
    }
    #[test]
    fn move_through_shared_reference_is_not_a_verified_effect(){
        let shared=ConstType::Ref(Box::new(owned()));
        let params=vec![("p".to_owned(),shared.clone())];
        let invalid=summary(shared,vec![effect(VerifiedEffectKind::Move,vec![left()])]);
        assert!(schema_test("step(p);",&params,invalid).unwrap().is_none());
    }
    #[test]
    fn forged_field_id_must_not_get_a_boundary_certificate(){
        let params=vec![("p".to_owned(),owned())];
        let forged=FieldKey{aggregate:TypeId(77),field:FieldId(0)};
        let invalid=summary(owned(),vec![effect(VerifiedEffectKind::Move,vec![forged])]);
        assert!(schema_test("step(p);",&params,invalid).unwrap().is_none());
    }
    #[test]
    fn copy_literal_cannot_instantiate_an_owned_drop_witness(){
        let scalar=ConstType::Bool;
        let invalid=summary(scalar,vec![effect(VerifiedEffectKind::Drop,Vec::new())]);
        assert!(schema_test("step(true);",&[],invalid).unwrap().is_none());
    }
}


#[cfg(test)]
mod conditional_transitive_effect_paths_0655_tests {
    use super::*;
    fn run(body:&str,formals:&[(String,ConstType)],summary:VerifiedCallSummary)
        ->Option<FunctionMir> {
        let tokens=crate::syntax::lex(body).unwrap();
        let mut types=HashMap::new();
        types.insert("Pair".to_owned(),vec![
            ("left".to_owned(),ConstType::Named("Blob".into())),
            ("right".to_owned(),ConstType::Named("Blob".into()))]);
        types.insert("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]);
        let ids=HashMap::from([("Pair".to_owned(),TypeId(0)),
            ("Blob".to_owned(),TypeId(1))]);
        let names=vec!["Pair".to_owned(),"Blob".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        let calls=HashMap::from([("step".to_owned(),summary)]);
        lower_with_verified_calls(&tokens,0..tokens.len(),formals,&schema,&[],&calls)
            .expect("lower")
    }
    fn left()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn right()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn n()->FieldKey{FieldKey{aggregate:TypeId(1),field:FieldId(0)}}
    fn mutable()->ConstType{ConstType::RefMut(Box::new(ConstType::Named("Pair".into())))}
    fn summary(effects:Vec<VerifiedParameterEffect>)->VerifiedCallSummary{
        VerifiedCallSummary{parameters:vec![mutable()],parameter_effects:effects,
            field_writes:Vec::new(),returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()}
    }
    #[test]
    fn conditional_owned_move_and_drop_are_metadata_not_second_transfers(){
        let owned=ConstType::Named("Pair".into());
        let effects=vec![
            VerifiedParameterEffect{parameter:0,fields:vec![left()],
                kind:VerifiedEffectKind::Move},
            VerifiedParameterEffect{parameter:0,fields:vec![right()],
                kind:VerifiedEffectKind::Drop},
        ];
        let summary=VerifiedCallSummary{parameters:vec![owned.clone()],
            parameter_effects:effects,field_writes:Vec::new(),
            returned:None,returned_alternatives:Vec::new(),path_cases:Vec::new()};
        let params=vec![("p".into(),owned)];
        let mir=run("if true {step(p);} else {step(p);}",&params,summary)
            .expect("complete branch-sensitive transfer");
        assert!(mir.verify().unwrap().is_empty());
        let calls=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter(|s|matches!(s,Statement::Call{name,..} if name=="step"))
            .collect::<Vec<_>>();
        assert_eq!(calls.len(),2);
        for call in calls {
            assert_eq!(call.events().iter().filter(|event|
                event.op==Access::Move && event.path.fields.is_empty()).count(),1,
                "exactly one transfer per reachable call boundary");
            assert_eq!(call.verified_effects().len(),2);
            assert!(call.events().iter().all(|event|event.op!=Access::Drop),
                "callee-internal drops must never be replayed in the caller");
        }
    }
    #[test]
    fn transitive_write_is_checked_even_without_direct_field_writes_entry(){
        let path=vec![right(),n()];
        let effect=VerifiedParameterEffect{parameter:0,fields:path.clone(),
            kind:VerifiedEffectKind::Write};
        let params=vec![("p".into(),mutable())];
        let mir=run("step(p);",&params,summary(vec![effect])).expect("typed call");
        assert!(mir.verify().unwrap().is_empty());
        let writes=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).filter(|e|e.op==Access::Write &&
                e.path.fields==path).collect::<Vec<_>>();
        assert_eq!(writes.len(),1,"each may-write needs exactly one checked event");
        assert!(writes[0].loan.is_some(),"write must carry an exclusive loan");
    }
    #[test]
    fn returned_initialization_state_is_substituted_at_owned_call_boundary(){
        let owned=ConstType::Named("Pair".into());
        let moved=VerifiedParameterEffect{parameter:0,fields:vec![left()],
            kind:VerifiedEffectKind::Move};
        let summary=VerifiedCallSummary{
            parameters:vec![owned.clone()],parameter_effects:vec![moved.clone()],
            field_writes:Vec::new(),returned:None,returned_alternatives:Vec::new(),
            path_cases:vec![VerifiedPathCase{effects:vec![moved],returned:None,
                uninitialized:vec![VerifiedParameterPath{parameter:0,fields:vec![left()]}]}],
        };
        let params=vec![("p".into(),owned)];
        let mir=run("step(p);",&params,summary).expect("valid owned effect evidence");
        let case=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|match s {
            Statement::Call{path_cases,..}=>path_cases.first(),_=>None,
        }).expect("one mapped return case");
        assert_eq!(case.uninitialized.len(),1);
        assert_eq!(case.uninitialized[0].fields,vec![left()]);
        let movements=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).filter(|e|e.op==Access::Move).count();
        assert_eq!(movements,1,"owned argument is transferred once at the boundary");
    }
    #[test]
    fn forged_reference_initialization_state_cannot_be_certified(){
        let write=VerifiedParameterEffect{parameter:0,fields:vec![left()],
            kind:VerifiedEffectKind::Write};
        let mut certified=summary(vec![write.clone()]);
        certified.path_cases=vec![VerifiedPathCase{effects:vec![write],returned:None,
            uninitialized:vec![VerifiedParameterPath{parameter:0,fields:vec![left()]}]}];
        let params=vec![("p".into(),mutable())];
        assert!(run("step(p);",&params,certified).is_none(),
            "a write through &mut cannot claim an owned path is moved");
    }
    #[test]
    fn conditional_calls_preserve_distinct_write_paths_and_local_move_path_ids(){
        let effects=vec![VerifiedParameterEffect{parameter:0,fields:vec![left(),n()],
            kind:VerifiedEffectKind::Write},VerifiedParameterEffect{
                parameter:0,fields:vec![right(),n()],kind:VerifiedEffectKind::Write}];
        let params=vec![("p".into(),mutable())];
        let mir=run("if true {step(p);} else {step(p);}",&params,
            summary(effects)).expect("conditional calls");
        assert!(mir.verify().unwrap().is_empty());
        let applied=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::verified_effects).collect::<Vec<_>>();
        assert_eq!(applied.len(),4,"two may-effects in each of two arms");
        let mut forest=cfg_borrow::Forest::default();
        let paths=applied.iter().map(|e|forest.intern(&e.path).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(paths[0],paths[2]);
        assert_eq!(paths[1],paths[3]);
        assert_ne!(paths[0],paths[1],"sibling projections have distinct local MovePathId");
    }
    #[test]
    fn forged_nested_transitive_effect_is_rejected(){
        let fake=FieldKey{aggregate:TypeId(89),field:FieldId(0)};
        let effects=vec![VerifiedParameterEffect{parameter:0,
            fields:vec![right(),fake],kind:VerifiedEffectKind::Write}];
        let params=vec![("p".into(),mutable())];
        assert!(run("if true {step(p);} else {step(p);}",&params,
            summary(effects)).is_none());
    }
    #[test]
    fn transitive_move_cannot_be_replayed_through_a_mutable_reference(){
        let effects=vec![VerifiedParameterEffect{parameter:0,
            fields:vec![left()],kind:VerifiedEffectKind::Move}];
        let params=vec![("p".into(),mutable())];
        assert!(run("step(p);",&params,summary(effects)).is_none());
    }
    #[test]
    fn duplicate_direct_and_transitive_write_witness_is_executed_once(){
        let field=vec![right(),n()];
        let mut proof=summary(vec![VerifiedParameterEffect{parameter:0,
            fields:field.clone(),kind:VerifiedEffectKind::Write}]);
        proof.field_writes.push(VerifiedFieldWrite{parameter:0,fields:field.clone()});
        let params=vec![("p".into(),mutable())];
        let mir=run("step(p);",&params,proof).expect("typed call");
        let writes=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .flat_map(Statement::events).filter(|e|e.op==Access::Write &&
                e.path.fields==field).count();
        assert_eq!(writes,1);
    }
}

#[cfg(test)]
mod path_sensitive_interprocedural_0656_tests {
    use super::*;
    fn left()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn right()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn blob()->ConstType{ConstType::Named("Blob".into())}
    fn pair()->ConstType{ConstType::Named("Pair".into())}
    fn mutable()->ConstType{ConstType::RefMut(Box::new(pair()))}
    fn effect(fields:Vec<FieldKey>)->VerifiedParameterEffect {
        VerifiedParameterEffect{parameter:0,fields,kind:VerifiedEffectKind::Write}
    }
    fn call_summary()->VerifiedCallSummary {
        VerifiedCallSummary{
            parameters:vec![mutable()],
            field_writes:Vec::new(),
            parameter_effects:vec![effect(vec![left()]),effect(vec![right()])],
            returned:None,returned_alternatives:Vec::new(),
            path_cases:vec![
                VerifiedPathCase{effects:vec![effect(vec![left()])],returned:None,uninitialized:Vec::new()},
                VerifiedPathCase{effects:vec![effect(vec![right()])],returned:None,uninitialized:Vec::new()},
            ],
        }
    }
    fn lower_body(source:&str,summary:VerifiedCallSummary)->Option<(usize,FunctionMir)> {
        let tokens=crate::syntax::lex(source).unwrap();
        let types=HashMap::from([
            ("Pair".into(),vec![("left".into(),blob()),("right".into(),blob())]),
            ("Blob".into(),vec![("n".into(),ConstType::I64)]),
        ]);
        let ids=HashMap::from([("Pair".into(),TypeId(0)),("Blob".into(),TypeId(1))]);
        let names=vec!["Pair".into(),"Blob".into()];
        let enums=HashMap::new();let payloads=HashMap::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let calls=HashMap::from([("step".into(),summary)]);
        let params=vec![("p".into(),mutable())];
        lower_with_verified_calls(&tokens,0..tokens.len(),&params,&schema,&[],&calls)
            .unwrap().map(|mir|(tokens.len(),mir))
    }
    #[test]
    fn correlated_callee_effects_remain_distinct_at_boundary(){
        let (n,mir)=lower_body("step(p);",call_summary()).expect("complete MIR");
        assert!(mir.verify().unwrap().is_empty());
        let cases=mir.solve_path_cases(n,&[("p".into(),mutable())],&[])
            .expect("exact finite paths");
        assert_eq!(cases.len(),2);
        assert!(cases.iter().all(|case|case.effects.len()==1));
        assert!(cases.iter().any(|case|case.effects==vec![effect(vec![left()])]));
        assert!(cases.iter().any(|case|case.effects==vec![effect(vec![right()])]));
    }
    #[test]
    fn branching_call_cases_do_not_forge_joint_effect(){
        let (n,mir)=lower_body("if true {step(p);} else {step(p);}",call_summary())
            .expect("complete conditional MIR");
        assert!(mir.verify().unwrap().is_empty());
        let cases=mir.solve_path_cases(n,&[("p".into(),mutable())],&[])
            .expect("every conditional path");
        assert_eq!(cases.len(),2);
        assert!(cases.iter().all(|case|case.effects.len()==1));
    }
    #[test]
    fn transitive_chains_remap_owners_not_callee_ids(){
        let (n,mir)=lower_body("step(p);",call_summary()).unwrap();
        let call=mir.blocks.iter().flat_map(|b|&b.statements).find_map(|s|
            match s {Statement::Call{path_cases,..}=>Some(path_cases),_=>None}).unwrap();
        assert_eq!(call.len(),2);
        for case in call {assert_eq!(case.effects[0].path.owner.0 as usize,n+1);}
        let mut forest=cfg_borrow::Forest::default();
        let a=forest.intern(&call[0].effects[0].path).unwrap();
        let b=forest.intern(&call[1].effects[0].path).unwrap();
        assert_ne!(a,b,"different fields need distinct caller MovePathIds");
    }
    #[test]
    fn forged_correlated_effect_is_not_admitted(){
        let mut summary=call_summary();
        summary.path_cases[0].effects.push(VerifiedParameterEffect{
            parameter:0,fields:vec![FieldKey{aggregate:TypeId(77),field:FieldId(0)}],
            kind:VerifiedEffectKind::Write});
        assert!(lower_body("step(p);",summary).is_none());
    }
    #[test]
    fn returned_index_without_reference_is_not_admitted(){
        let mut summary=call_summary();
        summary.path_cases[0].returned=Some(0);
        assert!(lower_body("step(p);",summary).is_none());
    }
    #[test]
    fn case_cannot_invent_move_through_mut_ref(){
        let mut summary=call_summary();
        summary.parameter_effects.push(VerifiedParameterEffect{
            parameter:0,fields:vec![left()],kind:VerifiedEffectKind::Move});
        summary.path_cases[0].effects[0].kind=VerifiedEffectKind::Move;
        assert!(lower_body("step(p);",summary).is_none());
    }
    #[test]
    fn diamond_phi_correlates_effect_and_returned_field(){
        let root=Path::root(SymbolId(101));
        let a=root.child(left());let b=root.child(right());
        let dest=Path::root(SymbolId(300));
        let o1=RefOption{loan:SymbolId(201),path:a.clone(),exclusive:false,parent:None};
        let o2=RefOption{loan:SymbolId(202),path:b.clone(),exclusive:false,parent:None};
        let write=|path:Path|Statement::Access(Event{
            op:Access::Write,path,loan:None,parent:None,token:1});
        let borrow=|option:&RefOption|Statement::Access(Event{
            op:Access::BorrowShared,path:option.path.clone(),loan:Some(option.loan),
            parent:None,token:1});
        let mir=FunctionMir{entry:0,loans:HashMap::from([
            (o1.loan,a.clone()),(o2.loan,b.clone())]),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![write(a.clone()),borrow(&o1)],terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![write(b.clone()),borrow(&o2)],terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![Statement::ValuePhi{
                ty:ConstType::Ref(Box::new(blob())),predecessors:vec![1,2],
                check:Event{op:Access::Read,path:dest,loan:None,parent:None,token:2},
                generation:Some(SymbolId(301)),provenance:None,
                alternatives:vec![o1,o2],
            }],terminator:Terminator::Return},
        ]};
        let origins=vec![
            VerifiedReturnedReference{parameter:0,fields:vec![left()],ty:ConstType::Ref(Box::new(blob()))},
            VerifiedReturnedReference{parameter:0,fields:vec![right()],ty:ConstType::Ref(Box::new(blob()))},
        ];
        let cases=mir.solve_path_cases(100,&[("p".into(),mutable())],&origins).unwrap();
        assert_eq!(cases.len(),2);
        assert!(cases.contains(&VerifiedPathCase{effects:vec![effect(vec![left()])],returned:Some(0),uninitialized:Vec::new()}));
        assert!(cases.contains(&VerifiedPathCase{effects:vec![effect(vec![right()])],returned:Some(1),uninitialized:Vec::new()}));
    }
    #[test]
    fn return_phi_uses_only_effects_correlated_with_its_origin(){
        let mut summary=call_summary();
        let returned_ty=ConstType::RefMut(Box::new(blob()));
        summary.returned_alternatives=vec![
            VerifiedReturnedReference{parameter:0,fields:vec![left()],ty:returned_ty.clone()},
            VerifiedReturnedReference{parameter:0,fields:vec![right()],ty:returned_ty},
        ];
        summary.path_cases[0].returned=Some(0);
        summary.path_cases[1].returned=Some(1);
        let (_,mir)=lower_body("let r = step(p);",summary)
            .expect("bounded verified return PHI");
        let calls=mir.blocks.iter().flat_map(|b|&b.statements).filter_map(|s|
            match s {Statement::Call{effects,path_cases,..}=>Some((effects,path_cases)),_=>None})
            .collect::<Vec<_>>();
        assert_eq!(calls.len(),2);
        assert!(calls.iter().all(|(effects,cases)|effects.len()==1 &&
            cases.len()==1 && cases[0].effects.as_slice()==effects.as_slice()));
        assert_ne!(calls[0].0[0].path,calls[1].0[0].path,
            "one PHI successor cannot inherit the other successor's write");
    }
    #[test]
    fn incomplete_path_case_union_cannot_weaken_may_write_checks(){
        let mut summary=call_summary();
        summary.path_cases.pop();
        assert!(lower_body("step(p);",summary).is_none());
    }
    fn terminal_ref_phi(fields:&[FieldKey])->FunctionMir {
        let root=Path::root(SymbolId(101));
        let dest=Path::root(SymbolId(300));
        let mut loans=HashMap::new();
        let mut blocks=vec![BasicBlock{statements:Vec::new(),
            terminator:Terminator::Goto((1..=fields.len()).collect())}];
        let mut options=Vec::new();
        for (i,field) in fields.iter().enumerate() {
            let loan=SymbolId(201+i as u32);
            let path=root.child(field.clone());
            loans.insert(loan,path.clone());
            options.push(RefOption{loan,path:path.clone(),exclusive:false,parent:None});
            blocks.push(BasicBlock{statements:vec![Statement::Access(Event{
                op:Access::BorrowShared,path,loan:Some(loan),parent:None,token:1,
            })],terminator:Terminator::Goto(vec![fields.len()+1])});
        }
        let provenance=options.first().and_then(|first|
            options.iter().all(|candidate|candidate.path==first.path &&
                candidate.exclusive==first.exclusive && candidate.parent==first.parent)
            .then(||(first.path.clone(),false,None)));
        blocks.push(BasicBlock{statements:vec![Statement::ValuePhi{
            ty:ConstType::Ref(Box::new(blob())),
            predecessors:(1..=fields.len()).collect(),
            check:Event{op:Access::Read,path:dest,loan:None,parent:None,token:2},
            generation:Some(SymbolId(301)),provenance,alternatives:options,
        }],terminator:Terminator::Return});
        FunctionMir{entry:0,loans,blocks}
    }
    fn single_origin(fields:Vec<FieldKey>)->VerifiedReturnedReference {
        VerifiedReturnedReference{parameter:0,fields,
            ty:ConstType::Ref(Box::new(blob()))}
    }
    #[test]
    fn terminal_phi_without_declared_origin_fails_even_with_real_loan(){
        let mir=terminal_ref_phi(&[left()]);
        assert!(mir.solve_path_cases(100,&[("p".into(),mutable())],&[]).is_none());
    }
    #[test]
    fn terminal_phi_with_matching_single_origin_is_certified(){
        let mir=terminal_ref_phi(&[left()]);
        let cases=mir.solve_path_cases(100,&[("p".into(),mutable())],
            &[single_origin(vec![left()])]).expect("single proven source");
        assert_eq!(cases.len(),1);
        assert_eq!(cases[0].returned,Some(0));
    }
    #[test]
    fn terminal_phi_single_origin_cannot_hide_other_arm(){
        let mir=terminal_ref_phi(&[left(),right()]);
        assert!(mir.solve_path_cases(100,&[("p".into(),mutable())],
            &[single_origin(vec![left()])]).is_none());
    }
    #[test]
    fn terminal_phi_duplicate_origin_is_ambiguous(){
        let mir=terminal_ref_phi(&[left()]);
        let origins=[single_origin(vec![left()]),single_origin(vec![left()])];
        assert!(mir.solve_path_cases(100,&[("p".into(),mutable())],&origins).is_none());
    }
    #[test]
    fn terminal_phi_origin_must_match_reference_type_and_live_loan(){
        let mut mir=terminal_ref_phi(&[left()]);
        let mut origin=single_origin(vec![left()]);
        origin.ty=ConstType::RefMut(Box::new(blob()));
        assert!(mir.solve_path_cases(100,&[("p".into(),mutable())],
            &[origin]).is_none());
        mir.loans.clear();
        assert!(mir.solve_path_cases(100,&[("p".into(),mutable())],
            &[single_origin(vec![left()])]).is_none());
    }
    #[test]
    fn pure_cyclic_cfg_reaches_a_fixed_point(){
        let mir=FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![0,1])},
            BasicBlock{statements:vec![],terminator:Terminator::Return},
        ]};
        let cases=mir.solve_path_cases(100,&[],&[]).expect("loop converges");
        assert_eq!(cases,vec![VerifiedPathCase{effects:Vec::new(),returned:None,uninitialized:Vec::new()}]);
    }
    #[test]
    fn cyclic_write_effect_is_idempotent_not_replayed(){
        let path=Path::root(SymbolId(101)).child(left());
        let mir=FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![Statement::Access(Event{op:Access::Write,path,
                loan:None,parent:None,token:0})],terminator:Terminator::Goto(vec![0])},
            BasicBlock{statements:vec![],terminator:Terminator::Return},
        ]};
        let cases=mir.solve_path_cases(100,&[("p".into(),pair())],&[])
            .expect("finite write lattice");
        assert_eq!(cases.len(),2);
        assert!(cases.iter().any(|c|c.effects.is_empty()));
        assert!(cases.iter().any(|c|c.effects==vec![effect(vec![left()])]));
    }
    #[test]
    fn move_then_reinitialize_sibling_on_loop_is_valid(){
        let path=Path::root(SymbolId(101)).child(left());
        let mir=FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![
                Statement::Access(Event{op:Access::Move,path:path.clone(),
                    loan:None,parent:None,token:0}),
                Statement::Access(Event{op:Access::Initialize,path,
                    loan:None,parent:None,token:0}),
            ],terminator:Terminator::Goto(vec![0])},
            BasicBlock{statements:vec![],terminator:Terminator::Return},
        ]};
        let cases=mir.solve_path_cases(100,&[("p".into(),pair())],&[])
            .expect("reinitialized MovePath fixed point");
        assert!(cases.iter().any(|c|c.effects.iter().any(|e|
            e.kind==VerifiedEffectKind::Move && e.fields==vec![left()])));
    }
    #[test]
    fn move_twice_on_a_cyclic_path_fails_closed(){
        let path=Path::root(SymbolId(101)).child(left());
        let mir=FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![Statement::Access(Event{op:Access::Move,path,
                loan:None,parent:None,token:0})],terminator:Terminator::Goto(vec![0])},
            BasicBlock{statements:vec![],terminator:Terminator::Return},
        ]};
        assert!(mir.solve_path_cases(100,&[("p".into(),pair())],&[]).is_none());
    }
    #[test]
    fn call_cases_remain_correlated_across_loop_backedge(){
        let root=Path::root(SymbolId(101));
        let l=VerifiedAppliedEffect{path:root.child(left()),kind:VerifiedEffectKind::Write,alternatives:Vec::new()};
        let r=VerifiedAppliedEffect{path:root.child(right()),kind:VerifiedEffectKind::Write,alternatives:Vec::new()};
        let mir=FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![Statement::Call{name:"step".into(),token:0,
                events:Vec::new(),effects:vec![l.clone(),r.clone()],
                path_cases:vec![
                    VerifiedAppliedPathCase{effects:vec![l],returned:None,uninitialized:Vec::new()},
                    VerifiedAppliedPathCase{effects:vec![r],returned:None,uninitialized:Vec::new()},
                ]}],terminator:Terminator::Goto(vec![0])},
            BasicBlock{statements:vec![],terminator:Terminator::Return},
        ]};
        let cases=mir.solve_path_cases(100,&[("p".into(),mutable())],&[])
            .expect("finite transitive case lattice");
        assert_eq!(cases.len(),4);
        assert!(cases.iter().any(|c|c.effects.is_empty()));
        assert!(cases.iter().any(|c|c.effects.len()==1));
        assert!(cases.iter().any(|c|c.effects.len()==2));
    }
    #[test]
    fn returned_phi_after_cyclic_prefix_retains_both_sources(){
        let mut mir=terminal_ref_phi(&[left(),right()]);
        mir.blocks.insert(0,BasicBlock{statements:Vec::new(),
            terminator:Terminator::Goto(vec![0,1])});
        mir.entry=0;
        for block in mir.blocks.iter_mut().skip(1) {
            if let Terminator::Goto(targets)=&mut block.terminator {
                for target in targets.iter_mut(){*target+=1;}
            }
            for statement in &mut block.statements {
                if let Statement::ValuePhi{predecessors,..}=statement {
                    for source in predecessors{*source+=1;}
                }
            }
        }
        let origins=[single_origin(vec![left()]),single_origin(vec![right()])];
        let cases=mir.solve_path_cases(100,&[("p".into(),mutable())],&origins)
            .expect("PHI remains proven after a cyclic prefix");
        assert_eq!(cases.len(),2);
        assert!(cases.iter().any(|c|c.returned==Some(0)));
        assert!(cases.iter().any(|c|c.returned==Some(1)));
    }
    #[test]
    fn returning_phi_cannot_borrow_moved_referent(){
        let mut mir=terminal_ref_phi(&[left(),right()]);
        let path=Path::root(SymbolId(101)).child(left());
        mir.blocks[1].statements.insert(0,Statement::Access(Event{
            op:Access::Move,path,loan:None,parent:None,token:0,
        }));
        let origins=[single_origin(vec![left()]),single_origin(vec![right()])];
        assert!(mir.solve_path_cases(100,&[("p".into(),mutable())],&origins).is_none());
    }
    #[test]
    fn unrelated_partial_move_does_not_destroy_returned_phi_provenance(){
        let mut mir=terminal_ref_phi(&[left()]);
        let other=Path::root(SymbolId(101)).child(right());
        mir.blocks[1].statements.insert(0,Statement::Access(Event{
            op:Access::Move,path:other,loan:None,parent:None,token:0,
        }));
        let cases=mir.solve_path_cases(100,&[("p".into(),mutable())],
            &[single_origin(vec![left()])]).expect("sibling is independent");
        assert_eq!(cases.len(),1);
        assert_eq!(cases[0].returned,Some(0));
        assert!(cases[0].effects.iter().any(|e|e.fields==vec![right()] &&
            e.kind==VerifiedEffectKind::Move));
        assert_eq!(cases[0].uninitialized,vec![VerifiedParameterPath{
            parameter:0,fields:vec![right()],
        }],"the returned PHI remains linked to the exact moved sibling");
    }
    #[test]
    fn initialized_move_path_on_one_branch_does_not_mask_uninitialized_other(){
        let mut mir=terminal_ref_phi(&[left(),right()]);
        let right_path=Path::root(SymbolId(101)).child(right());
        mir.blocks[2].statements.insert(0,Statement::Access(Event{
            op:Access::Drop,path:right_path,loan:None,parent:None,token:0,
        }));
        let origins=[single_origin(vec![left()]),single_origin(vec![right()])];
        assert!(mir.solve_path_cases(100,&[("p".into(),mutable())],&origins).is_none());
    }
    #[test]
    fn finite_state_budget_falls_back_instead_of_dropping_paths(){
        let mut blocks=Vec::new();
        for n in 0..9 {
            let base=n*3;
            blocks.push(BasicBlock{statements:Vec::new(),
                terminator:Terminator::Goto(vec![base+1,base+2])});
            let path=Path::root(SymbolId(101)).child(FieldKey{
                aggregate:TypeId(0),field:FieldId(n as u32),
            });
            let next=if n==8 {27}else{(n+1)*3};
            blocks.push(BasicBlock{statements:vec![Statement::Access(Event{
                op:Access::Write,path,loan:None,parent:None,token:0,
            })],terminator:Terminator::Goto(vec![next])});
            blocks.push(BasicBlock{statements:Vec::new(),
                terminator:Terminator::Goto(vec![next])});
        }
        blocks.push(BasicBlock{statements:Vec::new(),terminator:Terminator::Return});
        let mir=FunctionMir{entry:0,loans:HashMap::new(),blocks};
        assert!(mir.solve_path_cases(100,&[("p".into(),pair())],&[]).is_none());
    }
    #[test]
    fn ambiguous_phi_origin_fails_closed(){
        let root=Path::root(SymbolId(101));
        let a=root.child(left());
        let mir=FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1])},
            BasicBlock{statements:vec![Statement::ValuePhi{
                ty:ConstType::Ref(Box::new(blob())),predecessors:vec![0],
                check:Event{op:Access::Read,path:Path::root(SymbolId(300)),
                    loan:None,parent:None,token:0},
                generation:Some(SymbolId(301)),provenance:None,
                alternatives:vec![RefOption{loan:SymbolId(201),path:a,exclusive:false,parent:None}],
            }],terminator:Terminator::Return},
        ]};
        assert!(mir.solve_path_cases(100,&[],&[]).is_none());
    }
}

#[cfg(test)]
mod cyclic_compound_assign_0657_fix1_tests {
    use super::*;

    fn lower(source:&str)->Option<FunctionMir> {
        let tokens=crate::syntax::lex(source).expect("valid source tokens");
        let types=HashMap::from([
            ("Tri".to_owned(),vec![("c".to_owned(),ConstType::Named("Blob".into()))]),
            ("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
        ]);
        let ids=HashMap::from([("Tri".to_owned(),TypeId(0)),("Blob".to_owned(),TypeId(1))]);
        let names=vec!["Tri".to_owned(),"Blob".to_owned()];
        let enums=HashMap::new();
        let payloads=HashMap::new();
        let methods=HashMap::new();
        let effects=HashMap::new();
        let calls=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let params=vec![("t".to_owned(),ConstType::RefMut(Box::new(ConstType::Named("Tri".into()))))];
        lower_with_verified_calls(&tokens,0..tokens.len(),&params,&schema,&[],&calls)
            .expect("MIR lowering must not produce an internal error")
    }

    #[test]
    fn cyclic_scalar_compound_assignment_has_complete_mir() {
        let mir=lower("let mut i:i64=0; while i<2 {t.c.n=11; i+=1;}")
            .expect("while with += must be fully covered by MIR");
        assert!(mir.verify().expect("CFG checker succeeds").is_empty());
    }
    #[test]
    fn immutable_scalar_compound_assignment_is_not_certified() {
        assert!(lower("let i:i64=0; i+=1;").is_none());
    }
    #[test]
    fn ill_typed_scalar_compound_assignment_is_not_certified() {
        assert!(lower("let mut i:i64=0; i+=true;").is_none());
    }
    #[test]
    fn scalar_compound_assignment_keeps_read_before_write() {
        let mir=lower("let mut i:i64=0; i+=1;").expect("MIR covers +=");
        let ops=mir.blocks.iter().flat_map(|block|block.statements.iter())
            .flat_map(|statement|statement.events())
            .map(|event|event.op).collect::<Vec<_>>();
        assert!(ops.windows(2).any(|pair|pair[0]==Access::Read && pair[1]==Access::Write),
            "compound assignment must read initialized old value before writing");
    }
}

#[cfg(test)]
mod disjunctive_interprocedural_0659_tests {
    use super::*;
    fn run(body:&str)->Option<(FunctionMir,Vec<cfg_borrow::Conflict>)>{
        let tokens=crate::syntax::lex(body).ok()?;
        let blob=ConstType::Named("Blob".into());
        let fields=HashMap::from([
            ("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
            ("Tri".to_owned(),vec![("a".to_owned(),blob.clone()),
                ("b".to_owned(),blob.clone()),("c".to_owned(),blob.clone())]),
        ]);
        let ids=HashMap::from([("Blob".to_owned(),TypeId(0)),
            ("Tri".to_owned(),TypeId(1))]);
        let names=vec!["Blob".to_owned(),"Tri".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&fields,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let mut calls=HashMap::new();
        let shared=ConstType::Ref(Box::new(blob.clone()));
        let mutable=ConstType::RefMut(Box::new(blob.clone()));
        for (name,parameters) in [
            ("inspect",vec![shared.clone()]),
            ("change",vec![mutable.clone()]),
            ("read_both",vec![shared.clone(),shared]),
            ("mixed",vec![mutable.clone(),ConstType::Ref(Box::new(blob.clone()))]),
            ("consume",vec![blob.clone()])
        ] {
            calls.insert(name.to_owned(),VerifiedCallSummary{
                parameters,field_writes:vec![],parameter_effects:vec![],
                returned:None,returned_alternatives:vec![],path_cases:vec![]});
        }
        let n=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        calls.insert("set_n".into(),VerifiedCallSummary{
            parameters:vec![mutable],
            field_writes:vec![VerifiedFieldWrite{parameter:0,fields:vec![n]}],
            parameter_effects:vec![VerifiedParameterEffect{parameter:0,
                fields:vec![n],kind:VerifiedEffectKind::Write}],
            returned:None,returned_alternatives:vec![],path_cases:vec![]});
        let mir=lower_with_verified_calls(&tokens,0..tokens.len(),&[],
            &schema,&[],&calls).ok()??;
        let errors=mir.verify().ok()?;
        Some((mir,errors))
    }
    const OWNER:&str="let mut p:Tri=Tri{a:Blob{n:1},b:Blob{n:2},c:Blob{n:3}};";
    #[test]
    fn shared_disjunctive_argument_is_certified_on_all_paths(){
        let src=format!("{OWNER} let r=if true{{&p.a}}else{{&p.b}};inspect(r);");
        assert!(run(&src).expect("complete MIR").1.is_empty());
    }
    #[test]
    fn both_shared_aliases_are_legal(){
        let src=format!("{OWNER} let r=if true{{&p.a}}else{{&p.b}};read_both(r,&p.a);");
        assert!(run(&src).expect("shared call").1.is_empty());
    }
    #[test]
    fn live_disjunctive_origin_rejects_move(){
        for field in ["a","b"]{
            let src=format!("{OWNER} let r=if true{{&p.a}}else{{&p.b}};consume(p.{field});inspect(r);");
            assert!(!run(&src).expect("complete ownership MIR").1.is_empty());
        }
    }
    #[test]
    fn independent_third_field_can_be_moved(){
        let src=format!("{OWNER} let r=if true{{&p.a}}else{{&p.b}};consume(p.c);inspect(r);");
        assert!(run(&src).expect("separate paths").1.is_empty());
    }
    #[test]
    fn shared_phi_cannot_upgrade_to_mutable_call(){
        let src=format!("{OWNER} let r=if true{{&p.a}}else{{&p.b}};change(r);");
        assert!(run(&src).is_none());
    }
    #[test]
    fn exclusive_disjunctive_phi_can_reborrow_for_call(){
        let src=format!("{OWNER} let r=if true{{&mut p.a}}else{{&mut p.b}};change(r);");
        let (mir,errors)=run(&src).expect("exclusive PHI");
        assert!(errors.is_empty(),"{errors:?}");
        assert!(mir.blocks.iter().flat_map(|b|&b.statements).any(|s|
            matches!(s,Statement::Call{name,events,..} if name=="change" &&
                events.iter().any(|e|e.op==Access::Write && e.loan.is_some()))));
    }
    #[test]
    fn exclusive_disjunctive_phi_can_prove_projected_write(){
        let src=format!("{OWNER} let r=if true{{&mut p.a}}else{{&mut p.b}};set_n(r);");
        let (mir,errors)=run(&src).expect("write via PHI");
        assert!(errors.is_empty(),"{errors:?}");
        assert!(mir.blocks.iter().flat_map(|b|&b.statements).any(|s|
            matches!(s,Statement::Call{name,effects,..} if name=="set_n" &&
                effects.iter().any(|e|e.kind==VerifiedEffectKind::Write))));
    }
    #[test]
    fn exclusive_phi_conflicts_with_overlapping_shared_argument(){
        let src=format!("{OWNER} let r=if true{{&mut p.a}}else{{&mut p.b}};mixed(r,&p.a);");
        let result=run(&src);
        assert!(result.is_none() || !result.unwrap().1.is_empty());
    }
    #[test]
    fn mutable_phi_cannot_move_potential_referent(){
        let src=format!("{OWNER} let r=if true{{&mut p.a}}else{{&mut p.b}};consume(p.b);change(r);");
        assert!(!run(&src).expect("MIR must reject the move").1.is_empty());
    }
}

#[cfg(test)]
mod disjunctive_alias_proof_audit_0659_tests {
    use super::*;
    fn source()->(FunctionMir,SymbolId,Path,Path){
        let owner=SymbolId(17);
        let reference=SymbolId(18);
        let phi_generation=SymbolId(50);
        let a=Path::root(owner).child(FieldKey{aggregate:TypeId(1),field:FieldId(0)});
        let b=Path::root(owner).child(FieldKey{aggregate:TypeId(1),field:FieldId(1)});
        let candidates=vec![RefOption{loan:SymbolId(30),path:a.clone(),exclusive:true,parent:None},
            RefOption{loan:SymbolId(31),path:b.clone(),exclusive:true,parent:None}];
        let n=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let effect=VerifiedAppliedEffect{path:Path::root(reference),
            kind:VerifiedEffectKind::Write,
            alternatives:vec![a.child(n),b.child(n)]};
        let mir=FunctionMir{entry:0,loans:HashMap::from([
            (SymbolId(30),a.clone()),(SymbolId(31),b.clone())]),blocks:vec![
            BasicBlock{statements:vec![Statement::ValuePhi{
                ty:ConstType::RefMut(Box::new(ConstType::Named("Blob".into()))),
                predecessors:vec![1,2],check:Event{op:Access::Read,
                    path:Path::root(reference),loan:None,parent:None,token:0},
                generation:Some(phi_generation),provenance:None,alternatives:candidates,
            },Statement::Call{name:"set_n".into(),token:0,
                events:vec![Event{op:Access::Write,path:Path::root(reference),
                    loan:Some(phi_generation),parent:None,token:0}],
                effects:vec![effect],path_cases:vec![]}],terminator:Terminator::Return},
        ]};
        (mir,phi_generation,a,b)
    }
    #[test]
    fn complete_disjunctive_effects_have_symbolic_owner_and_exact_paths(){
        let (mir,_,_,_)=source();
        assert!(mir.validate_interprocedural_alias_proofs().is_ok());
    }
    #[test]
    fn omitted_phi_effect_alternative_fails_closed(){
        let (mut mir,_,_,_)=source();
        let Statement::Call{effects,..}=&mut mir.blocks[0].statements[1]else{panic!()};
        effects[0].alternatives.pop();
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn forged_phi_effect_field_suffix_fails_closed(){
        let (mut mir,_,_,_)=source();
        let Statement::Call{effects,..}=&mut mir.blocks[0].statements[1]else{panic!()};
        effects[0].alternatives[1].fields.push(FieldKey{aggregate:TypeId(4),field:FieldId(9)});
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn wrong_phi_generation_cannot_authorize_write(){
        let (mut mir,_,_,_)=source();
        let Statement::Call{events,..}=&mut mir.blocks[0].statements[1]else{panic!()};
        events[0].loan=Some(SymbolId(99));
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn move_through_disjunctive_mutable_loan_is_rejected(){
        let (mut mir,_,_,_)=source();
        let Statement::Call{effects,..}=&mut mir.blocks[0].statements[1]else{panic!()};
        effects[0].kind=VerifiedEffectKind::Move;
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
}


#[cfg(test)]
mod composed_phi_call_chain_0660_tests {
    use super::*;

    fn lower_with_forwarders(src:&str)->FunctionMir {
        let tokens=crate::syntax::lex(src).expect("valid test syntax");
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let mut calls=HashMap::new();
        for (name,exclusive) in [("forward",false),("forward_mut",true)] {
            let ty=if exclusive {
                ConstType::RefMut(Box::new(ConstType::I64))
            }else{
                ConstType::Ref(Box::new(ConstType::I64))
            };
            calls.insert(name.to_owned(),VerifiedCallSummary{
                parameters:vec![ty.clone()],field_writes:vec![],
                parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{
                    parameter:0,fields:vec![],ty,
                }),returned_alternatives:vec![],path_cases:vec![],
            });
        }
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("MIR lowering should not report internal error")
            .expect("complete source-PHI / return-PHI lowering required")
    }
    fn checked(src:&str)->Vec<cfg_borrow::Conflict> {
        lower_with_forwarders(src).verify().expect("valid MIR identities")
    }
    #[test]
    fn shared_two_hop_return_preserves_both_exact_owners(){
        let mir=lower_with_forwarders("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let s=forward(r);let t=forward(s);let v=*t;");
        assert!(mir.verify().unwrap().is_empty());
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|{
            if let Statement::ValuePhi{alternatives,..}=stmt {Some(alternatives)}else{None}
        }).collect::<Vec<_>>();
        assert_eq!(phis.len(),3);
        assert_eq!(phis.iter().map(|group|group.len()).collect::<Vec<_>>(),vec![2,2,2]);
        for pair in phis.windows(2){
            for (before,after) in pair[0].iter().zip(pair[1].iter()){
                assert_eq!(after.parent,Some(before.loan));
                assert_eq!(after.path,before.path);
                assert_ne!(after.loan,before.loan);
            }
        }
    }
    #[test]
    fn shared_chain_forbids_write_to_either_live_source(){
        for bad in ["a=7;","b=8;"]{
            let src=format!("let mut a:i64=1;let mut b:i64=2;let r=if true{{&a}}else{{&b}};let s=forward(r);let t=forward(s);{bad}let v=*t;");
            assert!(!checked(&src).is_empty(),"loan protection failed for {bad}");
        }
    }
    #[test]
    fn mutable_two_hop_return_preserves_exclusive_loan_parents(){
        let mir=lower_with_forwarders("let mut a:i64=1;let mut b:i64=2;let r=if true{&mut a}else{&mut b};let s=forward_mut(r);let t=forward_mut(s);*t=6;");
        assert!(mir.verify().unwrap().is_empty());
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|{
            if let Statement::ValuePhi{alternatives,..}=stmt {Some(alternatives)}else{None}
        }).collect::<Vec<_>>();
        assert_eq!(phis.len(),3);
        for pair in phis.windows(2) {
            for (before,after) in pair[0].iter().zip(pair[1].iter()) {
                assert!(before.exclusive && after.exclusive);
                assert_eq!(after.parent,Some(before.loan));
            }
        }
    }
    #[test]
    fn mutable_chain_rejects_conflicting_source_write(){
        let src="let mut a:i64=1;let mut b:i64=2;let r=if true{&mut a}else{&mut b};let s=forward_mut(r);let t=forward_mut(s);a=8;*t=6;";
        assert!(!checked(src).is_empty());
    }
    #[test]
    fn forged_child_loan_cannot_retarget_other_phi_branch(){
        let mut mir=lower_with_forwarders("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let s=forward(r);let v=*s;");
        let mut seen=0;
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()) {
            if let Statement::ValuePhi{alternatives,..}=stmt {
                seen+=1;
                if seen==2 {alternatives[1].path=alternatives[0].path.clone();break;}
            }
        }
        assert_eq!(seen,2);
        assert!(mir.verify().is_err(),"a forged cross-branch result origin must not verify");
    }
    #[test]
    fn forged_return_parent_is_not_accepted(){
        let mut mir=lower_with_forwarders("let a:i64=1;let b:i64=2;let r=if true{&a}else{&b};let s=forward(r);let v=*s;");
        let mut count=0;
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()) {
            if let Statement::ValuePhi{alternatives,..}=stmt {
                count+=1;
                if count==2 {alternatives[1].parent=Some(alternatives[0].loan);break;}
            }
        }
        assert_eq!(count,2);
        assert!(mir.verify().is_err(),"wrong source loan cannot authenticate a return");
    }
}

#[cfg(test)]
mod multiparameter_phi_composition_0661_tests {
    use super::*;

    fn lower(src:&str)->Option<FunctionMir> {
        let tokens=crate::syntax::lex(src).expect("valid test syntax");
        let types=HashMap::new();let ids=HashMap::new();let names=Vec::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let shared=ConstType::Ref(Box::new(ConstType::I64));
        let mutable=ConstType::RefMut(Box::new(ConstType::I64));
        let mut calls=HashMap::new();
        for (name,parameters,origin) in [
            ("first",vec![shared.clone(),shared.clone()],0),
            ("second",vec![shared.clone(),shared.clone()],1),
            ("second_mut",vec![shared.clone(),mutable.clone()],1),
            ("two_mut",vec![mutable.clone(),mutable.clone()],1),
            ("bad_index",vec![shared.clone(),shared.clone()],2),
        ] {
            let result=parameters.get(origin).cloned().unwrap_or(shared.clone());
            calls.insert(name.to_owned(),VerifiedCallSummary{
                parameters,field_writes:vec![],parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{
                    parameter:origin,fields:vec![],ty:result,
                }),returned_alternatives:vec![],path_cases:vec![],
            });
        }
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("no internal lowering error")
    }
    fn valid(src:&str)->FunctionMir {
        let mir=lower(src).expect("verified multi-input PHI should lower completely");
        assert!(mir.verify().expect("valid MIR identities").is_empty());
        mir
    }
    fn source()->&'static str {
        "let a:i64=1;let b:i64=2;let c:i64=3;let extra=&c;let r=if true{&a}else{&b};"
    }
    fn output(mir:&FunctionMir)->Vec<RefOption> {
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|match s {
            Statement::ValuePhi{alternatives,..} if alternatives.len()==2=>Some(alternatives),
            _=>None,
        }).last().expect("returned reference PHI").clone()
    }
    #[test]
    fn second_reference_parameter_can_forward_a_disjunctive_phi(){
        let mir=valid(&format!("{}let s=second(extra,r);let n=*s;",source()));
        let option=output(&mir);
        assert_eq!(option.len(),2);
        assert_ne!(option[0].path,option[1].path);
        assert!(option.iter().all(|o|o.parent.is_some() && !o.exclusive));
    }
    #[test]
    fn first_parameter_still_preserves_exact_phi_parents(){
        let mir=valid(&format!("{}let s=first(r,extra);let n=*s;",source()));
        let all=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::ValuePhi{alternatives,..}=s {
                Some(alternatives.clone())
            }else{None}).collect::<Vec<_>>();
        assert_eq!(all.len(),2);
        for (original,result) in all[0].iter().zip(&all[1]) {
            assert_eq!(result.parent,Some(original.loan));
            assert_eq!(result.path,original.path);
        }
    }
    #[test]
    fn two_different_parameter_positions_compose_across_calls(){
        let mir=valid(&format!("{}let s=second(extra,r);let t=first(s,extra);let n=*t;",source()));
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::ValuePhi{alternatives,..}=s {
                Some(alternatives)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),3);
        for pair in phis.windows(2) {
            for (a,b) in pair[0].iter().zip(pair[1]) {
                assert_eq!(b.parent,Some(a.loan));
                assert_eq!(b.path,a.path);
            }
        }
    }
    #[test]
    fn extra_shared_reference_does_not_block_disjoint_mutable_phi(){
        let mir=valid("let mut a:i64=1;let mut b:i64=2;let c:i64=3;let extra=&c;let r=if true{&mut a}else{&mut b};let s=second_mut(extra,r);*s=4;");
        assert!(output(&mir).iter().all(|o|o.exclusive));
    }
    #[test]
    fn forwarded_mutable_phi_still_protects_every_source(){
        for field in ["a","b"] {
            let src=format!("let mut a:i64=1;let mut b:i64=2;let c:i64=3;let extra=&c;let r=if true{{&mut a}}else{{&mut b}};let s=second_mut(extra,r);{field}=9;*s=4;");
            let mir=lower(&src).expect("full MIR should retain every borrowed path");
            assert!(mir.verify().map_or(true,|conflicts|!conflicts.is_empty()));
        }
    }
    #[test]
    fn duplicated_exclusive_phi_cannot_be_two_disjoint_arguments(){
        let src="let mut a:i64=1;let mut b:i64=2;let r=if true{&mut a}else{&mut b};let s=two_mut(r,r);*s=4;";
        let result=lower(src);
        assert!(result.is_none() || result.unwrap().verify()
            .map_or(true,|conflicts|!conflicts.is_empty()));
    }
    #[test]
    fn earlier_shared_phi_can_be_an_unreturned_readonly_argument(){
        let src="let a:i64=1;let b:i64=2;let c:i64=3;let d:i64=4;let r=if true{&a}else{&b};let s=if true{&c}else{&d};let t=second(r,s);let n=*t;";
        let mir=valid(src);
        let groups=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter(|s|matches!(s,Statement::ValuePhi{..})).count();
        assert_eq!(groups,3,"both input PHIs and output PHI are still explicit");
    }
    #[test]
    fn independent_shared_phi_inputs_survive_two_forwarding_hops(){
        let src="let a:i64=1;let b:i64=2;let c:i64=3;let d:i64=4;let r=if true{&a}else{&b};let s=if true{&c}else{&d};let t=second(r,s);let u=first(t,r);let n=*u;";
        let mir=valid(src);
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|statement|if let Statement::ValuePhi{alternatives,..}=statement {
                Some(alternatives)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),4);
        for pair in [(1usize,2usize),(2,3)] {
            for (source,dest) in phis[pair.0].iter().zip(phis[pair.1].iter()) {
                assert_eq!(dest.parent,Some(source.loan));
                assert_eq!(dest.path,source.path);
            }
        }
    }
    #[test]
    fn unrelated_shared_phi_must_remain_live_until_call(){
        for owner in ["a","b"] {
            let src=format!("let mut a:i64=1;let mut b:i64=2;let c:i64=3;let d:i64=4;let r=if true{{&a}}else{{&b}};let s=if true{{&c}}else{{&d}};{owner}=9;let t=second(r,s);let n=*t;");
            let rejected=match lower(&src) {
                None=>true,
                Some(mir)=>mir.verify().map_or(true,|conflicts|!conflicts.is_empty()),
            };
            assert!(rejected,"missed shared loan on {owner}");
        }
    }
    #[test]
    fn unrelated_mutable_phi_from_older_merge_fails_closed(){
        let src="let mut a:i64=1;let mut b:i64=2;let mut c:i64=3;let mut d:i64=4;let r=if true{&mut a}else{&mut b};let s=if true{&mut c}else{&mut d};let t=two_mut(r,s);*t=7;";
        assert!(lower(src).is_none(),"independent exclusive loans need stronger CFG correlation");
    }
    #[test]
    fn earlier_returned_phi_cannot_be_guessed_from_a_later_join(){
        let src="let a:i64=1;let b:i64=2;let c:i64=3;let d:i64=4;let r=if true{&a}else{&b};let s=if true{&c}else{&d};let t=first(r,s);let n=*t;";
        assert!(lower(src).is_none(),"a returned earlier PHI needs an explicit relational CFG proof");
    }
    #[test]
    fn malformed_return_parameter_index_fails_closed(){
        let src=format!("{}let s=bad_index(extra,r);let n=*s;",source());
        assert!(lower(&src).is_none());
    }
    #[test]
    fn projected_field_result_retains_move_path_and_parent_loan(){
        let tokens=crate::syntax::lex("let p:Tri=Tri{a:Blob{n:1},b:Blob{n:2},c:Blob{n:3}};let spare=&p.c;let r=if true{&p.a}else{&p.b};let s=project(spare,r);let n=*s;").unwrap();
        let blob=ConstType::Named("Blob".into());
        let types=HashMap::from([
            ("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
            ("Tri".to_owned(),vec![("a".to_owned(),blob.clone()),
                ("b".to_owned(),blob.clone()),("c".to_owned(),blob.clone())]),
        ]);
        let ids=HashMap::from([("Blob".into(),TypeId(0)),("Tri".into(),TypeId(1))]);
        let names=vec!["Blob".to_owned(),"Tri".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let calls=HashMap::from([("project".to_owned(),VerifiedCallSummary{
            parameters:vec![ConstType::Ref(Box::new(blob.clone())),
                ConstType::Ref(Box::new(blob))],
            returned:Some(VerifiedReturnedReference{parameter:1,
                fields:vec![FieldKey{aggregate:TypeId(0),field:FieldId(0)}],
                ty:ConstType::Ref(Box::new(ConstType::I64))}),
            field_writes:vec![],parameter_effects:vec![],
            returned_alternatives:vec![],path_cases:vec![],
        })]);
        let mir=lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("verified projected call should not fail internally")
            .expect("complete typed MIR projection");
        assert!(mir.verify().unwrap().is_empty());
        let options=output(&mir);
        assert_eq!(options.len(),2);
        assert!(options.iter().all(|o|o.path.fields.len()==2 &&
            o.path.fields[1]==FieldKey{aggregate:TypeId(0),field:FieldId(0)} &&
            o.parent.is_some()));
    }
    #[test]
    fn live_extra_shared_alias_blocks_mutable_phi_conflict(){
        let src="let mut a:i64=1;let mut b:i64=2;let extra=&a;let r=if true{&mut a}else{&mut b};let s=second_mut(extra,r);let n=*extra;*s=4;";
        let result=lower(src);
        assert!(result.is_none() || result.unwrap().verify()
            .map_or(true,|conflicts|!conflicts.is_empty()));
    }
}

#[cfg(test)]
mod relational_multi_origin_phi_0662_tests {
    use super::*;

    fn lower(body:&str,effectful:bool)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(body).expect("valid MIR test syntax");
        let blob=ConstType::Named("Blob".into());
        let types=HashMap::from([
            ("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
            ("Tri".to_owned(),vec![("a".to_owned(),blob.clone()),
                ("b".to_owned(),blob.clone()),("c".to_owned(),blob.clone())]),
        ]);
        let ids=HashMap::from([("Blob".into(),TypeId(0)),("Tri".into(),TypeId(1))]);
        let names=vec!["Blob".to_owned(),"Tri".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let ref_ty=if effectful {ConstType::RefMut(Box::new(blob))}
            else{ConstType::Ref(Box::new(blob))};
        let origins=(0..2).map(|parameter|VerifiedReturnedReference{
            parameter,fields:vec![],ty:ref_ty.clone(),
        }).collect::<Vec<_>>();
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let parameter_effects=if effectful{(0..2).map(|parameter|
            VerifiedParameterEffect{parameter,fields:vec![field],
                kind:VerifiedEffectKind::Write}).collect::<Vec<_>>()}
            else{Vec::new()};
        let field_writes=if effectful{(0..2).map(|parameter|
            VerifiedFieldWrite{parameter,fields:vec![field]}).collect::<Vec<_>>()}
            else{Vec::new()};
        let path_cases=if effectful {(0..2).map(|parameter|VerifiedPathCase{
            effects:vec![VerifiedParameterEffect{parameter,fields:vec![field],
                kind:VerifiedEffectKind::Write}],
            returned:Some(parameter),uninitialized:vec![],
        }).collect::<Vec<_>>()}else{Vec::new()};
        let summary=VerifiedCallSummary{
            parameters:vec![ref_ty.clone(),ref_ty.clone()],returned:None,
            returned_alternatives:origins.clone(),field_writes,parameter_effects,path_cases,
        };
        let mut calls=HashMap::from([("choose".into(),summary)]);
        calls.insert("relay".to_owned(),VerifiedCallSummary{
            parameters:vec![ref_ty.clone(),ref_ty],
            field_writes:vec![],parameter_effects:vec![],
            returned:Some(VerifiedReturnedReference{parameter:0,
                fields:vec![],ty:origins[0].ty.clone()}),
            returned_alternatives:vec![],path_cases:vec![],
        });
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("no MIR implementation error")
    }
    const OWNER:&str="let mut t:Tri=Tri{a:Blob{n:1},b:Blob{n:2},c:Blob{n:3}};";
    fn successful(body:&str,effectful:bool)->FunctionMir{
        let mir=lower(body,effectful).expect("complete relational PHI MIR");
        let conflicts=mir.verify().expect("valid relational PHI graph");
        assert!(conflicts.is_empty(),"{conflicts:?}");
        mir
    }
    fn output(mir:&FunctionMir)->Vec<RefOption>{
        mir.blocks.iter().flat_map(|block|block.statements.iter())
            .filter_map(|stmt|if let Statement::ValuePhi{alternatives,..}=stmt {
                Some(alternatives.clone())
            }else{None}).last().expect("output PHI").clone()
    }
    #[test]
    fn one_input_phi_two_return_origins_have_four_distinct_loans(){
        let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=choose(r,extra);let n=s.n;");
        let mir=successful(&body,false);
        let result=output(&mir);
        assert_eq!(result.len(),4);
        assert_eq!(result.iter().map(|r|r.loan).collect::<HashSet<_>>().len(),4);
        assert!(result.iter().all(|r|r.parent.is_some() && !r.exclusive));
        assert_ne!(result[0].path,result[2].path);
        assert_eq!(result[1].path,result[3].path);
        assert_ne!(result[0].path,result[1].path);
        assert_ne!(result[2].path,result[3].path);
    }
    #[test]
    fn returning_second_parameter_retains_edge_specific_parent(){
        let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=choose(extra,r);let n=s.n;");
        let mir=successful(&body,false);
        let result=output(&mir);
        assert_eq!(result.len(),4);
        assert_eq!(result[0].path,result[2].path);
        assert_ne!(result[1].path,result[3].path);
        assert_ne!(result[1].parent,result[3].parent);
        assert!(result.iter().all(|r|r.parent.is_some()));
    }
    #[test]
    fn repeated_returning_call_keeps_all_candidates(){
        let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=choose(r,extra);let n=s.n;");
        let mir=successful(&body,false);
        let count=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter(|s|matches!(s,Statement::Call{name,..} if name=="choose")).count();
        assert_eq!(count,4,"one invocation on each mutually exclusive MIR edge");
        let selected=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::Call{path_cases,..}=s {
                Some(path_cases)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(selected.len(),4);
    }
    #[test]
    fn composed_return_phi_forwards_through_another_call(){
        let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=choose(r,extra);let v=relay(s,extra);let n=v.n;");
        let mir=successful(&body,false);
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::ValuePhi{alternatives,..}=s {
                Some(alternatives.clone())
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),3);
        assert_eq!(phis[1].len(),4);
        assert_eq!(phis[2].len(),4);
        for (before,after) in phis[1].iter().zip(&phis[2]) {
            assert_eq!(after.path,before.path);
            assert_eq!(after.parent,Some(before.loan));
        }
    }
    #[test]
    fn move_of_independent_field_remains_legal(){
        let body=format!("{OWNER}let other:Blob=Blob{{n:7}};let extra=&other;let r=if true{{&t.a}}else{{&t.b}};let s=choose(r,extra);let spare:Blob=t.c;let n=s.n;");
        let mir=successful(&body,false);
        assert_eq!(output(&mir).len(),4);
    }
    #[test]
    fn projected_return_paths_keep_type_qualified_field_ids(){
        let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=project_choice(r,extra);let n=*s;");
        let tokens=crate::syntax::lex(&body).unwrap();
        let blob=ConstType::Named("Blob".into());
        let types=HashMap::from([
            ("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
            ("Tri".to_owned(),vec![("a".to_owned(),blob.clone()),
                ("b".to_owned(),blob.clone()),("c".to_owned(),blob.clone())]),
        ]);
        let ids=HashMap::from([("Blob".into(),TypeId(0)),("Tri".into(),TypeId(1))]);
        let names=vec!["Blob".to_owned(),"Tri".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let n=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let calls=HashMap::from([("project_choice".to_owned(),VerifiedCallSummary{
            parameters:vec![ConstType::Ref(Box::new(blob.clone())),
                ConstType::Ref(Box::new(blob))],returned:None,
            returned_alternatives:(0..2).map(|parameter|VerifiedReturnedReference{
                parameter,fields:vec![n],ty:ConstType::Ref(Box::new(ConstType::I64)),
            }).collect(),
            field_writes:vec![],parameter_effects:vec![],path_cases:vec![],
        })]);
        let mir=lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("valid MIR").expect("complete type-qualified projection");
        assert!(mir.verify().unwrap().is_empty());
        let cases=output(&mir);
        assert_eq!(cases.len(),4);
        assert!(cases.iter().all(|r|r.path.fields.last()==Some(&n) &&
            r.path.fields.len()==2 && r.parent.is_some()));
    }
    #[test]
    fn broken_output_phi_loan_identity_is_rejected(){
        let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=choose(r,extra);let n=s.n;");
        let mut mir=successful(&body,false);
        let phi=mir.blocks.iter_mut().flat_map(|block|block.statements.iter_mut())
            .filter_map(|stmt|if let Statement::ValuePhi{alternatives,..}=stmt {
                (alternatives.len()==4).then_some(alternatives)
            }else{None}).last().expect("relational output PHI");
        phi[3].loan=phi[0].loan;
        assert!(mir.verify().is_err(),"reusing a PHI loan must fail closed");
    }
    #[test]
    fn both_possible_pointees_remain_protected(){
        for field in ["a","b"] {
            let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=choose(r,extra);let moved:Blob=t.{field};let n=s.n;");
            let result=lower(&body,false);
            assert!(result.is_none() || result.unwrap().verify()
                .map_or(true,|conflicts|!conflicts.is_empty()),"borrow escaped for {field}");
        }
    }
    #[test]
    fn effectful_return_cases_keep_different_field_writes(){
        let body=format!("{OWNER}let extra=&mut t.c;let r=if true{{&mut t.a}}else{{&mut t.b}};let s=choose(r,extra);s.n=4;");
        let mir=successful(&body,true);
        let call_cases=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::Call{effects,path_cases,..}=s {
                Some((effects,path_cases))
            }else{None}).collect::<Vec<_>>();
        assert_eq!(call_cases.len(),4);
        assert!(call_cases.iter().all(|(effects,cases)|
            effects.len()==1 && effects[0].kind==VerifiedEffectKind::Write &&
            cases.len()==1 && cases[0].effects.len()==1));
    }
    #[test]
    fn effectful_call_rejects_overlap_with_live_shared_alias(){
        let body=format!("{OWNER}let witness=&t.a;let extra=&mut t.c;let r=if true{{&mut t.a}}else{{&mut t.b}};let s=choose(r,extra);let x=witness.n;s.n=4;");
        let result=lower(&body,true);
        assert!(result.is_none() || result.unwrap().verify()
            .map_or(true,|conflicts|!conflicts.is_empty()));
    }
    #[test]
    fn source_and_result_phis_share_exact_predecessor_edges(){
        let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=choose(r,extra);let n=s.n;");
        let mir=successful(&body,false);
        for block in &mir.blocks {
            for stmt in &block.statements {
                if let Statement::ValuePhi{predecessors,alternatives,..}=stmt {
                    if !alternatives.is_empty() {
                        assert_eq!(predecessors.len(),alternatives.len());
                    }
                }
            }
        }
    }
    #[test]
    fn return_origin_and_write_effects_remain_paired(){
        let body=format!("{OWNER}let extra=&mut t.c;let r=if true{{&mut t.a}}else{{&mut t.b}};let s=choose(r,extra);s.n=4;");
        let mir=successful(&body,true);
        let outcome=output(&mir);
        let branches=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::Call{name,effects,..}=s {
                (name=="choose").then_some(effects)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(branches.len(),4);
        assert_eq!(outcome.len(),branches.len());
        for (index,(result,effects)) in outcome.iter().zip(branches).enumerate() {
            let target=&effects[0].path;
            assert_eq!(target.fields.last(),Some(&FieldKey{
                aggregate:TypeId(0),field:FieldId(0)}));
            assert_eq!(target.owner,result.path.owner);
            assert_eq!(&target.fields[..target.fields.len()-1],result.path.fields.as_slice());
            assert!(index<4);
        }
    }
    #[test]
    fn fake_parent_identity_cannot_certify_returned_phi(){
        let body=format!("{OWNER}let extra=&t.c;let r=if true{{&t.a}}else{{&t.b}};let s=choose(r,extra);let n=s.n;");
        let mut mir=successful(&body,false);
        let phi=mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut())
            .filter_map(|s|if let Statement::ValuePhi{alternatives,..}=s {
                (alternatives.len()==4).then_some(alternatives)
            }else{None}).last().expect("returned PHI");
        phi[1].parent=Some(SymbolId(u32::MAX));
        assert!(mir.verify().is_err() || mir.verify().unwrap().len()>0);
    }
    #[test]
    fn malformed_or_missing_correlated_effect_cases_fail_closed(){
        let body=format!("{OWNER}let extra=&mut t.c;let r=if true{{&mut t.a}}else{{&mut t.b}};let s=choose(r,extra);s.n=4;");
        let tokens=crate::syntax::lex(&body).unwrap();
        let types=HashMap::from([
            ("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)]),
            ("Tri".to_owned(),vec![("a".to_owned(),ConstType::Named("Blob".into())),
                ("b".to_owned(),ConstType::Named("Blob".into())),
                ("c".to_owned(),ConstType::Named("Blob".into()))]),
        ]);
        let ids=HashMap::from([("Blob".into(),TypeId(0)),("Tri".into(),TypeId(1))]);
        let names=vec!["Blob".to_owned(),"Tri".to_owned()];
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&HashMap::new(),enum_payloads:&HashMap::new(),
            types:&types,type_ids:&ids,type_names:&names,methods:&methods,
            verified_effects:&effects};
        let blob=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let bad=VerifiedCallSummary{
            parameters:vec![blob.clone(),blob.clone()],returned:None,
            returned_alternatives:(0..2).map(|parameter|VerifiedReturnedReference{
                parameter,fields:vec![],ty:blob.clone(),
            }).collect(),
            field_writes:vec![VerifiedFieldWrite{parameter:0,fields:vec![field]}],
            parameter_effects:vec![VerifiedParameterEffect{parameter:0,
                fields:vec![field],kind:VerifiedEffectKind::Write}],
            path_cases:vec![VerifiedPathCase{effects:vec![],returned:Some(0),
                uninitialized:vec![]}],
        };
        let calls=HashMap::from([("choose".into(),bad)]);
        let result=lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls);
        assert!(result.is_err() || result.ok().flatten().is_none());
    }
    #[test]
    fn aliased_mutable_actuals_never_become_disjoint_on_return(){
        let body=format!("{OWNER}let extra=&mut t.c;let r=if true{{&mut t.a}}else{{&mut t.b}};let s=choose(r,r);s.n=4;");
        let result=lower(&body,true);
        assert!(result.is_none() || result.unwrap().verify()
            .map_or(true,|conflicts|!conflicts.is_empty()));
    }
}

#[cfg(test)]
mod independent_phi_effects_0663_tests {
    use super::*;

    fn lower(body:&str,effectful:bool,mutate_summary:impl FnOnce(&mut VerifiedCallSummary))
        ->Option<FunctionMir> {
        let tokens=crate::syntax::lex(body).expect("test syntax");
        let blob=ConstType::Named("Blob".into());
        let types=HashMap::from([
            ("Blob".into(),vec![("n".into(),ConstType::I64)]),
            ("Tri".into(),vec![("a".into(),blob.clone()),
                ("b".into(),blob.clone()),("c".into(),blob.clone())]),
        ]);
        let ids=HashMap::from([("Blob".into(),TypeId(0)),("Tri".into(),TypeId(1))]);
        let names=vec!["Blob".into(),"Tri".into()];
        let methods=HashMap::new();let effects=HashMap::new();
        let enums=HashMap::new();let payloads=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let main_ref=if effectful {ConstType::RefMut(Box::new(blob.clone()))}
            else{ConstType::Ref(Box::new(blob.clone()))};
        let old_ref=ConstType::Ref(Box::new(blob));
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let parameter_effects=if effectful{(0..2).map(|parameter|
            VerifiedParameterEffect{parameter,fields:vec![field],
                kind:VerifiedEffectKind::Write}).collect()}else{Vec::new()};
        let field_writes=if effectful{(0..2).map(|parameter|
            VerifiedFieldWrite{parameter,fields:vec![field]}).collect()}else{Vec::new()};
        let path_cases=if effectful{(0..2).map(|parameter|VerifiedPathCase{
            effects:vec![VerifiedParameterEffect{parameter,fields:vec![field],
                kind:VerifiedEffectKind::Write}],
            returned:Some(parameter),uninitialized:vec![],
        }).collect()}else{Vec::new()};
        let mut summary=VerifiedCallSummary{
            parameters:vec![main_ref.clone(),main_ref.clone(),old_ref],
            returned:None,
            returned_alternatives:(0..2).map(|parameter|VerifiedReturnedReference{
                parameter,fields:vec![],ty:main_ref.clone(),
            }).collect(),
            field_writes,parameter_effects,path_cases,
        };
        mutate_summary(&mut summary);
        let calls=HashMap::from([("choose".into(),summary)]);
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("no MIR implementation error")
    }
    fn source(effectful:bool)->String{
        let borrow=if effectful{"&mut"}else{"&"};
        format!("let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};\
            let mut q:Blob=Blob{{n:7}};let x:Blob=Blob{{n:8}};let y:Blob=Blob{{n:9}};\
            let older=if true{{&x}}else{{&y}};\
            let extra={borrow} q;\
            let recent=if true{{{borrow} t.a}}else{{{borrow} t.b}};")
    }
    fn checked(body:&str,effectful:bool)->FunctionMir{
        let mir=lower(body,effectful,|_|{}).expect("complete independent PHI MIR");
        let conflicts=mir.verify().expect("well formed independent PHIs");
        assert!(conflicts.is_empty(),"{conflicts:?}");mir
    }
    fn output(mir:&FunctionMir)->Vec<RefOption>{
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::ValuePhi{alternatives,..}=s{Some(alternatives.clone())}
            else{None}).last().expect("output PHI")
    }
    #[test]
    fn earlier_independent_shared_phi_remains_distinct_from_relational_product(){
        let src=format!("{}let output=choose(recent,extra,older);let n=output.n;",source(false));
        let mir=checked(&src,false);
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|
            if let Statement::ValuePhi{alternatives,..}=stmt {
                Some(alternatives.clone())
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),3,"older PHI, recent PHI, output PHI");
        assert_eq!(phis[0].len(),2,"independent older PHI must not expand");
        assert_eq!(phis[1].len(),4,"recent PHI is specialized per return origin");
        assert_eq!(phis[2].len(),4);
        assert_eq!(output(&mir).len(),4);
    }
    #[test]
    fn two_older_independent_shared_joins_remain_unexpanded(){
        let src=source(false).replace("let extra=",
            "let w:Blob=Blob{n:10};let z:Blob=Blob{n:11};\
             let older2=if true{&w}else{&z};let extra=");
        let src=format!("{src}let output=choose(recent,extra,older,older2);let n=output.n;");
        let mir=lower(&src,false,|summary|{
            summary.parameters.push(ConstType::Ref(Box::new(
                ConstType::Named("Blob".into()))));
        }).expect("four-argument independent PHI composition");
        assert!(mir.verify().unwrap().is_empty());
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::ValuePhi{alternatives,..}=s{
                Some(alternatives.len())
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis,vec![2,2,4,4],"older generations must stay independent");
    }
    #[test]
    fn unrelated_readonly_phi_survives_origin_correlated_field_writes(){
        let src=format!("{}let output=choose(recent,extra,older);output.n=4;",source(true));
        let mir=checked(&src,true);
        let cases=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::Call{name,effects,path_cases,..}=s {
                (name=="choose").then_some((effects,path_cases))
            }else{None}).collect::<Vec<_>>();
        assert_eq!(cases.len(),4);
        for (effects,path_cases) in cases {
            assert_eq!(effects.len(),1);
            assert_eq!(path_cases.len(),1);
            assert_eq!(path_cases[0].effects.as_slice(),effects.as_slice());
            assert_eq!(effects[0].kind,VerifiedEffectKind::Write);
        }
    }
    #[test]
    fn independent_older_phi_generation_is_used_by_each_call_arm(){
        let src=format!("{}let output=choose(recent,extra,older);let n=output.n;",source(false));
        let mir=checked(&src,false);
        let older=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|
            if let Statement::ValuePhi{generation,alternatives,..}=s {
                (alternatives.len()==2).then_some(*generation)
            }else{None}).flatten().expect("older PHI generation");
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|s|
            if let Statement::Call{name,events,..}=s {
                name=="choose" && events.iter().any(|e|
                    e.op==Access::Read && e.loan==Some(older))
            }else{false}).count(),4);
    }
    #[test]
    fn partial_move_of_unrelated_field_remains_legal(){
        let src=format!("{}let output=choose(recent,extra,older);let spare:Blob=t.c;let n=output.n;",source(false));
        let mir=checked(&src,false);
        assert_eq!(output(&mir).len(),4);
    }
    #[test]
    fn independent_shared_phi_cannot_lose_either_referent(){
        for owner in ["x","y"]{
            let src=format!("{}let moved:Blob={owner};let output=choose(recent,extra,older);let n=output.n;",source(false));
            let rejected=match lower(&src,false,|_|{}){
                None=>true,Some(mir)=>mir.verify().map_or(true,|c|!c.is_empty()),
            };
            assert!(rejected,"unrelated {owner} PHI referent was moved");
        }
    }
    #[test]
    fn independent_shared_phi_cannot_alias_mutable_write(){
        let mut src=source(true);
        src=src.replace("let older=if true{&x}else{&y};",
            "let older=if true{&t.a}else{&t.b};");
        src.push_str("let output=choose(recent,extra,older);output.n=4;");
        let rejected=match lower(&src,true,|_|{}){
            None=>true,Some(mir)=>mir.verify().map_or(true,|c|!c.is_empty()),
        };
        assert!(rejected,"shared older PHI cannot authorize &mut write");
    }
    #[test]
    fn a_return_origin_from_an_older_join_must_not_be_guessed(){
        let src=format!("{}let output=choose(recent,extra,older);let n=output.n;",source(false));
        assert!(lower(&src,false,|summary|{
            summary.returned_alternatives[1].parameter=2;
        }).is_none());
    }
    #[test]
    fn forged_field_write_on_shared_older_phi_fails_closed(){
        let src=format!("{}let output=choose(recent,extra,older);let n=output.n;",source(true));
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        assert!(lower(&src,true,|summary|{
            summary.field_writes.push(VerifiedFieldWrite{
                parameter:2,fields:vec![field]});
            summary.parameter_effects.push(VerifiedParameterEffect{
                parameter:2,fields:vec![field],kind:VerifiedEffectKind::Write});
        }).is_none());
    }
    #[test]
    fn forged_path_case_effect_on_independent_phi_fails_closed(){
        let src=format!("{}let output=choose(recent,extra,older);let n=output.n;",source(true));
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        assert!(lower(&src,true,|summary|{
            summary.path_cases[0].effects.push(VerifiedParameterEffect{
                parameter:2,fields:vec![field],kind:VerifiedEffectKind::Write});
        }).is_none());
    }
    #[test]
    fn missing_correlated_origin_effect_case_fails_closed(){
        let src=format!("{}let output=choose(recent,extra,older);let n=output.n;",source(true));
        assert!(lower(&src,true,|summary|{
            summary.path_cases.pop();
        }).is_none());
    }
    #[test]
    fn independent_mutable_phi_is_not_speculatively_selected(){
        let src=source(false).replace("let older=if true{&x}else{&y};",
            "let older=if true{&mut q}else{&mut t.c};");
        let src=format!("{src}let output=choose(recent,extra,older);let n=output.n;");
        assert!(lower(&src,false,|_|{}).is_none());
    }
    #[test]
    fn fake_older_phi_generation_does_not_authorize_a_call(){
        let src=format!("{}let output=choose(recent,extra,older);let n=output.n;",source(false));
        let mut mir=checked(&src,false);
        let old_generation=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|
            if let Statement::ValuePhi{generation,alternatives,..}=s {
                (alternatives.len()==2).then_some(*generation)
            }else{None}).flatten().expect("prior generation");
        let mut changed=0;
        for block in &mut mir.blocks{for s in &mut block.statements{
            if let Statement::Call{name,events,..}=s {
                if name=="choose" {for e in events{
                    if e.op==Access::Read && e.loan==Some(old_generation){
                        e.loan=Some(SymbolId(u32::MAX));changed+=1;
                    }
                }}
            }
        }}
        assert_eq!(changed,4);
        assert!(mir.verify().is_err() || mir.verify().unwrap().len()>0);
    }
}

#[cfg(test)]
mod independent_mutable_cross_cfg_0664_tests {
    use super::*;

    fn lower(body:&str,mutate:impl FnOnce(&mut VerifiedCallSummary))
        ->Option<FunctionMir> {
        let tokens=crate::syntax::lex(body).expect("test syntax");
        let blob=ConstType::Named("Blob".into());
        let types=HashMap::from([
            ("Blob".into(),vec![("n".into(),ConstType::I64)]),
            ("Tri".into(),vec![("a".into(),blob.clone()),
                ("b".into(),blob.clone()),("c".into(),blob.clone())]),
        ]);
        let ids=HashMap::from([("Blob".into(),TypeId(0)),("Tri".into(),TypeId(1))]);
        let names=vec!["Blob".into(),"Tri".into()];
        let methods=HashMap::new();let effects=HashMap::new();
        let enums=HashMap::new();let payloads=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let mutable=ConstType::RefMut(Box::new(blob));
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let mut summary=VerifiedCallSummary{
            parameters:vec![mutable.clone(),mutable.clone(),mutable.clone()],
            returned:None,
            returned_alternatives:(0..2).map(|parameter|VerifiedReturnedReference{
                parameter,fields:vec![],ty:mutable.clone(),
            }).collect(),
            field_writes:(0..3).map(|parameter|VerifiedFieldWrite{
                parameter,fields:vec![field]}).collect(),
            parameter_effects:(0..3).map(|parameter|VerifiedParameterEffect{
                parameter,fields:vec![field],kind:VerifiedEffectKind::Write,
            }).collect(),
            path_cases:(0..2).map(|origin|VerifiedPathCase{
                effects:vec![
                    VerifiedParameterEffect{parameter:origin,fields:vec![field],
                        kind:VerifiedEffectKind::Write},
                    VerifiedParameterEffect{parameter:2,fields:vec![field],
                        kind:VerifiedEffectKind::Write},
                ],returned:Some(origin),uninitialized:vec![],
            }).collect(),
        };
        mutate(&mut summary);
        let calls=HashMap::from([("choose".into(),summary)]);
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("no internal lowering error")
    }
    fn source()->String {
        "let mut t:Tri=Tri{a:Blob{n:1},b:Blob{n:2},c:Blob{n:3}};\
         let mut q:Blob=Blob{n:7};\
         let mut x:Blob=Blob{n:8};let mut y:Blob=Blob{n:9};\
         let older=if true{&mut x}else{&mut y};\
         let extra=&mut q;\
         let recent=if true{&mut t.a}else{&mut t.b};".into()
    }
    fn body(extra:&str)->String {
        format!("{}let output=choose(recent,extra,older);{extra}",source())
    }
    fn checked(src:&str,mutate:impl FnOnce(&mut VerifiedCallSummary))->FunctionMir {
        let mir=lower(src,mutate).expect("complete independent mutable PHI MIR");
        let conflicts=mir.verify().expect("well-formed independent mutable PHIs");
        assert!(conflicts.is_empty(),"{conflicts:?}");mir
    }
    fn old_phi(mir:&FunctionMir)->(SymbolId,Vec<RefOption>){
        mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|stmt|
            match stmt {
                Statement::ValuePhi{ty:ConstType::RefMut(_),generation:Some(g),
                    alternatives,..} if alternatives.len()==2=>Some((*g,alternatives.clone())),
                _=>None,
            }).expect("older independent mutable PHI")
    }
    #[test]
    fn independent_mutable_phi_is_accepted_with_exact_exclusive_loans(){
        let mir=checked(&body("let n=output.n;"),|_|{});
        let (_,options)=old_phi(&mir);
        assert_eq!(options.len(),2);
        assert!(options.iter().all(|o|o.exclusive));
    }
    #[test]
    fn independent_mutable_origin_is_never_selected_at_newer_merge(){
        let mir=checked(&body("let n=output.n;"),|_|{});
        let (generation,_) = old_phi(&mir);
        let call_events=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            match s{Statement::Call{name,events,..} if name=="choose"=>Some(events),_=>None})
            .collect::<Vec<_>>();
        assert_eq!(call_events.len(),4);
        for events in call_events {
            assert!(events.iter().any(|e|e.op==Access::Read &&
                e.loan==Some(generation)));
            assert!(events.iter().any(|e|e.op==Access::Write &&
                e.loan==Some(generation)));
        }
    }
    #[test]
    fn writes_to_older_mutable_phi_retain_both_typed_movepaths(){
        let mir=checked(&body("let n=output.n;"),|_|{});
        let (_,options)=old_phi(&mir);
        let writes=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            match s {Statement::Call{name,effects,..} if name=="choose"=>Some(effects),_=>None})
            .collect::<Vec<_>>();
        assert_eq!(writes.len(),4);
        for effects in writes {
            let old=effects.iter().find(|e|e.alternatives.len()==2)
                .expect("complete disjunctive write");
            for (candidate,target) in options.iter().zip(&old.alternatives){
                assert!(candidate.path.ancestor_of(target));
                assert_eq!(target.fields.len(),candidate.path.fields.len()+1);
            }
        }
    }
    #[test]
    fn old_mutable_phi_does_not_multiply_new_merge_predecessors(){
        let mir=checked(&body("let n=output.n;"),|_|{});
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::ValuePhi{alternatives,..}=s{
                Some(alternatives.len())
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis,vec![2,4,4]);
    }
    #[test]
    fn independent_mutable_phi_keeps_all_owners_borrowed(){
        for name in ["x","y"]{
            let src=format!("{}let taken:Blob={name};\
                let output=choose(recent,extra,older);let n=output.n;",source());
            let rejected=match lower(&src,|_|{}){
                None=>true,Some(mir)=>mir.verify().map_or(true,|e|!e.is_empty()),
            };
            assert!(rejected,"moved a live independent mutable origin {name}");
        }
    }
    #[test]
    fn overlapping_old_mutable_and_new_mutable_phis_fail_closed(){
        let src=body("let n=output.n;")
            .replace("let older=if true{&mut x}else{&mut y};",
                     "let older=if true{&mut t.a}else{&mut t.b};");
        let rejected=match lower(&src,|_|{}){
            None=>true,Some(mir)=>mir.verify().map_or(true,|e|!e.is_empty()),
        };
        assert!(rejected,"overlapping independent mutable PHIs are unsound");
    }
    #[test]
    fn missing_old_mutable_write_witness_fails_closed(){
        let src=body("let n=output.n;");
        assert!(lower(&src,|s|{for case in &mut s.path_cases {case.effects.retain(|e|e.parameter!=2);}}).is_none());
    }
    #[test]
    fn move_through_independent_mutable_phi_is_not_certified(){
        let src=body("let n=output.n;");
        assert!(lower(&src,|s|{
            let move_effect=VerifiedParameterEffect{parameter:2,
                fields:vec![],kind:VerifiedEffectKind::Move};
            s.parameter_effects.push(move_effect.clone());
            s.path_cases[0].effects.push(move_effect);
        }).is_none());
    }
    #[test]
    fn returning_an_independent_mutable_phi_is_proved_relationally(){
        let src=body("let n=output.n;");
        let mir=checked(&src,|s|{
            s.returned_alternatives[1].parameter=2;
        });
        let result_options=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .find_map(|stmt|match stmt {
                Statement::ValuePhi{alternatives,..} if alternatives.len()==4 =>
                    Some(alternatives),
                _=>None,
            }).expect("four distinct proven mutable return candidates");
        assert_eq!(result_options.iter().map(|o|o.path.owner)
            .collect::<HashSet<_>>().len(),3);
    }
    #[test]
    fn forged_mutable_phi_generation_is_rejected(){
        let mut mir=checked(&body("let n=output.n;"),|_|{});
        let (generation,_) = old_phi(&mir);
        let mut changed=0;
        for block in &mut mir.blocks {for stmt in &mut block.statements{
            if let Statement::Call{name,events,..}=stmt{
                if name=="choose" {for event in events {
                    if event.op==Access::Write && event.loan==Some(generation) {
                        event.loan=Some(SymbolId(u32::MAX));changed+=1;
                    }
                }}
            }
        }}
        assert_eq!(changed,4);
        assert!(mir.verify().is_err() || mir.verify().unwrap().len()>0);
    }
    #[test]
    fn two_independent_mutable_phi_generations_remain_separate(){
        let src=source().replace("let extra=&mut q;",
            "let mut w:Blob=Blob{n:10};let mut z:Blob=Blob{n:11};\
             let older2=if true{&mut w}else{&mut z};let extra=&mut q;");
        let src=format!("{src}let output=choose(recent,extra,older,older2);let n=output.n;");
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let mir=checked(&src,|s|{
            s.parameters.push(ConstType::RefMut(Box::new(ConstType::Named("Blob".into()))));
            s.field_writes.push(VerifiedFieldWrite{parameter:3,fields:vec![field]});
            let extra=VerifiedParameterEffect{parameter:3,fields:vec![field],
                kind:VerifiedEffectKind::Write};
            s.parameter_effects.push(extra.clone());
            for case in &mut s.path_cases {case.effects.push(extra.clone());}
        });
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            match s {Statement::ValuePhi{generation:Some(g),alternatives,..}
                =>Some((*g,alternatives.len())),_=>None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),4);
        assert_eq!(phis.iter().map(|(_,n)|*n).collect::<Vec<_>>(),vec![2,2,4,4]);
        assert_ne!(phis[0].0,phis[1].0);
    }
    #[test]
    fn partial_move_of_independent_sibling_stays_valid(){
        let mir=checked(&body("let spare:Blob=t.c;let n=output.n;"),|_|{});
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn forged_old_mutable_projection_cannot_be_used_as_effect(){
        let src=body("let n=output.n;");
        let bad=FieldKey{aggregate:TypeId(u32::MAX),field:FieldId(0)};
        assert!(lower(&src,|s|{
            s.field_writes.push(VerifiedFieldWrite{parameter:2,fields:vec![bad]});
            let added=VerifiedParameterEffect{parameter:2,fields:vec![bad],
                kind:VerifiedEffectKind::Write};
            s.parameter_effects.push(added.clone());
            for case in &mut s.path_cases{case.effects.push(added.clone());}
        }).is_none());
    }
    #[test]
    fn disjoint_fields_of_same_aggregate_remain_mutably_independent(){
        let src=body("let n=output.n;")
            .replace("let older=if true{&mut x}else{&mut y};",
                     "let older=if true{&mut t.c}else{&mut x};");
        let mir=checked(&src,|_|{});
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn older_mutable_group_cannot_forge_a_parent_loan(){
        let mut mir=checked(&body("let n=output.n;"),|_|{});
        let (generation,options)=old_phi(&mir);
        let victim=options[0].loan;
        let mut changed=false;
        for block in &mut mir.blocks {for statement in &mut block.statements {
            if let Statement::ValuePhi{generation:Some(g),alternatives,..}=statement {
                if *g==generation {
                    if let Some(option)=alternatives.iter_mut().find(|o|o.loan==victim) {
                        option.parent=Some(SymbolId(u32::MAX));changed=true;
                    }
                }
            }
        }}
        assert!(changed);
        assert!(mir.verify().is_err() || mir.verify().unwrap().len()>0);
    }
    #[test]
    fn older_mutable_group_cannot_have_a_phantom_candidate(){
        let mut mir=checked(&body("let n=output.n;"),|_|{});
        let (generation,options)=old_phi(&mir);
        assert_eq!(options.len(),2);
        for block in &mut mir.blocks {for statement in &mut block.statements {
            if let Statement::ValuePhi{generation:Some(g),alternatives,..}=statement {
                if *g==generation {
                    alternatives[1].loan=SymbolId(u32::MAX);
                }
            }
        }}
        assert!(mir.verify().is_err() || mir.verify().unwrap().len()>0);
    }
}

#[cfg(test)]
mod late_mut_phi_binding_0665_tests {
    use super::*;

    fn lower(source:&str)->Option<FunctionMir>{
        let tokens=crate::syntax::lex(source).expect("valid regression tokens");
        let blob=ConstType::Named("Blob".into());
        let types=HashMap::from([("Blob".into(),vec![("n".into(),ConstType::I64)])]);
        let ids=HashMap::from([("Blob".into(),TypeId(0))]);
        let names=vec!["Blob".to_owned()];
        let enums=HashMap::new();let payloads=HashMap::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,
            types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        let r=ConstType::RefMut(Box::new(blob));
        let summary=VerifiedCallSummary{
            parameters:vec![r.clone()],field_writes:vec![],
            parameter_effects:vec![],returned:Some(VerifiedReturnedReference{
                parameter:0,fields:vec![],ty:r}),
            returned_alternatives:vec![],path_cases:vec![],
        };
        let calls=HashMap::from([("forward".to_owned(),summary)]);
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("MIR builder must not panic")
    }
    fn base()->&'static str {
        "let mut a:Blob=Blob{n:1};let mut b:Blob=Blob{n:2};\
         let old=if true{&mut a}else{&mut b};let marker:i64=7;"
    }
    fn checked(body:&str)->FunctionMir {
        let source=format!("{}{}",base(),body);
        let mir=lower(&source).expect("late PHI must produce complete MIR");
        let conflicts=mir.verify().expect("well-formed late PHI proof");
        assert!(conflicts.is_empty(),"{conflicts:?}");mir
    }
    fn rejected(source:&str)->bool{
        match lower(source){
            None=>true,
            Some(mir)=>mir.verify().map_or(true,|errors|!errors.is_empty()),
        }
    }
    fn binding(mir:&FunctionMir)->(SymbolId,SymbolId,Vec<RefOption>){
        mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|
            if let Statement::LatePhiReborrow{generation,source_generation,children,..}=s{
                Some((*source_generation,*generation,children.clone()))
            }else{None}).expect("late conditional reborrow")
    }
    #[test]
    fn late_mutable_reborrow_is_bound_after_original_cfg_merge(){
        let mir=checked("let child=&mut *old;let n=child.n;");
        let (old,new,options)=binding(&mir);
        assert_ne!(old,new);
        assert_eq!(options.len(),2);
        assert!(options.iter().all(|option|option.exclusive && option.parent.is_some()));
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|s|
            matches!(s,Statement::LatePhiReborrow{..})).count(),1);
    }
    #[test]
    fn pure_forwarding_function_binds_real_parent_not_first_candidate(){
        let mir=checked("let child=forward(old);let n=child.n;");
        let (_,_,options)=binding(&mir);
        let parents=options.iter().map(|o|o.parent).collect::<HashSet<_>>();
        assert_eq!(parents.len(),2);
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|s|
            matches!(s,Statement::Call{name,..} if name=="forward")).count(),1);
    }
    #[test]
    fn one_new_loan_per_source_and_exact_typed_movepath(){
        let mir=checked("let child=&mut *old;let n=child.n;");
        let (old,_,children)=binding(&mir);
        let sources=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|
            if let Statement::ValuePhi{generation:Some(g),alternatives,..}=s{
                (*g==old).then_some(alternatives.clone())
            }else{None}).unwrap();
        for (source,child) in sources.iter().zip(children.iter()) {
            assert_eq!(child.path,source.path);
            assert_eq!(child.parent,Some(source.loan));
            assert_ne!(child.loan,source.loan);
        }
    }
    #[test]
    fn late_reborrow_keeps_both_possible_owners_protected(){
        for owner in ["a","b"] {
            let body=format!("let child=&mut *old;let taken:Blob={owner};let n=child.n;");
            assert!(rejected(&format!("{}{}",base(),body)),
                "moved live late-PHI origin {owner}");
        }
    }
    #[test]
    fn parent_access_while_derived_mutable_loan_is_live_fails(){
        let src=format!("{}let child=&mut *old;let n=old.n;let k=child.n;",base());
        assert!(rejected(&src),"mutable source must be suspended by child");
    }
    #[test]
    fn two_successive_late_reborrows_preserve_parent_chain(){
        let mir=checked("let first=&mut *old;let second=&mut *first;let n=second.n;");
        let chains=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::LatePhiReborrow{source_generation,generation,children,..}=s{
                Some((*source_generation,*generation,children.clone()))
            }else{None}).collect::<Vec<_>>();
        assert_eq!(chains.len(),2);
        assert_eq!(chains[1].0,chains[0].1);
        for (a,b) in chains[0].2.iter().zip(chains[1].2.iter()){
            assert_eq!(b.parent,Some(a.loan));
        }
    }
    #[test]
    fn independent_mutable_phi_chains_keep_separate_generations(){
        let src="let mut a:Blob=Blob{n:1};let mut b:Blob=Blob{n:2};\
            let mut c:Blob=Blob{n:3};let mut d:Blob=Blob{n:4};\
            let r=if true{&mut a}else{&mut b};\
            let s=if true{&mut c}else{&mut d};\
            let x=&mut *r;let y=&mut *s;let a1=x.n;let a2=y.n;";
        let mir=lower(src).expect("complete disjoint late reborrows");
        assert!(mir.verify().unwrap().is_empty());
        let generations=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::LatePhiReborrow{generation,..}=s{Some(*generation)}else{None})
            .collect::<HashSet<_>>();
        assert_eq!(generations.len(),2);
    }
    #[test]
    fn forged_parent_loan_cannot_certify_late_binding(){
        let mut mir=checked("let child=&mut *old;let n=child.n;");
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()) {
            if let Statement::LatePhiReborrow{children,..}=stmt {
                children[0].parent=Some(SymbolId(u32::MAX));break;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn forged_generation_cannot_certify_late_binding(){
        let mut mir=checked("let child=&mut *old;let n=child.n;");
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()) {
            if let Statement::LatePhiReborrow{event,..}=stmt {
                event.parent=Some(SymbolId(u32::MAX));break;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn forged_field_projection_cannot_escape_source_loan(){
        let mut mir=checked("let child=&mut *old;let n=child.n;");
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()) {
            if let Statement::LatePhiReborrow{children,..}=stmt {
                children[0].path=children[0].path.child(FieldKey{
                    aggregate:TypeId(0),field:FieldId(0)});break;
            }
        }
        assert!(mir.verify().is_err());
    }
    #[test]
    fn effectful_forwarding_must_not_gain_a_false_late_phi_certificate(){
        let source=format!("{}let child=effect(old);let n=child.n;",base());
        let tokens=crate::syntax::lex(&source).expect("syntax");
        let blob=ConstType::Named("Blob".into());
        let types=HashMap::from([("Blob".to_owned(),vec![("n".to_owned(),ConstType::I64)])]);
        let ids=HashMap::from([("Blob".to_owned(),TypeId(0))]);
        let names=vec!["Blob".to_owned()];
        let enums=HashMap::new();let payloads=HashMap::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let refer=ConstType::RefMut(Box::new(blob));
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let summary=VerifiedCallSummary{parameters:vec![refer.clone()],
            field_writes:vec![VerifiedFieldWrite{parameter:0,fields:vec![field]}],
            parameter_effects:vec![VerifiedParameterEffect{parameter:0,
                fields:vec![field],kind:VerifiedEffectKind::Write}],
            returned:Some(VerifiedReturnedReference{parameter:0,
                fields:vec![],ty:refer}),returned_alternatives:vec![],path_cases:vec![],
        };
        let calls=HashMap::from([("effect".to_owned(),summary)]);
        let result=lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("no internal lowering error");
        assert!(result.is_none(),"effectful return may not gain unsound certificate");
    }
    #[test]
    fn late_projected_phi_creates_exact_typed_field_paths(){
        let mir=checked("let field=&mut old.n;let value=*field;");
        let (source,out,children)=binding(&mir);
        assert_ne!(source,out);
        assert_eq!(children.len(),2);
        let key=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        assert!(children.iter().all(|option|option.exclusive &&
            option.path.fields==vec![key] && option.parent.is_some()));
        let projected_type=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .find_map(|s|if let Statement::LatePhiReborrow{ty,..}=s{
                Some(ty.clone())
            }else{None}).unwrap();
        assert_eq!(projected_type,ConstType::RefMut(Box::new(ConstType::I64)));
        let source_options=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .find_map(|s|if let Statement::ValuePhi{generation:Some(id),alternatives,..}=s{
                (*id==source).then_some(alternatives.clone())
            }else{None}).unwrap();
        for (parent,child) in source_options.iter().zip(&children){
            assert_eq!(child.parent,Some(parent.loan));
            assert!(parent.path.ancestor_of(&child.path));
        }
    }
    #[test]
    fn intervening_field_write_precedes_late_projected_reborrow(){
        let mir=checked("old.n=3;let field=&mut old.n;let value=*field;");
        let (_,_,children)=binding(&mir);
        assert_eq!(children.len(),2);
        assert!(children.iter().all(|child|child.path.fields.len()==1));
    }
    #[test]
    fn projected_phi_reborrow_can_be_reborrowed_again_later(){
        let mir=checked("let first=&mut old.n;let marker2:i64=8;\
            let second=&mut *first;let value=*second;");
        let phis=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::LatePhiReborrow{generation,
                source_generation,children,..}=s{
                Some((*generation,*source_generation,children.clone()))
            }else{None}).collect::<Vec<_>>();
        assert_eq!(phis.len(),2);
        assert_eq!(phis[1].1,phis[0].0);
        for (parent,child) in phis[0].2.iter().zip(&phis[1].2){
            assert_eq!(child.parent,Some(parent.loan));
            assert_eq!(child.path,parent.path);
        }
    }
    #[test]
    fn independent_projected_mut_phis_keep_distinct_parent_chains(){
        let src="let mut a:Blob=Blob{n:1};let mut b:Blob=Blob{n:2};\
            let mut c:Blob=Blob{n:3};let mut d:Blob=Blob{n:4};\
            let r=if true{&mut a}else{&mut b};\
            let s=if false{&mut c}else{&mut d};\
            let marker:i64=0;let x=&mut r.n;let y=&mut s.n;\
            let first=*x;let second=*y;";
        let mir=lower(src).expect("independent projected PHIs must lower");
        assert!(mir.verify().unwrap().is_empty());
        let groups=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::LatePhiReborrow{generation,
                source_generation,children,..}=s{
                Some((*generation,*source_generation,children.clone()))
            }else{None}).collect::<Vec<_>>();
        assert_eq!(groups.len(),2);
        assert_ne!(groups[0].0,groups[1].0);
        assert_ne!(groups[0].1,groups[1].1);
        let owners=groups.iter().map(|(_,_,options)|options.iter()
            .map(|o|o.path.owner).collect::<HashSet<_>>())
            .collect::<Vec<_>>();
        assert!(owners[0].is_disjoint(&owners[1]));
    }
    #[test]
    fn parent_phi_cannot_be_used_while_projected_child_is_live(){
        assert!(rejected(&format!("{}let field=&mut old.n;\
            let x=old.n;let still_live=*field;",base())));
    }
    #[test]
    fn projected_child_protects_both_possible_original_owners(){
        for owner in ["a","b"]{
            let src=format!("{}let field=&mut old.n;let moved:Blob={owner};\
                let value=*field;",base());
            assert!(rejected(&src),"original {owner} must remain borrowed");
        }
    }
    #[test]
    fn forged_projected_child_cannot_switch_its_owner(){
        let mut mir=checked("let field=&mut old.n;let value=*field;");
        let mut forged=None;
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()){
            if let Statement::LatePhiReborrow{children,..}=stmt{
                forged=Some((children[0].loan,children[0].path.clone()));
                children[0].path.owner=SymbolId(u32::MAX);
                break;
            }
        }
        let (loan,mut path)=forged.unwrap();
        path.owner=SymbolId(u32::MAX);
        mir.loans.insert(loan,path);
        assert!(mir.verify().is_err(),"child must remain within parent MovePath");
    }
    #[test]
    fn forged_two_level_field_projection_is_not_a_single_valid_reborrow(){
        let mut mir=checked("let field=&mut old.n;let value=*field;");
        let mut forged=None;
        for stmt in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()){
            if let Statement::LatePhiReborrow{children,..}=stmt{
                let key=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
                children[0].path=children[0].path.child(key);
                forged=Some((children[0].loan,children[0].path.clone()));
                break;
            }
        }
        let (loan,path)=forged.unwrap();
        mir.loans.insert(loan,path);
        assert!(mir.verify().is_err(),"deep projection must be proved step by step");
    }
    #[test]
    fn unknown_field_in_late_projection_is_not_certified(){
        let src=format!("{}let field=&mut old.missing;let value=*field;",base());
        assert!(lower(&src).is_none(),"unknown FieldKey cannot enter MIR");
    }
    #[test]
    fn stale_or_retired_source_generation_is_not_implicitly_reused(){
        let src=format!("{}let n=old.n;let child=&mut *old;let q=child.n;",base());
        let mir=lower(&src).expect("late reborrow MIR");
        assert!(mir.verify().unwrap().is_empty());
    }
}

#[cfg(test)]
mod staged_projected_return_0667_tests {
    use super::*;

    fn root()->ConstType{ConstType::Named("Root".into())}
    fn middle()->ConstType{ConstType::Named("Middle".into())}
    fn leaf()->ConstType{ConstType::Named("Leaf".into())}
    fn key_root()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn key_middle()->FieldKey{FieldKey{aggregate:TypeId(1),field:FieldId(0)}}
    const SOURCE:&str="let mut a:Root=Root{middle:Middle{leaf:Leaf{n:1},sibling:2},other:3};\
        let mut b:Root=Root{middle:Middle{leaf:Leaf{n:4},sibling:5},other:6};\
        let old=if true{&mut a}else{&mut b};let marker:i64=7;";

    fn lower_with(body:&str,alter:impl FnOnce(&mut HashMap<String,VerifiedCallSummary>))
        ->Option<FunctionMir>{
        let source=format!("{SOURCE}{body}");
        let tokens=crate::syntax::lex(&source).expect("QRust test tokens");
        let types=HashMap::from([
            ("Root".to_owned(),vec![("middle".into(),middle()),("other".into(),ConstType::I64)]),
            ("Middle".to_owned(),vec![("leaf".into(),leaf()),("sibling".into(),ConstType::I64)]),
            ("Leaf".to_owned(),vec![("n".into(),ConstType::I64)]),
        ]);
        let ids=HashMap::from([("Root".to_owned(),TypeId(0)),
            ("Middle".to_owned(),TypeId(1)),("Leaf".to_owned(),TypeId(2))]);
        let names=vec!["Root".to_owned(),"Middle".to_owned(),"Leaf".to_owned()];
        let enums=HashMap::new();let payloads=HashMap::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,
            types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        let mut calls=HashMap::new();
        let r=ConstType::RefMut(Box::new(root()));
        let m=ConstType::RefMut(Box::new(middle()));
        let l=ConstType::RefMut(Box::new(leaf()));
        for (name,param,fields,result) in [
            ("return_root",r.clone(),vec![],r.clone()),
            ("return_middle",r.clone(),vec![key_root()],m.clone()),
            ("return_leaf",r.clone(),vec![key_root(),key_middle()],l.clone()),
            ("leaf_of_middle",m.clone(),vec![key_middle()],l.clone()),
            ("forward_leaf",l.clone(),vec![],l.clone()),
        ] {
            calls.insert(name.to_owned(),VerifiedCallSummary{
                parameters:vec![param],field_writes:vec![],
                parameter_effects:vec![],returned:Some(VerifiedReturnedReference{
                    parameter:0,fields,ty:result}),
                returned_alternatives:vec![],path_cases:vec![],
            });
        }
        alter(&mut calls);
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("MIR lowering must not panic")
    }
    fn lower(body:&str)->Option<FunctionMir>{lower_with(body,|_|{})}
    fn checked(body:&str)->FunctionMir{
        let mir=lower(body).expect("complete staged mutable PHI MIR");
        let conflicts=mir.verify().expect("well-formed staged MIR");
        assert!(conflicts.is_empty(),"{conflicts:?}");
        mir
    }
    fn stages(mir:&FunctionMir)->Vec<(SymbolId,SymbolId,Option<FieldKey>,Vec<RefOption>)>{
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|{
            if let Statement::LatePhiReborrow{source_generation,generation,
                projection,children,..}=stmt {
                Some((*source_generation,*generation,*projection,children.clone()))
            }else{None}
        }).collect()
    }
    fn rejected(body:&str)->bool{
        match lower(body){
            None=>true,
            Some(mir)=>mir.verify().map_or(true,|conflicts|!conflicts.is_empty()),
        }
    }
    #[test]
    fn two_qualified_fields_emit_two_real_reborrow_generations(){
        let mir=checked("let value=&mut old.middle.leaf;let n=value.n;");
        let steps=stages(&mir);
        assert_eq!(steps.len(),2);
        assert_eq!([steps[0].2,steps[1].2],[Some(key_root()),Some(key_middle())]);
        assert_eq!(steps[1].0,steps[0].1);
        for (left,right) in steps[0].3.iter().zip(&steps[1].3){
            assert_eq!(right.parent,Some(left.loan));
            assert_eq!(right.path,left.path.child(key_middle()));
            assert_eq!(right.path.fields.len(),2);
        }
    }
    #[test]
    fn nested_fields_can_be_borrowed_at_separate_program_points(){
        let mir=checked("let first=&mut old.middle;let marker2:i64=11;\
            let second=&mut first.leaf;let n=second.n;");
        let steps=stages(&mir);
        assert_eq!(steps.len(),2);
        assert_eq!(steps[1].0,steps[0].1);
    }
    #[test]
    fn verified_projected_return_preserves_both_owners_and_two_parents(){
        let mir=checked("let value=return_leaf(old);let n=value.n;");
        let steps=stages(&mir);
        assert_eq!(steps.len(),2);
        let origins=steps[1].3.iter().map(|r|r.path.owner).collect::<HashSet<_>>();
        assert_eq!(origins.len(),2);
        assert!(steps[1].3.iter().all(|r|r.path.fields==vec![key_root(),key_middle()]));
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|s|
            matches!(s,Statement::Call{name,..} if name=="return_leaf")).count(),1);
    }
    #[test]
    fn projected_return_chained_with_second_interprocedural_projection(){
        let mir=checked("let first=return_middle(old);let marker2:i64=11;\
            let second=leaf_of_middle(first);let n=second.n;");
        let steps=stages(&mir);
        assert_eq!(steps.len(),2);
        assert_eq!(steps[1].0,steps[0].1);
        for (a,b) in steps[0].3.iter().zip(&steps[1].3){
            assert_eq!(b.parent,Some(a.loan));
        }
    }
    #[test]
    fn identity_forward_after_projected_return_preserves_complete_chain(){
        let mir=checked("let first=return_leaf(old);let marker2:i64=11;\
            let second=forward_leaf(first);let n=second.n;");
        let steps=stages(&mir);
        assert_eq!(steps.len(),3);
        assert_eq!(steps[2].2,None);
        assert_eq!(steps[2].0,steps[1].1);
        assert!(steps[2].3.iter().zip(&steps[1].3).all(|(c,p)|
            c.parent==Some(p.loan) && c.path==p.path));
    }
    #[test]
    fn independent_owner_can_be_moved_during_nested_reference_lifetime(){
        let mir=checked("let value=return_leaf(old);            let independent:Leaf=Leaf{n:9};let moved:Leaf=independent;            let n=value.n;");
        assert!(mir.verify().unwrap().is_empty());
        assert!(stages(&mir)[1].3.iter().all(|c|c.path.fields.len()==2));
    }
    #[test]
    fn both_possible_original_owners_remain_borrowed(){
        for owner in ["a","b"]{
            let body=format!("let value=return_leaf(old);let moved:Root={owner};let n=value.n;");
            assert!(rejected(&body),"moving {owner} while leaf loan is live");
        }
    }
    #[test]
    fn projected_child_blocks_access_through_suspended_source(){
        assert!(rejected("let child=&mut old.middle.leaf;let n=old.middle.leaf.n;\
            let still_live=child.n;"));
    }
    #[test]
    fn unknown_mid_chain_field_never_gets_a_certificate(){
        assert!(lower("let child=&mut old.middle.unknown;let n=child.n;").is_none());
    }
    #[test]
    fn forged_intermediate_parent_id_is_rejected(){
        let mut mir=checked("let child=&mut old.middle.leaf;let n=child.n;");
        for block in &mut mir.blocks {for stmt in &mut block.statements {
            if let Statement::LatePhiReborrow{children,projection:Some(field),..}=stmt {
                if *field==key_middle(){children[0].parent=Some(SymbolId(u32::MAX));break;}
            }
        }}
        assert!(mir.verify().is_err());
    }
    #[test]
    fn forged_mid_chain_field_id_is_rejected_even_when_loan_path_is_updated(){
        let mut mir=checked("let child=&mut old.middle.leaf;let n=child.n;");
        let bad=FieldKey{aggregate:TypeId(u32::MAX),field:FieldId(0)};
        for block in &mut mir.blocks {for stmt in &mut block.statements {
            if let Statement::LatePhiReborrow{children,projection:Some(field),..}=stmt{
                if *field==key_middle(){
                    children[0].path.fields[1]=bad;
                    let new=children[0].path.clone();
                    mir.loans.insert(children[0].loan,new);
                    break;
                }
            }
        }}
        assert!(mir.verify().is_err());
    }
    #[test]
    fn changing_last_stage_projection_without_children_is_rejected(){
        let mut mir=checked("let child=&mut old.middle.leaf;let n=child.n;");
        for block in &mut mir.blocks {for stmt in &mut block.statements {
            if let Statement::LatePhiReborrow{projection:Some(field),..}=stmt {
                if *field==key_middle(){*field=key_root();break;}
            }
        }}
        assert!(mir.verify().is_err());
    }
    #[test]
    fn forged_return_field_is_not_a_projected_loan(){
        let body="let child=return_leaf(old);let n=child.n;";
        let forged=lower_with(body,|calls|{
            let summary=calls.get_mut("return_leaf").unwrap();
            summary.returned.as_mut().unwrap().fields[1]=FieldKey{
                aggregate:TypeId(u32::MAX),field:FieldId(0)};
        });
        assert!(forged.is_none(),"forged aggregate id cannot enter PHI chain");
    }
    #[test]
    fn projected_return_wrong_result_type_is_not_certified(){
        let bad=lower_with("let child=return_leaf(old);let n=child.n;",|calls|{
            calls.get_mut("return_leaf").unwrap().returned.as_mut().unwrap().ty=
                ConstType::RefMut(Box::new(middle()));
        });
        assert!(bad.is_none(),"return type must match final projected field");
    }
    #[test]
    fn effectful_projected_return_requires_separate_certificate(){
        let bad=lower_with("let child=return_leaf(old);let n=child.n;",|calls|{
            let summary=calls.get_mut("return_leaf").unwrap();
            let effect=VerifiedParameterEffect{parameter:0,
                fields:vec![key_root()],kind:VerifiedEffectKind::Write};
            summary.parameter_effects.push(effect);
        });
        assert!(bad.is_none(),"pure path cannot admit an effectful returning call");
    }
    #[test]
    fn root_forwarding_retains_exact_empty_projection(){
        let mir=checked("let child=return_root(old);let n=child.middle.leaf.n;");
        let steps=stages(&mir);
        assert_eq!(steps.len(),1);
        assert_eq!(steps[0].2,None);
        assert!(steps[0].3.iter().all(|child|child.path.fields.is_empty()));
    }
}


#[cfg(test)]
mod multiparameter_effectful_late_return_0668_tests {
    use super::*;

    fn root()->ConstType {ConstType::Named("Root".into())}
    fn leaf()->ConstType {ConstType::Named("Leaf".into())}
    fn kr()->FieldKey {FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn km()->FieldKey {FieldKey{aggregate:TypeId(1),field:FieldId(0)}}
    fn ko()->FieldKey {FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn mutable_root()->ConstType {ConstType::RefMut(Box::new(root()))}
    fn mutable_leaf()->ConstType {ConstType::RefMut(Box::new(leaf()))}
    fn write(parameter:usize,fields:Vec<FieldKey>)->VerifiedParameterEffect {
        VerifiedParameterEffect{parameter,fields,kind:VerifiedEffectKind::Write}
    }
    fn verified(parameter:usize,params:Vec<ConstType>,effects:Vec<VerifiedParameterEffect>)
        ->VerifiedCallSummary {
        VerifiedCallSummary{
            parameters:params,
            field_writes:effects.iter().map(|e|VerifiedFieldWrite{
                parameter:e.parameter,fields:e.fields.clone(),}).collect(),
            parameter_effects:effects.clone(),
            returned:Some(VerifiedReturnedReference{
                parameter,fields:vec![kr(),km()],ty:mutable_leaf()}),
            returned_alternatives:vec![],
            path_cases:if effects.is_empty(){vec![]}else{
                effects.into_iter().map(|e|VerifiedPathCase{
                    effects:vec![e],returned:Some(0),uninitialized:vec![],
                }).collect()
            },
        }
    }
    const SOURCE:&str="let mut a:Root=Root{middle:Middle{leaf:Leaf{n:1},sibling:2},other:3};\
        let mut b:Root=Root{middle:Middle{leaf:Leaf{n:4},sibling:5},other:6};\
        let old=if true{&mut a}else{&mut b};let marker:i64=7;";
    const SPARE:&str="let mut spare:Root=Root{middle:Middle{leaf:Leaf{n:8},sibling:9},other:10};";
    const SECOND_PHI:&str="let mut c:Root=Root{middle:Middle{leaf:Leaf{n:11},sibling:12},other:13};\
        let mut d:Root=Root{middle:Middle{leaf:Leaf{n:14},sibling:15},other:16};\
        let older=if false{&mut c}else{&mut d};let gap:i64=8;";
    fn lower(body:&str,alter:impl FnOnce(&mut HashMap<String,VerifiedCallSummary>))
        ->Option<FunctionMir>{
        let code=format!("{SOURCE}{body}");
        let tokens=crate::syntax::lex(&code).expect("valid ownership regression tokens");
        let types=HashMap::from([
            ("Root".into(),vec![("middle".into(),ConstType::Named("Middle".into())),
                ("other".into(),ConstType::I64)]),
            ("Middle".into(),vec![("leaf".into(),leaf()),
                ("sibling".into(),ConstType::I64)]),
            ("Leaf".into(),vec![("n".into(),ConstType::I64)]),
        ]);
        let ids=HashMap::from([("Root".into(),TypeId(0)),
            ("Middle".into(),TypeId(1)),("Leaf".into(),TypeId(2))]);
        let names=vec!["Root".into(),"Middle".into(),"Leaf".into()];
        let enums=HashMap::new();let payloads=HashMap::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,
            types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        let m=mutable_root();
        let mut calls=HashMap::from([
            ("select_second".into(),verified(1,vec![m.clone(),m.clone()],vec![])),
            ("write_other".into(),verified(1,vec![m.clone(),m.clone()],vec![write(0,vec![ko()])])),
            ("write_selected".into(),verified(0,vec![m.clone(),m.clone()],vec![write(0,vec![ko()])])),
            ("write_two".into(),verified(0,vec![m.clone(),m.clone()],
                vec![write(0,vec![ko()]),write(1,vec![ko()])])),
            ("write_shared".into(),verified(0,vec![m.clone(),ConstType::Ref(Box::new(root()))],
                vec![write(0,vec![ko()])])),
            ("forward_leaf".into(),VerifiedCallSummary{
                parameters:vec![mutable_leaf()],field_writes:vec![],parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{parameter:0,fields:vec![],ty:mutable_leaf()}),
                returned_alternatives:vec![],path_cases:vec![],
            }),
        ]);
        alter(&mut calls);
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("typed MIR builder must not panic")
    }
    fn checked(body:&str)->FunctionMir{
        let mir=lower(body,|_|{}).expect("complete multiparameter returned PHI MIR");
        let conflicts=mir.verify().expect("well-formed provenance certificate");
        assert!(conflicts.is_empty(),"{conflicts:?}");mir
    }
    fn rejected(body:&str,alter:impl FnOnce(&mut HashMap<String,VerifiedCallSummary>))->bool{
        match lower(body,alter) {
            None=>true,
            Some(mir)=>mir.verify().map_or(true,|errors|!errors.is_empty()),
        }
    }
    fn calls(mir:&FunctionMir)->Vec<&Statement>{
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|s|
            matches!(s,Statement::Call{..})).collect()
    }
    fn stages(mir:&FunctionMir)->Vec<(SymbolId,SymbolId,Vec<RefOption>)>{
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::LatePhiReborrow{generation,source_generation,children,..}=s {
                Some((*source_generation,*generation,children.clone()))
            }else{None}).collect()
    }
    #[test]
    fn returned_second_parameter_is_selected_after_a_pure_two_arg_call(){
        let mir=checked(&format!("{SPARE}let child=select_second(&mut spare,old);let n=child.n;"));
        assert_eq!(calls(&mir).len(),1);
        let items=stages(&mir);assert_eq!(items.len(),2);
        assert_eq!(items[1].0,items[0].1);
        assert!(items[1].2.iter().all(|c|c.path.fields==vec![kr(),km()]));
    }
    #[test]
    fn correlated_write_to_other_parameter_precedes_late_phi_binding(){
        let mir=checked(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"));
        let statements=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .collect::<Vec<_>>();
        let at=statements.iter().position(|s|matches!(s,
            Statement::Call{name,..} if name=="write_other")).unwrap();
        let bound=statements.iter().position(|s|matches!(s,
            Statement::LatePhiReborrow{..})).unwrap();
        assert!(at<bound,"effects must precede the returned loan");
        let Statement::Call{effects,path_cases,..}=statements[at]else{unreachable!()};
        assert_eq!(effects.len(),1);
        assert_eq!(effects[0].kind,VerifiedEffectKind::Write);
        assert_eq!(effects[0].path.fields,vec![ko()]);
        assert_eq!(path_cases.len(),1);
        assert_eq!(path_cases[0].returned,None);
    }
    #[test]
    fn write_to_returned_source_is_checked_before_child_loan_is_created(){
        let mir=checked(&format!("{SPARE}let child=write_selected(old,&mut spare);let n=child.n;"));
        let Statement::Call{effects,..}=calls(&mir)[0]else{unreachable!()};
        assert_eq!(effects.len(),1);
        assert_eq!(effects[0].alternatives.len(),2);
        assert!(effects[0].alternatives.iter().all(|p|p.fields==vec![ko()]));
    }
    #[test]
    fn separate_effect_cases_remain_separate_witnesses(){
        let mir=checked(&format!("{SPARE}let child=write_two(old,&mut spare);let n=child.n;"));
        let Statement::Call{effects,path_cases,..}=calls(&mir)[0]else{unreachable!()};
        assert_eq!(effects.len(),2);
        assert_eq!(path_cases.len(),2);
        assert!(path_cases.iter().all(|c|c.effects.len()==1 && c.returned.is_none()));
        assert!(path_cases.iter().any(|c|c.effects[0].alternatives.len()==2));
        assert!(path_cases.iter().any(|c|c.effects[0].alternatives.is_empty()));
    }
    #[test]
    fn shared_extra_parameter_does_not_destroy_mutable_return(){
        let mir=checked(&format!("{SPARE}let child=write_shared(old,&spare);let n=child.n;"));
        assert_eq!(stages(&mir).len(),2);
    }
    #[test]
    fn two_independent_mutable_phi_groups_can_participate_in_effectful_call(){
        let mir=checked(&format!("{SECOND_PHI}let child=write_other(older,old);let n=child.n;"));
        let Statement::Call{effects,..}=calls(&mir)[0]else{unreachable!()};
        assert_eq!(effects.len(),1);
        assert_eq!(effects[0].alternatives.len(),2);
        let chain=stages(&mir);
        assert_eq!(chain.len(),2);
        assert!(chain[0].2.iter().all(|o|o.path.fields==vec![kr()]));
    }
    #[test]
    fn returned_chain_can_forward_through_a_subsequent_verified_call(){
        let mir=checked(&format!("{SPARE}let child=write_other(&mut spare,old);\
            let again=forward_leaf(child);let n=again.n;"));
        let chain=stages(&mir);
        assert_eq!(chain.len(),3);
        assert_eq!(chain[2].0,chain[1].1);
    }
    #[test]
    fn independent_owned_sibling_remains_usable_after_effectful_call(){
        let _=checked(&format!("{SPARE}let child=write_other(&mut spare,old);\
            let moved:Root=spare;let n=child.n;"));
    }
    #[test]
    fn source_parent_is_suspended_during_projected_mutable_child(){
        assert!(rejected(&format!("{SPARE}let child=write_other(&mut spare,old);\
            let n=old.middle.leaf.n;let v=child.n;"), |_|{}));
    }
    #[test]
    fn overlapping_extra_mutable_argument_cannot_bypass_phi_exclusivity(){
        assert!(rejected("let child=write_selected(old,&mut a);let n=child.n;", |_|{}));
    }
    #[test]
    fn missing_effect_path_cases_cannot_certify_effectful_return(){
        assert!(rejected(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"),
            |calls|calls.get_mut("write_other").unwrap().path_cases.clear()));
    }
    #[test]
    fn incomplete_effect_cases_cannot_certify_return(){
        assert!(rejected(&format!("{SPARE}let child=write_two(old,&mut spare);let n=child.n;"),
            |calls|calls.get_mut("write_two").unwrap().path_cases.pop().map(|_|()).unwrap()));
    }
    #[test]
    fn forged_return_origin_case_cannot_certify_mutable_return(){
        assert!(rejected(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"),
            |calls|calls.get_mut("write_other").unwrap().path_cases[0].returned=Some(1)));
    }
    #[test]
    fn unproven_move_through_reference_cannot_be_hidden_in_may_summary(){
        assert!(rejected(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"),
            |calls|calls.get_mut("write_other").unwrap().parameter_effects[0].kind=
                VerifiedEffectKind::Move));
    }
    #[test]
    fn wrong_typed_return_projection_cannot_certify_late_chain(){
        assert!(rejected(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"),
            |calls|calls.get_mut("write_other").unwrap().returned.as_mut().unwrap().fields[1]=
                FieldKey{aggregate:TypeId(42),field:FieldId(0)}));
    }
    #[test]
    fn wrong_result_type_cannot_certify_late_chain(){
        assert!(rejected(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"),
            |calls|calls.get_mut("write_other").unwrap().returned.as_mut().unwrap().ty=
                mutable_root()));
    }
    #[test]
    fn write_through_shared_parameter_cannot_certify_return(){
        assert!(rejected(&format!("{SPARE}let child=write_shared(old,&spare);let n=child.n;"),
            |calls|{
                let c=calls.get_mut("write_shared").unwrap();
                let forged=write(1,vec![ko()]);
                c.parameter_effects.push(forged.clone());
                c.field_writes.push(VerifiedFieldWrite{parameter:1,fields:vec![ko()]});
                c.path_cases.push(VerifiedPathCase{effects:vec![forged],
                    returned:Some(0),uninitialized:vec![]});
            }));
    }
    #[test]
    fn partial_field_write_without_a_may_witness_is_rejected(){
        assert!(rejected(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"),
            |calls|calls.get_mut("write_other").unwrap().field_writes.push(
                VerifiedFieldWrite{parameter:1,fields:vec![ko()]})));
    }
    #[test]
    fn a_forged_late_parent_loan_is_rejected_by_mir_verifier(){
        let mut mir=checked(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"));
        let mut changed=false;
        for block in &mut mir.blocks {for s in &mut block.statements {
            if let Statement::LatePhiReborrow{children,..}=s {
                children[0].parent=Some(SymbolId(u32::MAX));changed=true;break;
            }
        }if changed{break;}}
        assert!(changed);
        assert!(mir.verify().is_err());
    }
    #[test]
    fn same_mutable_phi_cannot_be_two_simultaneous_call_arguments(){
        assert!(rejected("let child=write_selected(old,old);let n=child.n;", |_|{}),
            "two mutable parameters cannot alias the same PHI generation");
    }
    #[test]
    fn identical_phi_arguments_cannot_be_excused_by_second_parameter_return(){
        assert!(rejected("let child=select_second(old,old);let n=child.n;", |_|{}),
            "the returned position cannot excuse simultaneous mutable aliasing");
    }
    #[test]
    fn multi_origin_return_is_not_forged_from_a_single_source(){
        assert!(rejected(&format!("{SPARE}let child=write_other(&mut spare,old);let n=child.n;"),
            |calls|{
                let s=calls.get_mut("write_other").unwrap();
                s.returned_alternatives.push(s.returned.as_ref().unwrap().clone());
            }));
    }
}


#[cfg(test)]
mod staged_effectful_multi_return_0669_tests {
    use super::*;
    fn root()->ConstType {ConstType::Named("Root".into())}
    fn leaf()->ConstType {ConstType::Named("Leaf".into())}
    fn field_root_middle()->FieldKey {FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn field_middle_leaf()->FieldKey {FieldKey{aggregate:TypeId(1),field:FieldId(0)}}
    fn field_root_other()->FieldKey {FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn mutable_root()->ConstType {ConstType::RefMut(Box::new(root()))}
    fn mutable_leaf()->ConstType {ConstType::RefMut(Box::new(leaf()))}
    fn write(parameter:usize)->VerifiedParameterEffect {
        VerifiedParameterEffect{parameter,fields:vec![field_root_other()],
            kind:VerifiedEffectKind::Write}
    }
    fn summary()->VerifiedCallSummary {
        let w0=write(0);let w1=write(1);
        VerifiedCallSummary{
            parameters:vec![mutable_root(),mutable_root()],
            field_writes:vec![VerifiedFieldWrite{parameter:0,
                fields:w0.fields.clone()},VerifiedFieldWrite{parameter:1,
                fields:w1.fields.clone()}],
            parameter_effects:vec![w0.clone(),w1.clone()],
            returned:None,
            returned_alternatives:(0..2).map(|parameter|VerifiedReturnedReference{
                parameter,fields:vec![field_root_middle(),field_middle_leaf()],
                ty:mutable_leaf(),
            }).collect(),
            path_cases:vec![
                VerifiedPathCase{effects:vec![w1],returned:Some(0),uninitialized:vec![]},
                VerifiedPathCase{effects:vec![w0],returned:Some(1),uninitialized:vec![]},
            ],
        }
    }
    const ROOTS:&str="let mut a:Root=Root{middle:Middle{leaf:Leaf{n:1}},other:2,spare:Leaf{n:3}};\
        let mut b:Root=Root{middle:Middle{leaf:Leaf{n:4}},other:5,spare:Leaf{n:6}};";
    fn lower(body:&str,change:impl FnOnce(&mut VerifiedCallSummary))->Option<FunctionMir>{
        let source=format!("{ROOTS}{body}");
        let tokens=crate::syntax::lex(&source).expect("valid regression tokens");
        let types=HashMap::from([
            ("Root".into(),vec![("middle".into(),ConstType::Named("Middle".into())),
                ("other".into(),ConstType::I64),("spare".into(),leaf())]),
            ("Middle".into(),vec![("leaf".into(),leaf())]),
            ("Leaf".into(),vec![("n".into(),ConstType::I64)]),
        ]);
        let ids=HashMap::from([("Root".into(),TypeId(0)),
            ("Middle".into(),TypeId(1)),("Leaf".into(),TypeId(2))]);
        let names=vec!["Root".into(),"Middle".into(),"Leaf".into()];
        let enums=HashMap::new();let payloads=HashMap::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,
            types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        let mut sig=summary();change(&mut sig);
        let calls=HashMap::from([("choose".into(),sig)]);
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("lowering should never panic")
    }
    const CALL:&str="let result=choose(&mut a,&mut b);let value=result.n;";
    fn checked(body:&str)->FunctionMir {
        let mir=lower(body,|_|{}).expect("complete staged relational return MIR");
        let conflicts=mir.verify().expect("verified staged provenance");
        assert!(conflicts.is_empty(),"{conflicts:?}");
        mir
    }
    fn rejected(body:&str,mutate:impl FnOnce(&mut VerifiedCallSummary))->bool {
        match lower(body,mutate){
            None=>true,
            Some(mir)=>mir.verify().map_or(true,|c|!c.is_empty()),
        }
    }
    fn return_options(mir:&FunctionMir)->Vec<RefOption> {
        mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|stmt|
            match stmt {
                Statement::ValuePhi{ty:ConstType::RefMut(_),alternatives,..}
                    if alternatives.len()==2=>Some(alternatives.clone()),
                _=>None,
            }).expect("staged multi-origin returned reference PHI")
    }
    fn alternatives(mir:&FunctionMir)->Vec<&BasicBlock>{
        mir.blocks.iter().filter(|block|block.statements.iter().any(|s|
            matches!(s,Statement::Call{name,..} if name=="choose"))).collect()
    }
    #[test]
    fn different_returned_sources_have_distinct_staged_loans(){
        let mir=checked(CALL);
        let opts=return_options(&mir);
        assert_eq!(opts.len(),2);
        assert_ne!(opts[0].path.owner,opts[1].path.owner);
        assert_ne!(opts[0].loan,opts[1].loan);
        assert!(opts.iter().all(|option|option.exclusive && option.parent.is_some() &&
            option.path.fields==vec![field_root_middle(),field_middle_leaf()]));
    }
    #[test]
    fn each_call_branch_has_two_typed_projected_reborrows(){
        let mir=checked(CALL);
        assert_eq!(alternatives(&mir).len(),2);
        for block in alternatives(&mir){
            let borrows=block.statements.iter().filter_map(|stmt|match stmt {
                Statement::Access(event) if event.op==Access::BorrowMut &&
                    event.path.fields.len()>0=>Some(event),_=>None,
            }).collect::<Vec<_>>();
            assert_eq!(borrows.len(),2);
            assert_eq!(borrows[0].path.fields,vec![field_root_middle()]);
            assert_eq!(borrows[1].path.fields,vec![field_root_middle(),field_middle_leaf()]);
            assert_eq!(borrows[1].parent,borrows[0].loan);
        }
    }
    #[test]
    fn returned_loans_keep_the_immediate_intermediate_parent(){
        let mir=checked(CALL);
        for option in return_options(&mir){
            let parent=option.parent.expect("intermediate parent");
            let path=mir.loans.get(&parent).expect("registered parent path");
            assert_eq!(path.fields,vec![field_root_middle()]);
            assert!(path.ancestor_of(&option.path));
        }
    }
    #[test]
    fn side_effects_precede_the_first_projected_borrow(){
        let mir=checked(CALL);
        for block in alternatives(&mir){
            let call=block.statements.iter().position(|s|
                matches!(s,Statement::Call{name,..} if name=="choose")).unwrap();
            let child=block.statements.iter().position(|s|
                matches!(s,Statement::Access(Event{op:Access::BorrowMut,path,..})
                    if !path.fields.is_empty())).unwrap();
            assert!(call<child);
        }
    }
    #[test]
    fn origin_correlates_exactly_with_its_write_case(){
        let mir=checked(CALL);
        let branches=alternatives(&mir);
        assert_eq!(branches.len(),2);
        for (index,block) in branches.iter().enumerate(){
            let Statement::Call{effects,path_cases,..}=block.statements.iter()
                .find(|s|matches!(s,Statement::Call{name,..} if name=="choose"))
                .unwrap()else{unreachable!()};
            assert_eq!(effects.len(),1);
            assert_eq!(path_cases.len(),1);
            assert_eq!(path_cases[0].returned,Some(0));
            assert_eq!(effects[0].kind,VerifiedEffectKind::Write);
            assert_eq!(effects[0].path.fields,vec![field_root_other()]);
            let returned=return_options(&mir);
            assert_ne!(effects[0].path.owner,returned[index].path.owner);
        }
    }
    #[test]
    fn partial_move_of_disjoint_sibling_remains_legal(){
        let _=checked("let result=choose(&mut a,&mut b);\
            let taken:Leaf=a.spare;let value=result.n;");
    }
    #[test]
    fn use_after_move_of_possible_return_source_is_not_certified(){
        for owner in ["a","b"]{
            let src=format!("let result=choose(&mut a,&mut b);\
                let taken:Root={owner};let value=result.n;");
            assert!(rejected(&src,|_|{}),"moved possible returned owner {owner}");
        }
    }
    #[test]
    fn two_simultaneous_mutable_arguments_cannot_be_same_place(){
        assert!(rejected("let result=choose(&mut a,&mut a);let value=result.n;",|_|{}));
    }
    #[test]
    fn missing_return_origin_case_fails_closed(){
        assert!(rejected(CALL,|s|{s.path_cases.pop();}));
    }
    #[test]
    fn missing_may_write_witness_fails_closed(){
        assert!(rejected(CALL,|s|{s.path_cases[0].effects.clear();}));
    }
    #[test]
    fn invented_write_case_is_not_a_certificate(){
        assert!(rejected(CALL,|s|{
            s.path_cases[0].effects.push(VerifiedParameterEffect{
                parameter:0,fields:vec![field_root_middle()],
                kind:VerifiedEffectKind::Write,
            });
        }));
    }
    #[test]
    fn move_through_mutable_reference_cannot_be_certified(){
        assert!(rejected(CALL,|s|{
            let bad=VerifiedParameterEffect{parameter:0,fields:vec![],
                kind:VerifiedEffectKind::Move};
            s.parameter_effects.push(bad.clone());
            s.path_cases[0].effects.push(bad);
        }));
    }
    #[test]
    fn forged_return_field_type_is_rejected(){
        assert!(rejected(CALL,|s|{
            s.returned_alternatives[0].fields[1]=FieldKey{
                aggregate:TypeId(u32::MAX),field:FieldId(0),
            };
        }));
    }
    #[test]
    fn wrong_return_reference_type_is_rejected(){
        assert!(rejected(CALL,|s|{
            s.returned_alternatives[1].ty=mutable_root();
        }));
    }
    #[test]
    fn direct_return_missing_effect_case_is_incomplete_not_internal_error(){
        assert!(lower("return choose(&mut a,&mut b);",|summary|{
            summary.path_cases[0].effects.clear();
        }).is_none());
    }
    #[test]
    fn direct_return_mixed_reference_types_are_incomplete_not_internal_error(){
        assert!(lower("return choose(&mut a,&mut b);",|summary|{
            summary.returned_alternatives[1].ty=mutable_root();
        }).is_none());
    }
    #[test]
    fn forged_intermediate_parent_id_rejected_by_verifier(){
        let mut mir=checked(CALL);
        let mut altered=false;
        for block in &mut mir.blocks {for stmt in &mut block.statements {
            if let Statement::Access(ev)=stmt {
                if ev.op==Access::BorrowMut && ev.path.fields.len()==2 {
                    ev.parent=Some(SymbolId(u32::MAX));altered=true;break;
                }
            }
        }if altered{break;}}
        assert!(altered);
        assert!(mir.verify().is_err() || mir.verify().unwrap().len()>0);
    }
    #[test]
    fn no_premature_return_effect_hoisting_across_branch(){
        let mir=checked(CALL);
        for block in alternatives(&mir) {
            let mut has_call=false;
            for statement in &block.statements {
                match statement {
                    Statement::Call{name,..} if name=="choose"=>has_call=true,
                    Statement::Access(Event{op:Access::BorrowMut,path,..})
                        if !path.fields.is_empty()=>assert!(has_call),
                    _=>(),
                }
            }
        }
    }
}

#[cfg(test)]
mod joint_symbolic_effectful_returns_0670_tests {
    use super::*;
    fn root()->ConstType {ConstType::Named("Root".into())}
    fn leaf()->ConstType {ConstType::Named("Leaf".into())}
    fn root_middle()->FieldKey {FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn middle_leaf()->FieldKey {FieldKey{aggregate:TypeId(1),field:FieldId(0)}}
    fn root_other()->FieldKey {FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn mutable_root()->ConstType {ConstType::RefMut(Box::new(root()))}
    fn mutable_leaf()->ConstType {ConstType::RefMut(Box::new(leaf()))}
    fn write(p:usize)->VerifiedParameterEffect {VerifiedParameterEffect{
        parameter:p,fields:vec![root_other()],kind:VerifiedEffectKind::Write}}
    fn summary()->VerifiedCallSummary {
        let wa=write(0);let wb=write(1);
        VerifiedCallSummary{
            parameters:vec![mutable_root(),mutable_root()],
            field_writes:vec![VerifiedFieldWrite{parameter:0,fields:wa.fields.clone()},
                VerifiedFieldWrite{parameter:1,fields:wb.fields.clone()}],
            parameter_effects:vec![wa.clone(),wb.clone()],
            returned:None,
            returned_alternatives:(0..2).map(|parameter|VerifiedReturnedReference{
                parameter,fields:vec![root_middle(),middle_leaf()],ty:mutable_leaf(),
            }).collect(),
            path_cases:vec![
                VerifiedPathCase{effects:vec![wb],returned:Some(0),uninitialized:vec![]},
                VerifiedPathCase{effects:vec![wa],returned:Some(1),uninitialized:vec![]},
            ],
        }
    }
    const OWNERS:&str="let mut a:Root=Root{middle:Middle{leaf:Leaf{n:1}},other:2};\
        let mut b:Root=Root{middle:Middle{leaf:Leaf{n:3}},other:4};\
        let mut c:Root=Root{middle:Middle{leaf:Leaf{n:5}},other:6};\
        let mut d:Root=Root{middle:Middle{leaf:Leaf{n:7}},other:8};";
    const PHIS:&str="let left=if true{&mut a}else{&mut b};\
        let right=if true{&mut c}else{&mut d};";
    const CALL:&str="let result=choose(left,right);let read=result.n;";
    fn lower(body:&str,change:impl FnOnce(&mut VerifiedCallSummary))->Option<FunctionMir>{
        let source=format!("{OWNERS}{body}");
        let tokens=crate::syntax::lex(&source).expect("valid compiler regression tokens");
        let types=HashMap::from([
            ("Root".into(),vec![("middle".into(),ConstType::Named("Middle".into())),
                ("other".into(),ConstType::I64)]),
            ("Middle".into(),vec![("leaf".into(),leaf())]),
            ("Leaf".into(),vec![("n".into(),ConstType::I64)]),
        ]);
        let ids=HashMap::from([("Root".into(),TypeId(0)),
            ("Middle".into(),TypeId(1)),("Leaf".into(),TypeId(2))]);
        let names=vec!["Root".into(),"Middle".into(),"Leaf".into()];
        let enums=HashMap::new();let payloads=HashMap::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,
            types:&types,type_ids:&ids,type_names:&names,
            methods:&methods,verified_effects:&effects};
        let mut certificate=summary();change(&mut certificate);
        let calls=HashMap::from([("choose".into(),certificate)]);
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("invalid certificate must fail closed, not cause lowering error")
    }
    fn checked(body:&str)->FunctionMir {
        let mir=lower(body,|_|{}).expect("complete relational late PHI MIR");
        let conflicts=mir.verify().expect("well-formed symbolic result PHI");
        assert!(conflicts.is_empty(),"{conflicts:?}");mir
    }
    fn rejected(body:&str,change:impl FnOnce(&mut VerifiedCallSummary))->bool {
        match lower(body,change){None=>true,Some(mir)=>mir.verify()
            .map_or(true,|conflicts|!conflicts.is_empty())}
    }
    fn phis(mir:&FunctionMir)->Vec<(SymbolId,Vec<RefOption>)> {
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|{
            if let Statement::ValuePhi{generation:Some(id),alternatives,..}=stmt {
                Some((*id,alternatives.clone()))
            }else{None}
        }).collect()
    }
    fn stages(mir:&FunctionMir)->Vec<(SymbolId,SymbolId,Vec<RefOption>)> {
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|{
            if let Statement::LatePhiReborrow{source_generation,generation,children,..}=stmt{
                Some((*source_generation,*generation,children.clone()))
            }else{None}
        }).collect()
    }
    #[test]
    fn two_independent_mut_phis_produce_four_typed_return_candidates(){
        let mir=checked(&format!("{PHIS}{CALL}"));
        let groups=phis(&mir);
        assert_eq!(groups.iter().map(|(_,v)|v.len()).collect::<Vec<_>>(),vec![2,2,4]);
        let out=&groups[2].1;
        assert_eq!(out.iter().map(|o|o.loan).collect::<HashSet<_>>().len(),4);
        assert_eq!(out.iter().map(|o|o.path.owner).collect::<HashSet<_>>().len(),4);
        assert!(out.iter().all(|o|o.exclusive && o.parent.is_some() &&
            o.path.fields==vec![root_middle(),middle_leaf()]));
    }
    #[test]
    fn two_return_origins_remain_mutually_exclusive_calls(){
        let mir=checked(&format!("{PHIS}{CALL}"));
        let calls=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|s|
            matches!(s,Statement::Call{name,..} if name=="choose")).count();
        assert_eq!(calls,2);
        assert_eq!(stages(&mir).len(),4);
    }
    #[test]
    fn each_branch_uses_its_own_write_effect_witness(){
        let mir=checked(&format!("{PHIS}{CALL}"));
        let mut effects=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|
            if let Statement::Call{name,effects,path_cases,..}=s {
                (name=="choose").then_some((effects,path_cases))
            }else{None}).collect::<Vec<_>>();
        assert_eq!(effects.len(),2);
        for (actual,cases) in effects.drain(..){
            assert_eq!(actual.len(),1);
            assert_eq!(cases.len(),1);
            assert_eq!(cases[0].effects.as_slice(),actual.as_slice());
            assert!(actual[0].alternatives.len()==2);
            assert_eq!(actual[0].kind,VerifiedEffectKind::Write);
            assert!(actual[0].alternatives.iter().all(|path|
                path.fields==vec![root_other()]));
        }
    }
    #[test]
    fn late_binding_preserves_both_input_generations(){
        let mir=checked(&format!("{PHIS}{CALL}"));
        let groups=phis(&mir);let stage=stages(&mir);
        assert_eq!(stage.len(),4);
        assert_eq!(stage[0].0,groups[0].0);
        assert_eq!(stage[2].0,groups[1].0);
        assert_eq!(stage[1].0,stage[0].1);
        assert_eq!(stage[3].0,stage[2].1);
    }
    #[test]
    fn projected_child_loans_preserve_exact_parent_chain(){
        let mir=checked(&format!("{PHIS}{CALL}"));
        let groups=phis(&mir);let stages=stages(&mir);
        for (i,source) in [(0,0),(2,1)] {
            for (initial,middle) in groups[source].1.iter().zip(&stages[i].2) {
                assert_eq!(middle.parent,Some(initial.loan));
                assert_eq!(middle.path,initial.path.child(root_middle()));
            }
            for (middle,last) in stages[i].2.iter().zip(&stages[i+1].2){
                assert_eq!(last.parent,Some(middle.loan));
                assert_eq!(last.path,middle.path.child(middle_leaf()));
            }
        }
    }
    #[test]
    fn write_effect_must_happen_before_late_reborrow_on_each_branch(){
        let mir=checked(&format!("{PHIS}{CALL}"));
        let mut witnessed=0;
        for block in &mir.blocks {
            let call=block.statements.iter().position(|s|
                matches!(s,Statement::Call{name,..} if name=="choose"));
            if let Some(call)=call {
                let late=block.statements.iter().position(|s|
                    matches!(s,Statement::LatePhiReborrow{..})).unwrap();
                assert!(call<late);witnessed+=1;
            }
        }
        assert_eq!(witnessed,2);
    }
    #[test]
    fn unrelated_owned_value_can_be_moved(){
        let src=format!("{PHIS}let independent:Leaf=Leaf{{n:12}};\
            let result=choose(left,right);let moved:Leaf=independent;let n=result.n;");
        let _=checked(&src);
    }
    #[test]
    fn every_possible_source_remains_borrowed(){
        for owner in ["a","b","c","d"]{
            let src=format!("{PHIS}let result=choose(left,right);\
                let moved:Root={owner};let n=result.n;");
            assert!(rejected(&src,|_|{}),"moved potential returned parent {owner}");
        }
    }
    #[test]
    fn one_phi_cannot_be_passed_twice_as_mut(){
        assert!(rejected(&format!("{PHIS}let result=choose(left,left);let n=result.n;"),|_|{}));
    }
    #[test]
    fn independent_phi_groups_with_possible_overlapping_owner_are_rejected(){
        let src=format!("{OWNERS}let left=if true{{&mut a}}else{{&mut b}};\
            let right=if true{{&mut a}}else{{&mut c}};{CALL}");
        let body=src.strip_prefix(OWNERS).unwrap();
        assert!(rejected(body,|_|{}));
    }
    #[test]
    fn missing_return_origin_case_rejects_entire_certificate(){
        assert!(rejected(&format!("{PHIS}{CALL}"),|s|{s.path_cases.pop();}));
    }
    #[test]
    fn missing_may_write_witness_cannot_be_hidden_by_an_origin(){
        assert!(rejected(&format!("{PHIS}{CALL}"),|s|{s.path_cases[0].effects.clear();}));
    }
    #[test]
    fn invented_effect_case_cannot_become_a_proof(){
        assert!(rejected(&format!("{PHIS}{CALL}"),|s|{
            s.path_cases[0].effects.push(VerifiedParameterEffect{
                parameter:0,fields:vec![root_middle()],kind:VerifiedEffectKind::Write});
        }));
    }
    #[test]
    fn move_or_drop_via_mutable_phi_is_not_certified(){
        for kind in [VerifiedEffectKind::Move,VerifiedEffectKind::Drop]{
            assert!(rejected(&format!("{PHIS}{CALL}"),|s|{
                let effect=VerifiedParameterEffect{parameter:0,fields:vec![],kind};
                s.parameter_effects.push(effect.clone());
                s.path_cases[0].effects.push(effect);
            }));
        }
    }
    #[test]
    fn forged_type_qualified_return_field_is_rejected(){
        assert!(rejected(&format!("{PHIS}{CALL}"),|s|{
            s.returned_alternatives[0].fields[1]=FieldKey{
                aggregate:TypeId(u32::MAX),field:FieldId(0)};
        }));
    }
    #[test]
    fn returned_phi_cannot_omit_one_conditional_child(){
        let mut mir=checked(&format!("{PHIS}{CALL}"));
        let mut damaged=false;
        for block in &mut mir.blocks {for statement in &mut block.statements {
            if let Statement::ValuePhi{alternatives,..}=statement {
                if alternatives.len()==4 {
                    alternatives.pop();damaged=true;break;
                }
            }
        }if damaged{break;}}
        assert!(damaged);
        assert!(mir.verify().is_err());
    }
    #[test]
    fn child_projection_cannot_escape_its_actual_parent_path(){
        let mut mir=checked(&format!("{PHIS}{CALL}"));
        let mut altered=false;
        for block in &mut mir.blocks {for statement in &mut block.statements {
            if let Statement::LatePhiReborrow{children,projection:Some(key),..}=statement {
                if *key==middle_leaf(){
                    children[0].path.fields[0]=root_other();
                    altered=true;break;
                }
            }
        }if altered{break;}}
        assert!(altered);
        assert!(mir.verify().is_err());
    }
    #[test]
    fn forged_intermediate_loan_parent_is_rejected(){
        let mut mir=checked(&format!("{PHIS}{CALL}"));
        let mut changed=false;
        for block in &mut mir.blocks {for statement in &mut block.statements{
            if let Statement::LatePhiReborrow{children,projection:Some(key),..}=statement {
                if *key==middle_leaf() {
                    children[0].parent=Some(SymbolId(u32::MAX));changed=true;break;
                }
            }
        }if changed{break;}}
        assert!(changed);
        assert!(mir.verify().is_err());
    }
}

#[cfg(test)]
mod nested_interprocedural_nll_0671_tests {
    use super::*;

    fn reference(pointee:ConstType,mutable:bool)->ConstType {
        if mutable {ConstType::RefMut(Box::new(pointee))}
        else {ConstType::Ref(Box::new(pointee))}
    }
    fn forward(ty:ConstType)->VerifiedCallSummary {
        VerifiedCallSummary{
            parameters:vec![ty.clone()],field_writes:vec![],parameter_effects:vec![],
            returned:Some(VerifiedReturnedReference{
                parameter:0,fields:vec![],ty,
            }),returned_alternatives:vec![],path_cases:vec![],
        }
    }
    pub(super) fn lower(source:&str,mutate:impl FnOnce(&mut HashMap<String,VerifiedCallSummary>))
        ->Option<FunctionMir> {
        let tokens=crate::syntax::lex(source).expect("valid nested call tokens");
        let types=HashMap::from([("Blob".to_owned(),vec![
            ("n".to_owned(),ConstType::I64),
            ("other".to_owned(),ConstType::I64),
        ])]);
        let ids=HashMap::from([("Blob".to_owned(),TypeId(0))]);
        let names=vec!["Blob".to_owned()];
        let enums=HashMap::new();let payloads=HashMap::new();
        let methods=HashMap::new();let effects=HashMap::new();
        let schema=Schema{enums:&enums,enum_payloads:&payloads,types:&types,
            type_ids:&ids,type_names:&names,methods:&methods,verified_effects:&effects};
        let scalar=ConstType::I64;
        let blob=ConstType::Named("Blob".into());
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let mut calls=HashMap::from([
            ("f".to_owned(),forward(reference(scalar.clone(),true))),
            ("s".to_owned(),forward(reference(scalar.clone(),false))),
            ("choose_left".to_owned(),VerifiedCallSummary{
                parameters:vec![reference(scalar.clone(),true),reference(scalar.clone(),true)],
                field_writes:vec![],parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{parameter:0,fields:vec![],
                    ty:reference(scalar.clone(),true)}),
                returned_alternatives:vec![],path_cases:vec![],
            }),
            ("choose_right".to_owned(),VerifiedCallSummary{
                parameters:vec![reference(scalar.clone(),true),reference(scalar.clone(),true)],
                field_writes:vec![],parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{parameter:1,fields:vec![],
                    ty:reference(scalar.clone(),true)}),
                returned_alternatives:vec![],path_cases:vec![],
            }),
            ("copy_then_ref".to_owned(),VerifiedCallSummary{
                parameters:vec![scalar.clone(),reference(scalar.clone(),true)],
                field_writes:vec![],parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{parameter:1,fields:vec![],
                    ty:reference(scalar.clone(),true)}),
                returned_alternatives:vec![],path_cases:vec![],
            }),
            ("owned_then_ref".to_owned(),VerifiedCallSummary{
                parameters:vec![blob.clone(),reference(scalar.clone(),true)],
                field_writes:vec![],parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{parameter:1,fields:vec![],
                    ty:reference(scalar.clone(),true)}),
                returned_alternatives:vec![],path_cases:vec![],
            }),
            ("choose_blob_right".to_owned(),VerifiedCallSummary{
                parameters:vec![reference(blob.clone(),true),reference(blob.clone(),true)],
                field_writes:vec![],parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{parameter:1,fields:vec![],
                    ty:reference(blob.clone(),true)}),
                returned_alternatives:vec![],path_cases:vec![],
            }),
            ("blob".to_owned(),forward(reference(blob.clone(),true))),
            ("project".to_owned(),VerifiedCallSummary{
                parameters:vec![reference(blob.clone(),true)],
                field_writes:vec![],parameter_effects:vec![],
                returned:Some(VerifiedReturnedReference{parameter:0,
                    fields:vec![field],ty:reference(scalar,true)}),
                returned_alternatives:vec![],path_cases:vec![],
            }),
            ("write_blob".to_owned(),VerifiedCallSummary{
                parameters:vec![reference(blob.clone(),true)],
                field_writes:vec![VerifiedFieldWrite{parameter:0,fields:vec![field]}],
                parameter_effects:vec![VerifiedParameterEffect{parameter:0,
                    fields:vec![field],kind:VerifiedEffectKind::Write}],
                returned:Some(VerifiedReturnedReference{parameter:0,
                    fields:vec![],ty:reference(blob,true)}),
                returned_alternatives:vec![],path_cases:vec![],
            }),
        ]);
        mutate(&mut calls);
        lower_with_verified_calls(&tokens,0..tokens.len(),&[],&schema,&[],&calls)
            .expect("nested call lowering must never silently skip an error")
    }
    pub(super) fn certified(source:&str)->FunctionMir {
        let mir=lower(source,|_|{}).expect("complete typed nested call MIR");
        let errors=mir.verify().expect("valid nested call proof graph");
        assert!(errors.is_empty(),"{errors:?}");
        mir
    }
    pub(super) fn rejected(source:&str,mutate:impl FnOnce(&mut HashMap<String,VerifiedCallSummary>))->bool {
        match lower(source,mutate) {
            None=>true,
            Some(mir)=>mir.verify().map_or(true,|errors|!errors.is_empty()),
        }
    }
    #[test]
    fn nested_mutable_call_keeps_every_parent_generation() {
        let mir=certified("let mut a:i64=1;let r=f(f(f(&mut a)));*r=2;");
        let ordered=mir.blocks.iter().flat_map(|b|b.statements.iter()).collect::<Vec<_>>();
        assert_eq!(ordered.iter().filter(|s|matches!(s,Statement::Call{name,..} if name=="f")).count(),3);
        let links=ordered.iter().flat_map(|s|s.events()).filter(|e|
            e.op==Access::BorrowMut && e.parent.is_some()).count();
        assert!(links>=3,"each call result must have an exact parent reborrow");
    }
    #[test]
    fn shared_nested_calls_are_valid_without_an_exclusive_upgrade() {
        let _=certified("let a:i64=1;let r=s(s(&a));let n=*r;");
        assert!(rejected("let mut a:i64=1;let r=f(s(&a));*r=2;", |_|{}));
    }
    #[test]
    fn if_result_retains_branch_specific_nested_reborrow_chains() {
        let mir=certified("let mut a:i64=1;let mut b:i64=2;let r=if true{f(f(&mut a))}else{f(f(&mut b))};*r=3;");
        let out=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|
            if let Statement::ValuePhi{alternatives,..}=s {
                (alternatives.len()==2).then_some(alternatives)
            }else{None}).expect("two conditional origins");
        assert_ne!(out[0].path.owner,out[1].path.owner);
        assert!(out.iter().all(|o|o.exclusive && o.parent.is_some()));
    }
    #[test]
    fn exhaustive_match_retains_branch_specific_nested_reborrow_chains() {
        let _=certified("let mut a:i64=1;let mut b:i64=2;let r=match true{true=>{f(f(&mut a))},false=>{f(f(&mut b))}};*r=3;");
    }
    #[test]
    fn nested_if_and_match_preserve_the_original_owners() {
        let _=certified("let mut a:i64=1;let mut b:i64=2;let r=if true{match true{true=>{f(f(&mut a))},false=>{f(f(&mut b))}}}else{f(f(&mut b))};*r=3;");
    }
    #[test]
    fn nested_if_and_match_reject_a_write_to_the_other_possible_parent() {
        assert!(rejected("let mut a:i64=1;let mut b:i64=2;let r=if true{match true{true=>{f(f(&mut a))},false=>{f(f(&mut b))}}}else{f(f(&mut b))};b=5;*r=3;", |_|{}));
    }
    #[test]
    fn write_to_original_parent_before_nested_result_last_use_is_rejected() {
        assert!(rejected("let mut a:i64=1;let r=f(f(&mut a));a=5;*r=3;", |_|{}));
    }
    #[test]
    fn nested_projection_keeps_type_qualified_original_move_path() {
        let mir=certified("let mut a:Blob=Blob{n:1,other:2};let r=f(project(&mut a));*r=4;");
        let projected=mir.loans.values().find(|p|p.fields.len()==1)
            .expect("field-sensitive projected loan");
        assert_eq!(projected.fields[0],FieldKey{aggregate:TypeId(0),field:FieldId(0)});
        let mut forest=cfg_borrow::Forest::default();
        let path_id=forest.intern(projected).unwrap();
        let parent_id=forest.intern(&Path::root(projected.owner)).unwrap();
        assert_eq!(forest.nodes()[path_id.0 as usize].parent,Some(parent_id));
        assert_eq!(forest.intern(projected).unwrap(),path_id,
            "reborrows must reuse the original typed MovePathId");
    }
    #[test]
    fn verified_nested_write_effect_happens_before_next_mutable_reborrow() {
        let mir=certified("let mut a:Blob=Blob{n:1,other:2};let r=blob(write_blob(&mut a));r.n=7;");
        let statements=mir.blocks.iter().flat_map(|b|b.statements.iter()).collect::<Vec<_>>();
        let write=statements.iter().position(|s|matches!(s,
            Statement::Call{name,..} if name=="write_blob")).unwrap();
        let outer=statements.iter().position(|s|matches!(s,
            Statement::Call{name,..} if name=="blob")).unwrap();
        assert!(write<outer);
    }
    #[test]
    fn nested_lifetime_can_end_at_its_last_use_before_owner_write() {
        let _=certified("let mut a:i64=1;let r=f(f(&mut a));*r=2;a=4;let n=a;");
    }
    #[test]
    fn a_possible_match_parent_cannot_be_modified_while_child_is_used() {
        assert!(rejected("let mut a:i64=1;let mut b:i64=2;let r=match true{true=>{f(f(&mut a))},false=>{f(f(&mut b))}};a=5;*r=3;", |_|{}));
    }
    #[test]
    fn forged_mid_chain_parent_id_is_detected() {
        let mut mir=certified("let mut a:i64=1;let r=f(f(&mut a));*r=2;");
        let mut changed=false;
        for block in &mut mir.blocks {for stmt in &mut block.statements {
            if let Statement::Access(Event{op:Access::BorrowMut,parent:Some(parent),..})=stmt {
                *parent=SymbolId(u32::MAX);changed=true;break;
            }
        }if changed{break;}}
        assert!(changed,"test must alter a genuine nested reborrow parent");
        assert!(mir.verify().map_or(true,|errors|!errors.is_empty()));
    }
    #[test]
    fn forged_nested_return_projection_cannot_be_certified() {
        assert!(rejected("let mut a:Blob=Blob{n:1,other:2};let r=f(project(&mut a));*r=4;", |calls|{
            calls.get_mut("project").unwrap().returned.as_mut().unwrap().fields[0].aggregate=TypeId(99);
        }));
    }
    #[test]
    fn missing_nested_callee_proof_is_not_assumed_pure() {
        assert!(rejected("let mut a:i64=1;let r=f(f(&mut a));*r=3;", |calls|{calls.remove("f");}));
    }
    #[test]
    fn multi_origin_nested_return_is_not_guessed_from_one_branch() {
        assert!(rejected("let mut a:i64=1;let r=f(f(&mut a));*r=3;", |calls|{
            let summary=calls.get_mut("f").unwrap();
            let origin=summary.returned.take().unwrap();
            summary.returned_alternatives=vec![origin.clone(),origin];
        }));
    }
    #[test]
    fn nested_call_as_first_of_two_disjoint_args_preserves_mutable_provenance() {
        let _=certified("let mut a:i64=1;let mut b:i64=2;let r=choose_left(f(&mut a),&mut b);*r=3;");
    }
    #[test]
    fn overlapping_mutable_second_argument_conflicts_with_nested_first_arg() {
        assert!(rejected("let mut a:i64=1;let r=choose_left(f(&mut a),&mut a);*r=3;", |_|{}));
    }
    #[test]
    fn later_nested_argument_is_sequenced_after_previous_mutable_borrow() {
        let mir=certified("let mut a:i64=1;let mut b:i64=2;let r=choose_right(&mut b,f(&mut a));*r=3;");
        let ordered=mir.blocks.iter().flat_map(|b|b.statements.iter()).collect::<Vec<_>>();
        let inner=ordered.iter().position(|s|matches!(s,
            Statement::Call{name,..} if name=="f")).unwrap();
        let outer=ordered.iter().position(|s|matches!(s,
            Statement::Call{name,..} if name=="choose_right")).unwrap();
        let prior=ordered.iter().position(|s|matches!(s,
            Statement::Access(Event{op:Access::BorrowMut,parent:None,..}))).unwrap();
        assert!(prior<inner && inner<outer,"earlier argument must precede nested call");
    }
    #[test]
    fn two_nested_arguments_preserve_their_separate_parent_chains(){
        let mir=certified("let mut a:i64=1;let mut b:i64=2;let r=choose_right(f(&mut a),f(&mut b));*r=3;");
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|s|
            matches!(s,Statement::Call{name,..} if name=="f")).count(),2);
    }
    #[test]
    fn nested_second_argument_can_be_nested_multiple_levels(){
        let _=certified("let mut a:i64=1;let mut b:i64=2;let r=choose_right(&mut b,f(f(&mut a)));*r=3;");
    }
    #[test]
    fn same_owner_cannot_be_borrowed_mutably_twice_across_later_call(){
        assert!(rejected("let mut a:i64=1;let r=choose_right(&mut a,f(&mut a));*r=3;", |_|{}));
    }
    #[test]
    fn two_nested_arguments_cannot_reborrow_the_same_exclusive_owner(){
        assert!(rejected("let mut a:i64=1;let r=choose_right(f(&mut a),f(&mut a));*r=3;", |_|{}));
    }
    #[test]
    fn earlier_copy_read_completes_before_nested_mutable_borrow(){
        let _=certified("let mut a:i64=1;let r=copy_then_ref(a,f(&mut a));*r=3;");
    }
    #[test]
    fn earlier_owned_value_is_consumed_before_nested_evaluation(){
        let mir=certified("let mut a:Blob=Blob{n:1,other:2};let mut b:i64=3;let r=owned_then_ref(a,f(&mut b));*r=4;");
        let ordered=mir.blocks.iter().flat_map(|b|b.statements.iter()).collect::<Vec<_>>();
        let moved=ordered.iter().position(|s|matches!(s,
            Statement::Access(Event{op:Access::Move,..}))).unwrap();
        let nested=ordered.iter().position(|s|matches!(s,
            Statement::Call{name,..} if name=="f")).unwrap();
        assert!(moved<nested);
    }
    #[test]
    fn earlier_owned_move_cannot_be_undone_by_nested_call(){
        assert!(rejected("let mut a:Blob=Blob{n:1,other:2};let mut b:i64=3;let r=owned_then_ref(a,f(&mut b));let x=a.n;*r=4;", |_|{}));
    }
    #[test]
    fn late_nested_result_keeps_owner_borrowed_until_last_use(){
        assert!(rejected("let mut a:i64=1;let mut b:i64=2;let r=choose_right(&mut b,f(&mut a));a=4;*r=3;", |_|{}));
    }
    #[test]
    fn nonreturned_earlier_loan_ends_before_unrelated_owner_write(){
        let _=certified("let mut a:i64=1;let mut b:i64=2;let r=choose_right(&mut b,f(&mut a));b=4;*r=3;");
    }
    #[test]
    fn nonreturned_later_nested_loan_ends_before_unrelated_owner_write(){
        let _=certified("let mut a:i64=1;let mut b:i64=2;let r=choose_left(&mut b,f(&mut a));a=4;*r=3;");
    }
    #[test]
    fn nested_later_argument_can_write_through_a_disjoint_verified_callee(){
        let _=certified("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=choose_blob_right(&mut a,write_blob(&mut b));r.n=5;");
    }
    #[test]
    fn nested_later_argument_cannot_write_through_an_earlier_alias(){
        assert!(rejected("let mut a:Blob=Blob{n:1,other:2};let r=choose_blob_right(&mut a,write_blob(&mut a));r.n=5;", |_|{}));
    }
    #[test]
    fn later_nested_projection_preserves_exact_field_move_path(){
        let mir=certified("let mut a:Blob=Blob{n:1,other:2};let mut b:i64=2;let r=choose_right(&mut b,project(&mut a));*r=3;");
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        assert!(mir.loans.values().any(|path|path.fields==vec![field]));
        let path=mir.loans.values().find(|path|path.fields==vec![field]).unwrap();
        let mut forest=cfg_borrow::Forest::default();
        let id=forest.intern(path).unwrap();
        assert_eq!(forest.intern(path).unwrap(),id);
        let root=forest.intern(&Path::root(path.owner)).unwrap();
        assert_eq!(forest.nodes()[id.0 as usize].parent,Some(root));
    }
    #[test]
    fn if_branch_specific_later_nested_returns_remain_disjoint(){
        let _=certified("let mut a:i64=1;let mut b:i64=2;let r=if true{choose_right(&mut b,f(&mut a))}else{choose_right(&mut a,f(&mut b))};*r=3;");
    }
    #[test]
    fn match_branch_specific_later_nested_returns_remain_disjoint(){
        let _=certified("let mut a:i64=1;let mut b:i64=2;let r=match true{true=>{choose_right(&mut b,f(&mut a))},false=>{choose_right(&mut a,f(&mut b))}};*r=3;");
    }
    #[test]
    fn older_independent_mutable_phi_is_checked_before_later_nested_call(){
        let mir=certified("let mut a:i64=1;let mut b:i64=2;let mut c:i64=3;let older=if true{&mut a}else{&mut b};let r=choose_right(older,f(&mut c));*r=4;");
        assert!(mir.blocks.iter().flat_map(|b|b.statements.iter()).any(|s|
            matches!(s,Statement::Access(Event{op:Access::Write,loan:Some(_),..}))));
    }
    #[test]
    fn older_phi_possible_owner_cannot_alias_later_nested_exclusive_borrow(){
        assert!(rejected("let mut a:i64=1;let mut b:i64=2;let older=if true{&mut a}else{&mut b};let r=choose_right(older,f(&mut a));*r=4;", |_|{}));
    }
    #[test]
    fn forged_later_nested_parent_still_fails_verification(){
        let mut mir=certified("let mut a:i64=1;let mut b:i64=2;let r=choose_right(&mut b,f(&mut a));*r=3;");
        let mut altered=false;
        for block in &mut mir.blocks {for stmt in &mut block.statements {
            if let Statement::Access(Event{op:Access::BorrowMut,parent:Some(parent),..})=stmt {
                *parent=SymbolId(u32::MAX);altered=true;break;
            }
        }if altered{break;}}
        assert!(altered);
        assert!(mir.verify().map_or(true,|errors|!errors.is_empty()));
    }
    #[test]
    fn effectful_outer_boundary_uses_complete_split_argument_certificate(){
        let mir=lower("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=choose_blob_right(&mut a,write_blob(&mut b));r.n=5;", |calls|{
            let summary=calls.get_mut("choose_blob_right").unwrap();
            let effect=VerifiedParameterEffect{parameter:0,
                fields:vec![FieldKey{aggregate:TypeId(0),field:FieldId(0)}],
                kind:VerifiedEffectKind::Write};
            summary.field_writes.push(VerifiedFieldWrite{
                parameter:0,fields:effect.fields.clone()});
            summary.parameter_effects.push(effect.clone());
            summary.path_cases.push(VerifiedPathCase{
                effects:vec![effect],returned:Some(0),uninitialized:Vec::new()});
        }).expect("full outer effect proof should lower");
        assert!(mir.verify().expect("valid split alias proof").is_empty());
    }
    #[test]
    fn unknown_or_multiorigin_nested_second_call_is_not_guessed(){
        assert!(rejected("let mut a:i64=1;let mut b:i64=2;let r=choose_right(&mut b,f(&mut a));*r=3;", |calls|{
            let summary=calls.get_mut("f").unwrap();
            let origin=summary.returned.take().unwrap();
            summary.returned_alternatives=vec![origin.clone(),origin];
        }));
    }
    #[test]
    fn excessive_nesting_must_not_exhaust_the_compiler_stack() {
        let mut expression="&mut a".to_owned();
        for _ in 0..18 {expression=format!("f({expression})");}
        let body=format!("let mut a:i64=1;let r={expression};*r=2;");
        assert!(rejected(&body, |_|{}));
    }
}



#[cfg(test)]
mod ordered_effectful_outer_0673_tests {
    use super::*;
    use super::nested_interprocedural_nll_0671_tests::{lower,certified,rejected};

    fn write_outer(returned:usize,write:usize)->VerifiedCallSummary {
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let blob=ConstType::Named("Blob".into());
        let reference=ConstType::RefMut(Box::new(blob));
        let effect=VerifiedParameterEffect{parameter:write,fields:vec![field],
            kind:VerifiedEffectKind::Write};
        VerifiedCallSummary{
            parameters:vec![reference.clone(),reference.clone()],
            field_writes:vec![VerifiedFieldWrite{parameter:write,fields:vec![field]}],
            parameter_effects:vec![effect.clone()],
            returned:Some(VerifiedReturnedReference{parameter:returned,
                fields:vec![],ty:reference}),returned_alternatives:vec![],
            path_cases:vec![VerifiedPathCase{effects:vec![effect],
                returned:Some(0),uninitialized:vec![]}],
        }
    }
    fn with_outer(calls:&mut HashMap<String,VerifiedCallSummary>) {
        calls.insert("write_choose_right".into(),write_outer(1,0));
        calls.insert("write_choose_left".into(),write_outer(0,1));
    }
    fn ok(source:&str)->FunctionMir {
        let mir=lower(source,with_outer).expect("complete staged outer certificate");
        let errors=mir.verify().expect("typed alias proof verification");
        assert!(errors.is_empty(),"{errors:?}");
        mir
    }
    fn no(source:&str)->bool {rejected(source,with_outer)}

    #[test]
    fn staged_first_borrow_authorizes_outer_field_write_after_nested_second(){
        let mir=ok("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=write_choose_right(&mut a,write_blob(&mut b));r.n=5;");
        let statements=mir.blocks.iter().flat_map(|block|block.statements.iter())
            .collect::<Vec<_>>();
        let inner=statements.iter().position(|stmt|
            matches!(stmt,Statement::Call{name,..} if name=="write_blob")).unwrap();
        let outer=statements.iter().position(|stmt|
            matches!(stmt,Statement::Call{name,..} if name=="write_choose_right")).unwrap();
        assert!(inner<outer);
        let Statement::Call{effects,events,..}=statements[outer]else{panic!()};
        assert_eq!(effects.len(),1);
        assert!(events.iter().any(|event|event.op==Access::Write && event.loan.is_some()));
        assert!(!events.iter().any(|event|event.op==Access::BorrowMut &&
            event.loan==events.iter().find(|e|e.op==Access::Write).and_then(|e|e.loan)));
    }
    #[test]
    fn both_nested_inputs_can_supply_independent_effectful_arguments(){
        let _=ok("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=write_choose_right(write_blob(&mut a),write_blob(&mut b));r.n=8;");
    }
    #[test]
    fn returned_first_argument_remains_live_after_write_through_second(){
        let _=ok("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=write_choose_left(&mut a,write_blob(&mut b));r.other=6;");
    }
    #[test]
    fn nested_third_level_input_still_preserves_effectful_outer_order(){
        let _=ok("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=write_choose_right(&mut a,blob(write_blob(&mut b)));r.n=9;");
    }
    #[test]
    fn effectful_outer_inside_if_branches_has_independent_loan_histories(){
        let _=ok("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=if true{write_choose_right(&mut a,write_blob(&mut b))}else{write_choose_right(&mut b,write_blob(&mut a))};r.other=5;");
    }
    #[test]
    fn effectful_outer_inside_match_branches_has_independent_loan_histories(){
        let _=ok("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=match true{true=>{write_choose_right(&mut a,write_blob(&mut b))},false=>{write_choose_right(&mut b,write_blob(&mut a))}};r.other=5;");
    }
    #[test]
    fn overlapping_mutable_actuals_are_rejected_before_outer_write(){
        assert!(no("let mut a:Blob=Blob{n:1,other:2};let r=write_choose_right(&mut a,write_blob(&mut a));r.n=4;"));
        assert!(no("let mut a:Blob=Blob{n:1,other:2};let r=write_choose_right(write_blob(&mut a),write_blob(&mut a));r.n=4;"));
    }
    #[test]
    fn owner_cannot_be_modified_between_staged_loan_and_return_use(){
        assert!(no("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=write_choose_right(&mut a,write_blob(&mut b));b.n=6;r.n=3;"));
    }
    #[test]
    fn incomplete_or_forged_outer_may_effect_witness_fails_closed(){
        let src="let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=write_choose_right(&mut a,write_blob(&mut b));r.n=5;";
        assert!(rejected(src,|calls|{with_outer(calls);
            calls.get_mut("write_choose_right").unwrap().path_cases.clear();
        }));
        assert!(rejected(src,|calls|{with_outer(calls);
            calls.get_mut("write_choose_right").unwrap().path_cases[0].effects.clear();
        }));
        assert!(rejected(src,|calls|{with_outer(calls);
            calls.get_mut("write_choose_right").unwrap().field_writes[0].fields[0].aggregate=TypeId(999);
        }));
    }
    #[test]
    fn forged_outer_write_loan_cannot_claim_staged_capability(){
        let src="let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=write_choose_right(&mut a,write_blob(&mut b));r.n=5;";
        let mut mir=ok(src);
        let mut changed=false;
        for block in &mut mir.blocks {for statement in &mut block.statements {
            if let Statement::Call{name,events,..}=statement {
                if name!="write_choose_right"{continue;}
                let write=events.iter_mut().find(|e|e.op==Access::Write).unwrap();
                write.loan=Some(SymbolId(u32::MAX));changed=true;
            }
        }}
        assert!(changed);
        let result=mir.verify();
        assert!(result.is_err() || result.is_ok_and(|errors|!errors.is_empty()));
    }
    #[test]
    fn future_borrow_in_same_block_is_not_a_valid_call_write_witness(){
        let src="let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=write_choose_right(&mut a,write_blob(&mut b));r.n=5;";
        let mut mir=ok(src);
        let mut changed=false;
        for block in &mut mir.blocks {
            let Some(call_at)=block.statements.iter().position(|statement|
                matches!(statement,Statement::Call{name,..} if name=="write_choose_right"))
                else{continue};
            let write_loan=match &block.statements[call_at] {
                Statement::Call{events,..}=>events.iter()
                    .find(|event|event.op==Access::Write).and_then(|event|event.loan).unwrap(),
                _=>unreachable!(),
            };
            let prior=block.statements[..call_at].iter().position(|statement|
                matches!(statement,Statement::Access(Event{op:Access::BorrowMut,
                    loan:Some(id),..}) if *id==write_loan)).unwrap();
            let borrowed=block.statements.remove(prior);
            block.statements.insert(call_at,borrowed);
            changed=true;
        }
        assert!(changed);
        let result=mir.verify();
        assert!(result.is_err() || result.is_ok_and(|diagnostics|!diagnostics.is_empty()));
    }
    #[test]
    fn moved_owned_actuals_cannot_inherit_staged_ref_write_certificate(){
        let src="let mut a:Blob=Blob{n:1,other:2};let mut b:i64=3;let r=owned_then_ref(a,f(&mut b));*r=4;";
        assert!(rejected(src,|calls|{
            let summary=calls.get_mut("owned_then_ref").unwrap();
            let effect=VerifiedParameterEffect{parameter:0,
                fields:vec![FieldKey{aggregate:TypeId(0),field:FieldId(0)}],
                kind:VerifiedEffectKind::Move};
            summary.parameter_effects.push(effect.clone());
            summary.path_cases.push(VerifiedPathCase{effects:vec![effect],
                returned:Some(0),uninitialized:vec![]});
        }));
    }
    #[test]
    fn symbolic_phi_actual_uses_exact_staged_exclusive_capability(){
        let src="let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let mut c:Blob=Blob{n:5,other:6};let p=if true{&mut a}else{&mut b};let r=write_choose_right(p,write_blob(&mut c));r.n=9;";
        let mir=ok(src);
        assert!(mir.blocks.iter().flat_map(|block|block.statements.iter()).any(|stmt|
            matches!(stmt,Statement::Call{name,effects,..} if name=="write_choose_right" &&
                effects.iter().any(|effect|effect.alternatives.len()==2))));
    }
    #[test]
    fn ordinary_pure_and_nested_effectful_calls_remain_supported(){
        let _=certified("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};let r=choose_blob_right(&mut a,write_blob(&mut b));r.n=5;");
    }
}

#[cfg(test)]
mod ordered_phi_effectful_nll_0674_tests {
    use super::*;
    use super::nested_interprocedural_nll_0671_tests::{lower,rejected};

    fn n()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn other()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn effect(parameter:usize,field:FieldKey)->VerifiedParameterEffect{
        VerifiedParameterEffect{parameter,fields:vec![field],kind:VerifiedEffectKind::Write}
    }
    fn conditional_outer(three:bool)->VerifiedCallSummary {
        let blob=ConstType::Named("Blob".into());
        let refer=ConstType::RefMut(Box::new(blob));
        let effects=if three{vec![effect(0,n()),effect(1,other())]}
            else{vec![effect(0,n()),effect(0,other())]};
        let ret=if three{2}else{1};
        VerifiedCallSummary{
            parameters:vec![refer.clone();ret+1],
            field_writes:effects.iter().map(|item|VerifiedFieldWrite{
                parameter:item.parameter,fields:item.fields.clone(),
            }).collect(),
            parameter_effects:effects.clone(),
            returned:Some(VerifiedReturnedReference{parameter:ret,
                fields:vec![],ty:refer}),
            returned_alternatives:vec![],
            path_cases:effects.iter().map(|item|VerifiedPathCase{
                effects:vec![item.clone()],returned:Some(0),uninitialized:vec![],
            }).collect(),
        }
    }
    fn setup(calls:&mut HashMap<String,VerifiedCallSummary>) {
        calls.insert("conditional_write".into(),conditional_outer(false));
        calls.insert("conditional_write_three".into(),conditional_outer(true));
    }
    fn two_phi()->&'static str{
        "let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};\
         let mut c:Blob=Blob{n:5,other:6};\
         let p=if true{&mut a}else{&mut b};\
         let r=conditional_write(p,write_blob(&mut c));r.other=9;"
    }
    fn verified(src:&str)->FunctionMir {
        let mir=lower(src,setup).expect("ordered PHI effect must have complete MIR");
        let diagnostics=mir.verify().expect("closed disjunctive alias certificate");
        assert!(diagnostics.is_empty(),"{diagnostics:?}");
        mir
    }
    fn denied(src:&str)->bool {rejected(src,setup)}

    #[test]
    fn if_phi_is_a_staged_nonreturned_effectful_argument(){
        let mir=verified(two_phi());
        let call=mir.blocks.iter().flat_map(|b|b.statements.iter()).find(|s|
            matches!(s,Statement::Call{name,..} if name=="conditional_write")).unwrap();
        let Statement::Call{events,effects,path_cases,..}=call else{unreachable!()};
        assert_eq!(effects.len(),2);
        assert_eq!(path_cases.len(),2);
        assert!(path_cases.iter().all(|case|case.effects.len()==1));
        assert!(effects.iter().all(|effect|
            effect.kind==VerifiedEffectKind::Write && effect.alternatives.len()==2));
        assert!(events.iter().any(|event|
            event.op==Access::Write && event.path.fields.is_empty()));
        assert_ne!(effects[0].alternatives[0],effects[1].alternatives[0]);
    }
    #[test]
    fn match_phi_preserves_alternative_owner_paths(){
        let _=verified("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};\
            let mut c:Blob=Blob{n:5,other:6};\
            let p=match true{true=>{&mut a},false=>{&mut b}};\
            let r=conditional_write(p,write_blob(&mut c));r.n=7;");
    }
    #[test]
    fn two_independent_phi_inputs_keep_correlated_conditional_effect_cases(){
        let mir=verified("let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};\
            let mut c:Blob=Blob{n:5,other:6};let mut d:Blob=Blob{n:7,other:8};\
            let mut e:Blob=Blob{n:9,other:10};\
            let p=if true{&mut a}else{&mut b};\
            let q=match true{true=>{&mut c},false=>{&mut d}};\
            let r=conditional_write_three(p,q,write_blob(&mut e));r.n=12;");
        let call=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|
            if let Statement::Call{name,effects,path_cases,..}=s {
                (name=="conditional_write_three").then_some((effects,path_cases))
            }else{None}).unwrap();
        assert_eq!(call.0.len(),2);
        assert_eq!(call.1.len(),2);
        assert!(call.0.iter().all(|effect|effect.alternatives.len()==2));
        assert!(call.1.iter().all(|case|case.effects.len()==1));
    }
    #[test]
    fn all_phi_effect_paths_reuse_typed_movepath_keys(){
        let mir=verified(two_phi());
        let effects=mir.blocks.iter().flat_map(|b|b.statements.iter()).find_map(|s|
            if let Statement::Call{name,effects,..}=s {
                (name=="conditional_write").then_some(effects)
            }else{None}).unwrap();
        let mut forest=cfg_borrow::Forest::default();
        for effect in effects {
            for path in &effect.alternatives {
                assert_eq!(path.fields.len(),1);
                let id=forest.intern(path).unwrap();
                let parent=forest.intern(&Path::root(path.owner)).unwrap();
                assert_eq!(forest.nodes()[id.0 as usize].parent,Some(parent));
                assert_eq!(forest.intern(path).unwrap(),id);
            }
        }
    }
    #[test]
    fn ordered_call_stages_phi_capability_before_inner_write(){
        let mir=verified(two_phi());
        let mut seen_stage=false;
        let mut seen_nested=false;
        let mut seen_outer=false;
        for block in &mir.blocks{for statement in &block.statements{
            match statement {
                Statement::Access(Event{op:Access::Write,loan:Some(_),path,..})
                    if path.fields.is_empty()=>{seen_stage=true;assert!(!seen_nested);},
                Statement::Call{name,..} if name=="write_blob"=>{
                    assert!(seen_stage);seen_nested=true;
                }
                Statement::Call{name,..} if name=="conditional_write"=>{
                    assert!(seen_nested);seen_outer=true;
                }
                _=>(),
            }
        }}
        assert!(seen_stage && seen_nested && seen_outer);
    }
    #[test]
    fn later_nested_call_cannot_borrow_a_possible_phi_owner(){
        assert!(denied("let mut a:Blob=Blob{n:1,other:2};\
            let mut b:Blob=Blob{n:3,other:4};\
            let p=if true{&mut a}else{&mut b};\
            let r=conditional_write(p,write_blob(&mut a));r.n=9;"));
    }
    #[test]
    fn parent_cannot_change_before_later_ordered_phi_use(){
        assert!(denied("let mut a:Blob=Blob{n:1,other:2};\
            let mut b:Blob=Blob{n:3,other:4};let mut c:Blob=Blob{n:5,other:6};\
            let p=if true{&mut a}else{&mut b};a.n=5;\
            let r=conditional_write(p,write_blob(&mut c));r.n=9;"));
    }
    #[test]
    fn missing_or_partial_correlated_witnesses_fail_closed(){
        assert!(rejected(two_phi(),|calls|{
            setup(calls);calls.get_mut("conditional_write").unwrap().path_cases.pop();
        }));
        assert!(rejected(two_phi(),|calls|{
            setup(calls);calls.get_mut("conditional_write").unwrap().path_cases.clear();
        }));
    }
    #[test]
    fn wrong_type_qualified_field_projection_is_not_inferred(){
        assert!(rejected(two_phi(),|calls|{
            setup(calls);calls.get_mut("conditional_write").unwrap()
                .field_writes[1].fields[0].aggregate=TypeId(999);
        }));
    }
    #[test]
    fn explicitly_certified_returned_phi_keeps_exact_staged_parent_loans(){
        let mir=lower(two_phi(),|calls|{
            setup(calls);
            calls.get_mut("conditional_write").unwrap()
                .returned.as_mut().unwrap().parameter=0;
        }).expect("a certified PHI return must lower completely");
        let diagnostics=mir.verify().expect("returned PHI proof must be valid");
        assert!(diagnostics.is_empty(),"{diagnostics:?}");
        let phis=mir.blocks.iter().flat_map(|block|block.statements.iter())
            .filter_map(|statement|match statement{
                Statement::ValuePhi{alternatives,..}=>Some(alternatives),
                _=>None,
            }).collect::<Vec<_>>();
        assert!(phis.len()>=2,"input PHI and returned PHI must both exist");
        let input=phis[0];
        let returned=phis[phis.len()-1];
        assert_eq!(input.len(),2);
        assert_eq!(returned.len(),4);
        for child in returned {
            assert!(child.exclusive);
            assert!(input.iter().any(|parent|
                child.parent==Some(parent.loan) && child.path==parent.path),
                "returned child must be linked to its actual staged PHI parent");
            assert_eq!(mir.loans.get(&child.loan),Some(&child.path));
        }
    }
    #[test]
    fn returned_phi_origin_requires_valid_correlated_case_index(){
        assert!(rejected(two_phi(),|calls|{
            setup(calls);
            let summary=calls.get_mut("conditional_write").unwrap();
            summary.returned.as_mut().unwrap().parameter=0;
            summary.path_cases[0].returned=Some(1);
        }),"a single certified returned origin has index zero only");
        assert!(rejected(two_phi(),|calls|{
            setup(calls);
            let summary=calls.get_mut("conditional_write").unwrap();
            summary.returned.as_mut().unwrap().parameter=0;
            summary.path_cases[0].returned=None;
        }),"a missing return-origin witness must fail closed");
    }
    #[test]
    fn returned_phi_origin_requires_exact_return_type(){
        assert!(rejected(two_phi(),|calls|{
            setup(calls);
            let summary=calls.get_mut("conditional_write").unwrap();
            let returned=summary.returned.as_mut().unwrap();
            returned.parameter=0;
            returned.ty=ConstType::RefMut(Box::new(ConstType::I64));
        }),"callee return type cannot be inferred from the PHI actual");
    }
    #[test]
    fn forged_disjunctive_effect_candidate_is_rejected_by_independent_auditor(){
        let mut mir=verified(two_phi());
        for block in &mut mir.blocks {for statement in &mut block.statements {
            if let Statement::Call{name,effects,..}=statement {
                if name=="conditional_write" {
                    effects[0].alternatives[0].owner=SymbolId(u32::MAX);
                }
            }
        }}
        assert!(mir.verify().is_err());
    }
    #[test]
    fn call_cannot_claim_phis_write_without_boundary_capability(){
        let mut mir=verified(two_phi());
        for block in &mut mir.blocks {for statement in &mut block.statements {
            if let Statement::Call{name,events,..}=statement {
                if name=="conditional_write" {
                    events.retain(|event|!(event.op==Access::Write &&
                        event.path.fields.is_empty()));
                }
            }
        }}
        assert!(mir.verify().is_err());
    }
}


#[cfg(test)]
mod ordered_effectful_phi_return_0675_tests {
    use super::*;
    use super::nested_interprocedural_nll_0671_tests::{lower,rejected};

    fn n()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(0)}}
    fn other()->FieldKey{FieldKey{aggregate:TypeId(0),field:FieldId(1)}}
    fn effect(parameter:usize,field:FieldKey)->VerifiedParameterEffect{
        VerifiedParameterEffect{parameter,fields:vec![field],kind:VerifiedEffectKind::Write}
    }
    fn borrow()->ConstType{
        ConstType::RefMut(Box::new(ConstType::Named("Blob".into())))
    }
    fn two_origin()->VerifiedCallSummary{
        let ty=borrow();
        let w0=effect(0,n());let w1=effect(1,other());
        VerifiedCallSummary{
            parameters:vec![ty.clone();3],
            field_writes:vec![
                VerifiedFieldWrite{parameter:0,fields:vec![n()]},
                VerifiedFieldWrite{parameter:1,fields:vec![other()]},
            ],
            parameter_effects:vec![w0.clone(),w1.clone()],
            returned:None,
            returned_alternatives:vec![
                VerifiedReturnedReference{parameter:0,fields:vec![],ty:ty.clone()},
                VerifiedReturnedReference{parameter:1,fields:vec![],ty},
            ],
            path_cases:vec![
                VerifiedPathCase{effects:vec![w0],returned:Some(0),uninitialized:vec![]},
                VerifiedPathCase{effects:vec![w1],returned:Some(1),uninitialized:vec![]},
            ],
        }
    }
    fn single_origin()->VerifiedCallSummary{
        let ty=borrow();
        let w0=effect(0,other());let w1=effect(1,n());
        VerifiedCallSummary{
            parameters:vec![ty.clone();2],
            field_writes:vec![
                VerifiedFieldWrite{parameter:0,fields:vec![other()]},
                VerifiedFieldWrite{parameter:1,fields:vec![n()]},
            ],
            parameter_effects:vec![w0.clone(),w1.clone()],
            returned:Some(VerifiedReturnedReference{
                parameter:0,fields:vec![],ty,
            }),
            returned_alternatives:vec![],
            path_cases:vec![
                VerifiedPathCase{effects:vec![w0],returned:Some(0),uninitialized:vec![]},
                VerifiedPathCase{effects:vec![w1],returned:Some(0),uninitialized:vec![]},
            ],
        }
    }
    fn projected_origin()->VerifiedCallSummary{
        let mut result=single_origin();
        result.returned.as_mut().unwrap().fields=vec![n()];
        result.returned.as_mut().unwrap().ty=ConstType::RefMut(Box::new(ConstType::I64));
        result
    }
    pub(super) fn setup(calls:&mut HashMap<String,VerifiedCallSummary>){
        calls.insert("choose_effectful".into(),two_origin());
        calls.insert("forward_effectful".into(),single_origin());
        calls.insert("project_effectful".into(),projected_origin());
    }
    pub(super) const PREFIX:&str="let mut a:Blob=Blob{n:1,other:2};\
        let mut b:Blob=Blob{n:3,other:4};\
        let mut c:Blob=Blob{n:5,other:6};\
        let mut d:Blob=Blob{n:7,other:8};\
        let mut e:Blob=Blob{n:9,other:10};\
        let p=if true{&mut a}else{&mut b};\
        let q=match true{true=>{&mut c},false=>{&mut d}};";
    fn two()->String{
        format!("{PREFIX}let result=choose_effectful(p,q,write_blob(&mut e));result.n=11;")
    }
    fn single()->String{
        format!("{PREFIX}let result=forward_effectful(p,write_blob(&mut e));result.n=11;")
    }
    fn verified(src:&str)->FunctionMir{
        let mir=lower(src,setup).expect("ordered returned PHI needs complete MIR");
        let diagnostics=mir.verify().expect("typed returned PHI proof must be valid");
        assert!(diagnostics.is_empty(),"{diagnostics:?}");
        mir
    }
    fn denied(src:&str)->bool {rejected(src,setup)}
    fn output_options(mir:&FunctionMir)->Vec<RefOption>{
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|{
            if let Statement::ValuePhi{alternatives,..}=s {
                Some(alternatives.clone())
            }else{None}
        }).last().expect("returned PHI options")
    }
    #[test]
    fn independent_if_and_match_returns_keep_exact_four_owner_paths(){
        let mir=verified(&two());
        let paths=output_options(&mir);
        assert_eq!(paths.len(),4);
        let owners=paths.iter().map(|o|o.path.owner).collect::<HashSet<_>>();
        assert_eq!(owners.len(),4);
        assert!(paths.iter().all(|o|o.exclusive && o.parent.is_some()));
    }
    #[test]
    fn every_return_origin_retains_only_its_own_conditional_write(){
        let mir=verified(&two());
        let mut count=0;
        for block in &mir.blocks {
            let call=block.statements.iter().find_map(|stmt|{
                if let Statement::Call{name,effects,path_cases,..}=stmt {
                    (name=="choose_effectful").then_some((effects,path_cases))
                }else{None}
            });
            if let Some((effects,path_cases))=call {
                count+=1;
                assert_eq!(effects.len(),1);
                assert_eq!(path_cases.len(),1);
                assert_eq!(path_cases[0].effects.as_slice(),effects.as_slice());
                let returned=block.statements.iter().find_map(|stmt|{
                    if let Statement::LatePhiReborrow{children,..}=stmt {
                        Some(children)
                    }else{None}
                }).expect("returned source must be rebound after the call");
                assert_eq!(effects[0].alternatives.len(),2);
                assert_eq!(returned.len(),2);
                for (actual,child) in effects[0].alternatives.iter().zip(returned){
                    assert_eq!(actual.owner,child.path.owner);
                    assert!(actual.fields.len()==1);
                }
            }
        }
        assert_eq!(count,2,"each correlated return/effect case is a separate CFG arm");
    }
    #[test]
    fn single_returned_phi_can_have_two_effect_cases(){
        let mir=verified(&single());
        assert_eq!(output_options(&mir).len(),4);
        let calls=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|s|
            matches!(s,Statement::Call{name,..} if name=="forward_effectful")).count();
        assert_eq!(calls,2);
    }
    #[test]
    fn typed_projected_phi_return_retains_parent_chain(){
        let src=format!("{PREFIX}let result=project_effectful(p,write_blob(&mut e));*result=11;");
        let mir=verified(&src);
        for child in output_options(&mir){
            assert_eq!(child.path.fields,vec![n()]);
            assert_eq!(mir.loans.get(&child.loan),Some(&child.path));
            let parent=mir.loans.get(&child.parent.unwrap()).unwrap();
            assert!(parent.ancestor_of(&child.path));
        }
    }
    #[test]
    fn returned_phi_source_can_be_an_exhaustive_match(){
        let source=two().replace(
            "let p=if true{&mut a}else{&mut b};",
            "let p=match true{true=>{&mut a},false=>{&mut b}};");
        let _=verified(&source);
    }
    #[test]
    fn ordinary_non_phi_ordered_calls_remain_supported(){
        let src="let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};            let r=choose_blob_right(&mut a,write_blob(&mut b));r.n=9;";
        let mir=lower(src,setup).expect("older ordinary ordered call must remain supported");
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn older_effectful_non_phi_return_path_remains_supported(){
        let src="let mut a:Blob=Blob{n:1,other:2};let mut b:Blob=Blob{n:3,other:4};            let r=forward_effectful(&mut a,write_blob(&mut b));r.n=9;";
        let mir=lower(src,setup).expect("older effectful return must remain supported");
        assert!(mir.verify().unwrap().is_empty());
    }
    #[test]
    fn selected_effects_happen_before_late_reborrow(){
        let mir=verified(&two());
        for block in &mir.blocks{
            let call=block.statements.iter().position(|stmt|
                matches!(stmt,Statement::Call{name,..} if name=="choose_effectful"));
            if let Some(call_index)=call{
                let reborrow=block.statements.iter().position(|stmt|
                    matches!(stmt,Statement::LatePhiReborrow{..})).unwrap();
                assert!(call_index<reborrow);
            }
        }
    }
    #[test]
    fn nested_argument_must_not_borrow_a_possible_returned_owner(){
        let src=format!("{PREFIX}let result=choose_effectful(p,q,write_blob(&mut a));result.n=11;");
        assert!(denied(&src));
    }
    #[test]
    fn same_mutable_phi_cannot_be_passed_to_two_formal_arguments(){
        let src=format!("{PREFIX}let result=choose_effectful(p,p,write_blob(&mut e));result.n=11;");
        assert!(denied(&src));
    }
    #[test]
    fn returned_source_cannot_be_modified_while_result_is_live(){
        let src=format!("{PREFIX}let result=choose_effectful(p,q,write_blob(&mut e));a.n=12;result.n=11;");
        assert!(denied(&src));
    }
    #[test]
    fn missing_correlated_effect_case_fails_closed(){
        assert!(rejected(&two(),|calls|{
            setup(calls);calls.get_mut("choose_effectful").unwrap().path_cases.pop();
        }));
    }
    #[test]
    fn invented_return_origin_index_fails_closed(){
        assert!(rejected(&two(),|calls|{
            setup(calls);calls.get_mut("choose_effectful").unwrap()
                .path_cases[1].returned=Some(99);
        }));
    }
    #[test]
    fn dropped_case_effect_is_not_authorized_by_may_summary(){
        assert!(rejected(&two(),|calls|{
            setup(calls);calls.get_mut("choose_effectful").unwrap()
                .path_cases[0].effects.clear();
        }));
    }
    #[test]
    fn reference_loan_cannot_be_moved_through_effect_certificate(){
        assert!(rejected(&two(),|calls|{
            setup(calls);calls.get_mut("choose_effectful").unwrap()
                .parameter_effects[0].kind=VerifiedEffectKind::Move;
        }));
    }
    #[test]
    fn return_origin_type_mismatch_is_not_certified(){
        assert!(rejected(&two(),|calls|{
            setup(calls);calls.get_mut("choose_effectful").unwrap()
                .returned_alternatives[1].ty=ConstType::RefMut(Box::new(ConstType::I64));
        }));
    }
    #[test]
    fn forged_field_key_in_correlated_write_is_rejected(){
        assert!(rejected(&two(),|calls|{
            setup(calls);calls.get_mut("choose_effectful").unwrap()
                .path_cases[0].effects[0].fields[0].aggregate=TypeId(999);
        }));
    }
    #[test]
    fn orphan_child_loan_does_not_pass_independent_verifier(){
        let mut mir=verified(&two());
        let mut damaged=false;
        for block in &mut mir.blocks {for stmt in &mut block.statements {
            if let Statement::LatePhiReborrow{children,..}=stmt {
                children[0].parent=Some(SymbolId(u32::MAX));
                damaged=true;break;
            }
        }if damaged{break;}}
        assert!(damaged);
        assert!(mir.verify().is_err());
    }
    #[test]
    fn swapped_effect_owner_cannot_forge_a_valid_alias_witness(){
        let mut mir=verified(&two());
        let mut changed=false;
        for block in &mut mir.blocks {for stmt in &mut block.statements {
            if let Statement::Call{name,effects,..}=stmt {
                if name=="choose_effectful"{
                    effects[0].alternatives[0].owner=SymbolId(u32::MAX);
                    changed=true;break;
                }
            }
        }if changed{break;}}
        assert!(changed);
        assert!(mir.verify().is_err());
    }
}


#[cfg(test)]
mod transitive_interprocedural_phi_returns_0676_tests {
    use super::*;
    use super::ordered_effectful_phi_return_0675_tests::{setup,PREFIX};
    use super::nested_interprocedural_nll_0671_tests::lower;
    fn source(suffix:&str)->String {
        format!("{PREFIX}let first=forward_effectful(p,write_blob(&mut e));\
            let second=forward_effectful(first,write_blob(&mut e));{suffix}")
    }
    fn checked(src:&str)->FunctionMir {
        let mir=lower(src,setup).expect("nested PHI return must lower to complete typed MIR");
        let diagnostics=mir.verify().expect("verified multi-level return should be well formed");
        assert!(diagnostics.is_empty(),"{diagnostics:?}");
        mir
    }
    fn output_groups(mir:&FunctionMir)->Vec<Vec<RefOption>> {
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|s|{
            if let Statement::ValuePhi{alternatives,..}=s {
                Some(alternatives.clone())
            }else{None}
        }).collect()
    }
    #[test]
    fn two_effectful_returns_preserve_all_parent_paths() {
        let mir=checked(&source("second.n=11;"));
        let groups=output_groups(&mir);
        let first=groups.iter().find(|options|options.len()==4).unwrap();
        let second=groups.iter().find(|options|options.len()==8).unwrap();
        let parents=first.iter().map(|o|o.loan).collect::<HashSet<_>>();
        assert!(second.iter().all(|child|
            child.exclusive && child.parent.is_some_and(|id|parents.contains(&id)) &&
            mir.loans.get(&child.loan)==Some(&child.path)));
        let owners=second.iter().map(|option|option.path.owner)
            .collect::<HashSet<_>>();
        assert_eq!(owners.len(),2);
    }
    #[test]
    fn forwarded_child_still_suspends_its_original_owner() {
        let src=source("a.n=12;second.n=11;");
        let denied=match lower(&src,setup) {
            None=>true,
            Some(mir)=>match mir.verify(){Err(_)=>true,Ok(issues)=>!issues.is_empty()},
        };
        assert!(denied);
    }
    #[test]
    fn projected_second_return_keeps_qualified_original_move_paths() {
        let src=format!("{PREFIX}let first=forward_effectful(p,write_blob(&mut e));\
            let scalar=project_effectful(first,write_blob(&mut e));*scalar=11;");
        let mir=checked(&src);
        let groups=output_groups(&mir);
        let last=groups.last().unwrap();
        let key=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        assert!(last.iter().all(|o|o.path.fields==vec![key] && o.parent.is_some()));
    }
    #[test]
    fn forged_grandchild_parent_is_not_accepted_by_mir_verifier() {
        let mut mir=checked(&source("second.n=11;"));
        let mut altered=false;
        for block in &mut mir.blocks {
            for statement in &mut block.statements {
                if let Statement::LatePhiReborrow{children,..}=statement {
                    if children.len()==4 {
                        children[0].parent=children[1].parent;
                        altered=true;
                        break;
                    }
                }
            }
            if altered{break;}
        }
        assert!(altered);
        assert!(mir.verify().is_err());
    }
}

#[cfg(test)]
mod nested_immediate_phi_forward_0677_tests {
    use super::*;
    use super::nested_interprocedural_nll_0671_tests::{lower,rejected};

    fn source(inner:&str)->String {
        format!("let mut a:i64=1;let mut b:i64=2;\
            let p=if true{{&mut a}}else{{&mut b}};{inner}")
    }
    fn checked(inner:&str)->FunctionMir {
        let src=source(inner);
        let mir=lower(&src,|_|{}).expect("nested PHI chain must be representable");
        let conflicts=mir.verify().expect("complete nested PHI proof");
        assert!(conflicts.is_empty(),"{conflicts:?}");
        mir
    }
    fn final_phi(mir:&FunctionMir)->&Vec<RefOption> {
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|
            if let Statement::ValuePhi{alternatives,..}=stmt {
                Some(alternatives)
            }else{None}).last().expect("forwarded PHI")
    }
    #[test]
    fn two_level_chain_retains_exact_parent_and_two_owners() {
        let mir=checked("let r=f(f(p));*r=3;");
        let result=final_phi(&mir);
        assert_eq!(result.len(),2);
        assert_ne!(result[0].path.owner,result[1].path.owner);
        assert!(result.iter().all(|r|r.exclusive && r.parent.is_some() &&
            mir.loans.get(&r.loan)==Some(&r.path)));
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|stmt|
            matches!(stmt,Statement::Call{name,..} if name=="f")).count(),4);
    }
    #[test]
    fn three_level_chain_keeps_each_borrow_on_its_selected_edge() {
        let mir=checked("let r=f(f(f(p)));*r=4;");
        assert_eq!(final_phi(&mir).len(),2);
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter()).filter(|stmt|
            matches!(stmt,Statement::Call{name,..} if name=="f")).count(),6);
    }
    #[test]
    fn each_nested_parent_chain_reaches_only_its_own_phi_predecessor() {
        let mir=checked("let r=f(f(f(p)));*r=4;");
        let groups=mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|
            if let Statement::ValuePhi{alternatives,..}=stmt {
                Some(alternatives)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(groups.len(),2);
        for (source,result) in groups[0].iter().zip(groups[1].iter()) {
            let mut parent=result.parent;
            let mut seen=HashSet::new();
            let mut reached=false;
            while let Some(loan)=parent {
                assert!(seen.insert(loan),"cycle in returned loan ancestors");
                if loan==source.loan {reached=true;break;}
                let links=mir.blocks.iter().flat_map(|block|block.statements.iter())
                    .flat_map(|stmt|stmt.events()).filter(|event|
                        event.op==Access::BorrowMut && event.loan==Some(loan))
                    .collect::<Vec<_>>();
                assert_eq!(links.len(),1,"every intermediate loan needs one origin");
                assert_eq!(links[0].path,source.path);
                parent=links[0].parent;
            }
            assert!(reached,"the selected PHI owner must be the ancestor");
        }
    }
    #[test]
    fn independent_owner_is_writable_during_nested_phi_lifetime() {
        let src="let mut a:i64=1;let mut b:i64=2;let mut c:i64=3;            let p=if true{&mut a}else{&mut b};            let r=f(f(p));c=8;*r=4;";
        let mir=lower(src,|_|{}).expect("unrelated owner must lower");
        assert!(mir.verify().expect("valid independent ownership").is_empty());
    }
    #[test]
    fn nested_chain_may_start_from_match_phi() {
        let src="let mut a:i64=1;let mut b:i64=2;\
            let p=match true{true=>{&mut a},false=>{&mut b}};\
            let r=f(f(p));*r=5;";
        let mir=lower(src,|_|{}).expect("match PHI must lower");
        assert!(mir.verify().expect("complete match proof").is_empty());
        assert_eq!(final_phi(&mir).len(),2);
    }
    #[test]
    fn reusing_the_returned_phi_in_a_later_call_remains_valid() {
        let mir=checked("let r=f(f(p));let s=f(r);*s=6;");
        assert_eq!(final_phi(&mir).len(),2);
    }
    #[test]
    fn original_possible_owner_cannot_change_before_last_use() {
        assert!(rejected(&source("let r=f(f(p));a=7;*r=5;"),|_|{}));
    }
    #[test]
    fn unknown_nested_summary_cannot_be_assumed_pure() {
        assert!(rejected(&source("let r=f(f(p));*r=5;"),|calls|{
            calls.remove("f");
        }));
    }
    #[test]
    fn a_forged_return_parameter_does_not_get_a_phi_parent() {
        assert!(rejected(&source("let r=f(f(p));*r=5;"),|calls|{
            calls.get_mut("f").unwrap().returned.as_mut().unwrap().parameter=1;
        }));
    }
    #[test]
    fn a_nested_return_with_a_field_projection_is_not_guessed() {
        assert!(rejected(&source("let r=f(f(p));*r=5;"),|calls|{
            calls.get_mut("f").unwrap().returned.as_mut().unwrap().fields.push(
                FieldKey{aggregate:TypeId(0),field:FieldId(0)});
        }));
    }
    #[test]
    fn an_unproved_write_cannot_be_hidden_in_a_pure_chain() {
        assert!(rejected(&source("let r=f(f(p));*r=5;"),|calls|{
            calls.get_mut("f").unwrap().parameter_effects.push(
                VerifiedParameterEffect{parameter:0,fields:vec![],
                    kind:VerifiedEffectKind::Write});
        }));
    }
    #[test]
    fn tampering_with_the_nested_parent_is_rejected_by_independent_verifier() {
        let mut mir=checked("let r=f(f(p));*r=5;");
        let mut altered=false;
        for block in &mut mir.blocks {
            for stmt in &mut block.statements {
                if let Statement::Access(Event{op:Access::BorrowMut,
                    parent:Some(parent),..})=stmt {
                    *parent=SymbolId(u32::MAX);
                    altered=true;
                    break;
                }
            }
            if altered {break;}
        }
        assert!(altered);
        assert!(mir.verify().map_or(true,|conflicts|!conflicts.is_empty()));
    }
    #[test]
    fn recursion_depth_bound_is_fail_closed() {
        let mut expression="p".to_owned();
        for _ in 0..13 {expression=format!("f({expression})");}
        let src=source(&format!("let r={expression};*r=5;"));
        assert!(rejected(&src,|_|{}));
    }
}

#[cfg(test)]
mod nested_conditional_write_phi_nll_0678_tests {
    use super::*;
    use super::nested_interprocedural_nll_0671_tests::lower;

    fn key(index:u32)->FieldKey {
        FieldKey{aggregate:TypeId(0),field:FieldId(index)}
    }
    fn write(index:u32)->VerifiedParameterEffect {
        VerifiedParameterEffect{parameter:0,fields:vec![key(index)],
            kind:VerifiedEffectKind::Write}
    }
    fn conditional()->VerifiedCallSummary {
        let ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        let a=write(0);
        let b=write(1);
        VerifiedCallSummary {
            parameters:vec![ty.clone()],
            field_writes:vec![
                VerifiedFieldWrite{parameter:0,fields:vec![key(0)]},
                VerifiedFieldWrite{parameter:0,fields:vec![key(1)]},
            ],
            parameter_effects:vec![a.clone(),b.clone()],
            returned:Some(VerifiedReturnedReference{
                parameter:0,fields:vec![],ty,
            }),
            returned_alternatives:vec![],
            path_cases:vec![
                VerifiedPathCase{effects:vec![a],returned:Some(0),uninitialized:vec![]},
                VerifiedPathCase{effects:vec![b],returned:Some(0),uninitialized:vec![]},
            ],
        }
    }
    fn setup(calls:&mut HashMap<String,VerifiedCallSummary>) {
        calls.insert("ew".into(),conditional());
        calls.insert("ew2".into(),conditional());
    }
    fn lower_with(source:&str,
        mutate:impl FnOnce(&mut HashMap<String,VerifiedCallSummary>))->Option<FunctionMir> {
        lower(source,|calls|{setup(calls);mutate(calls);})
    }
    fn checked(source:&str)->FunctionMir {
        let mir=lower_with(source,|_|{}).expect("fully witnessed nested writes");
        let issues=mir.verify().expect("complete CFG effect proof");
        assert!(issues.is_empty(),"{issues:?}");
        mir
    }
    fn rejected(source:&str,
        mutate:impl FnOnce(&mut HashMap<String,VerifiedCallSummary>))->bool {
        match lower_with(source,mutate) {
            None=>true,
            Some(mir)=>mir.verify().map_or(true,|issues|!issues.is_empty()),
        }
    }
    const SOURCE:&str="let mut a:Blob=Blob{n:1,other:2};\
        let mut b:Blob=Blob{n:3,other:4};\
        let p=if true{&mut a}else{&mut b};";

    #[test]
    fn two_nested_conditional_writers_follow_exact_phi_edges() {
        let mir=checked(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"));
        let outputs=mir.blocks.iter().flat_map(|block|block.statements.iter())
            .filter_map(|s|match s{Statement::ValuePhi{alternatives,..}=>Some(alternatives),_=>None})
            .collect::<Vec<_>>();
        assert_eq!(outputs.len(),2);
        assert_eq!(outputs[1].len(),2);
        assert_ne!(outputs[1][0].path.owner,outputs[1][1].path.owner);
        assert_eq!(mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter(|s|matches!(s,Statement::Call{name,..} if name=="ew" || name=="ew2"))
            .count(),4);
        for option in outputs[1] {
            assert!(option.exclusive && option.parent.is_some());
            assert_eq!(mir.loans.get(&option.loan),Some(&option.path));
        }
    }
    #[test]
    fn all_conditional_write_cases_remain_distinct_at_each_call() {
        let mir=checked(&format!("{SOURCE}let r=ew(ew2(p));r.other=9;"));
        let calls=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|stmt|match stmt{
                Statement::Call{name,path_cases,..} if name=="ew" || name=="ew2" =>
                    Some(path_cases),_=>None,
            }).collect::<Vec<_>>();
        assert_eq!(calls.len(),4);
        for cases in calls {
            assert_eq!(cases.len(),2,"no conditional Write may be erased");
            let fields=cases.iter().map(|case|{
                assert_eq!(case.returned,Some(0));
                assert_eq!(case.effects.len(),1);
                let effect=&case.effects[0];
                assert_eq!(effect.kind,VerifiedEffectKind::Write);
                assert!(effect.alternatives.is_empty());
                assert_eq!(effect.path.fields.len(),1);
                effect.path.fields[0]
            }).collect::<HashSet<_>>();
            assert_eq!(fields,HashSet::from([key(0),key(1)]));
        }
    }
    #[test]
    fn three_level_mixed_pure_and_effectful_returns_are_live() {
        let mir=checked(&format!("{SOURCE}let r=ew(blob(ew2(p)));r.n=7;"));
        let names=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|match s{Statement::Call{name,..}=>Some(name.as_str()),_=>None})
            .collect::<Vec<_>>();
        assert_eq!(names.len(),6);
        assert_eq!(names.iter().filter(|n|**n=="blob").count(),2);
    }
    #[test]
    fn exhaustive_match_phi_has_same_effectful_provenance() {
        let src="let mut a:Blob=Blob{n:1,other:2};\
            let mut b:Blob=Blob{n:3,other:4};\
            let p=match true{true=>{&mut a},false=>{&mut b}};\
            let r=ew(ew2(p));r.n=8;";
        checked(src);
    }
    #[test]
    fn unchanged_field_paths_reuse_typed_move_path_ids() {
        let mir=checked(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"));
        let mut forest=cfg_borrow::Forest::default();
        for path in mir.loans.values(){
            let parent_id=forest.intern(&Path::root(path.owner)).unwrap();
            let leaf_id=forest.intern(path).unwrap();
            if path.fields.is_empty(){assert_eq!(leaf_id,parent_id);}
            assert_eq!(forest.intern(path).unwrap(),leaf_id);
        }
    }
    #[test]
    fn independent_owner_can_change_with_both_loans_live() {
        let src="let mut a:Blob=Blob{n:1,other:2};\
            let mut b:Blob=Blob{n:3,other:4};\
            let mut c:i64=1;\
            let p=if true{&mut a}else{&mut b};\
            let r=ew(ew2(p));c=5;r.other=9;";
        checked(src);
    }
    #[test]
    fn an_original_possible_owner_cannot_change_before_result_use() {
        assert!(rejected(&format!("{SOURCE}let r=ew(ew2(p));a.n=9;r.other=4;"),|_|{}));
        assert!(rejected(&format!("{SOURCE}let r=ew(ew2(p));b.n=9;r.other=4;"),|_|{}));
    }
    #[test]
    fn each_possible_write_requires_a_complete_case_witness() {
        assert!(rejected(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"),|calls|{
            calls.get_mut("ew2").unwrap().path_cases[0].effects.clear();
        }));
    }
    #[test]
    fn may_effect_cannot_be_promoted_to_a_move_or_drop() {
        for kind in [VerifiedEffectKind::Move,VerifiedEffectKind::Drop] {
            assert!(rejected(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"),|calls|{
                calls.get_mut("ew").unwrap().parameter_effects[0].kind=kind;
            }));
        }
    }
    #[test]
    fn invalid_return_origin_cannot_steal_other_argument() {
        assert!(rejected(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"),|calls|{
            calls.get_mut("ew2").unwrap().returned.as_mut().unwrap().parameter=1;
        }));
    }
    #[test]
    fn wrong_returned_case_index_is_rejected() {
        assert!(rejected(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"),|calls|{
            calls.get_mut("ew2").unwrap().path_cases[1].returned=Some(1);
        }));
    }
    #[test]
    fn malformed_field_projection_is_rejected() {
        assert!(rejected(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"),|calls|{
            calls.get_mut("ew").unwrap().parameter_effects[0].fields[0].aggregate=TypeId(999);
        }));
    }
    #[test]
    fn forged_middle_loan_parent_is_rejected_by_independent_verifier() {
        let mut mir=checked(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"));
        let mut damaged=false;
        for block in &mut mir.blocks {
            for stmt in &mut block.statements {
                if let Statement::Access(Event{op:Access::BorrowMut,parent:Some(parent),..})=stmt {
                    *parent=SymbolId(u32::MAX);
                    damaged=true;break;
                }
            }
            if damaged{break;}
        }
        assert!(damaged);
        assert!(mir.verify().is_err());
    }
    #[test]
    fn forged_parent_in_ordered_call_event_fails_structural_verification() {
        let mut mir=checked(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"));
        let mut damaged=false;
        for block in &mut mir.blocks {
            for stmt in &mut block.statements {
                if let Statement::Call{events,..}=stmt {
                    if let Some(event)=events.iter_mut().find(|event|
                        event.op==Access::BorrowMut && event.parent.is_some()) {
                        event.parent=Some(SymbolId(u32::MAX));
                        damaged=true;
                        break;
                    }
                }
            }
            if damaged{break;}
        }
        assert!(damaged,"the test must tamper with an actual call reborrow");
        assert!(mir.verify().is_err(),"unknown parent in Call must fail closed");
    }
    #[test]
    fn missing_conditional_cases_is_not_a_pure_call_certificate() {
        assert!(rejected(&format!("{SOURCE}let r=ew(ew2(p));r.n=7;"),|calls|{
            calls.get_mut("ew2").unwrap().path_cases.clear();
        }));
    }
}

#[cfg(test)]
mod nested_projected_phi_nll_0679_tests {
    use super::*;
    use super::nested_interprocedural_nll_0671_tests::lower;

    const INPUT:&str="let mut a:Blob=Blob{n:1,other:2};\
        let mut b:Blob=Blob{n:3,other:4};\
        let p=if true{&mut a}else{&mut b};";

    fn key(index:u32)->FieldKey {
        FieldKey{aggregate:TypeId(0),field:FieldId(index)}
    }
    fn enable_conditional_writer(calls:&mut HashMap<String,VerifiedCallSummary>){
        let ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        let w0=VerifiedParameterEffect{parameter:0,
            fields:vec![key(0)],kind:VerifiedEffectKind::Write};
        let w1=VerifiedParameterEffect{parameter:0,
            fields:vec![key(1)],kind:VerifiedEffectKind::Write};
        calls.insert("ew".into(),VerifiedCallSummary{
            parameters:vec![ty.clone()],
            field_writes:vec![VerifiedFieldWrite{parameter:0,fields:vec![key(0)]},
                VerifiedFieldWrite{parameter:0,fields:vec![key(1)]}],
            parameter_effects:vec![w0.clone(),w1.clone()],
            returned:Some(VerifiedReturnedReference{parameter:0,fields:vec![],ty}),
            returned_alternatives:vec![],
            path_cases:vec![
                VerifiedPathCase{effects:vec![w0],returned:Some(0),uninitialized:vec![]},
                VerifiedPathCase{effects:vec![w1],returned:Some(0),uninitialized:vec![]},
            ],
        });
    }
    fn checked(body:&str)->FunctionMir {
        let mir=lower(body,enable_conditional_writer)
            .expect("fully certified projected PHI chain must lower");
        let issues=mir.verify().expect("typed MIR projection proof must verify");
        assert!(issues.is_empty(),"{issues:?}");
        mir
    }
    fn rejected(body:&str,
        change:impl FnOnce(&mut HashMap<String,VerifiedCallSummary>))->bool {
        match lower(body,|calls|{enable_conditional_writer(calls);change(calls)}) {
            None=>true,
            Some(mir)=>mir.verify().map_or(true,|issues|!issues.is_empty()),
        }
    }
    fn last_result(mir:&FunctionMir)->Vec<RefOption> {
        mir.blocks.iter().flat_map(|b|b.statements.iter()).filter_map(|stmt|{
            if let Statement::ValuePhi{alternatives,..}=stmt {
                Some(alternatives.clone())
            }else{None}
        }).last().expect("projected output PHI")
    }
    #[test]
    fn pure_two_level_projection_keeps_field_key_and_original_owners(){
        let mir=checked(&format!("{INPUT}let r=f(project(p));*r=9;"));
        let options=last_result(&mir);
        assert_eq!(options.len(),2);
        assert_ne!(options[0].path.owner,options[1].path.owner);
        for option in &options {
            assert_eq!(option.path.fields,vec![key(0)]);
            assert_eq!(mir.loans.get(&option.loan),Some(&option.path));
            assert!(option.exclusive && option.parent.is_some());
        }
    }
    #[test]
    fn projection_after_effectful_inner_call_keeps_both_write_cases(){
        let mir=checked(&format!("{INPUT}let r=f(project(ew(p)));*r=9;"));
        assert_eq!(last_result(&mir).len(),2);
        let calls=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|s|if let Statement::Call{name,path_cases,..}=s {
                (name=="ew").then_some(path_cases)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(calls.len(),2);
        for cases in calls {
            assert_eq!(cases.len(),2);
            let fields=cases.iter().map(|case|{
                assert_eq!(case.returned,Some(0));
                assert_eq!(case.effects.len(),1);
                case.effects[0].path.fields[0]
            }).collect::<HashSet<_>>();
            assert_eq!(fields,HashSet::from([key(0),key(1)]));
        }
    }
    #[test]
    fn projection_before_identity_return_is_valid(){
        let mir=checked(&format!("{INPUT}let r=project(blob(ew(p)));*r=5;"));
        assert!(last_result(&mir).iter().all(|o|o.path.fields==vec![key(0)]));
    }
    #[test]
    fn match_phi_projects_exact_same_typed_field(){
        let src="let mut a:Blob=Blob{n:1,other:2};\
            let mut b:Blob=Blob{n:3,other:4};\
            let p=match true{true=>{&mut a},false=>{&mut b}};\
            let r=project(ew(p));*r=8;";
        assert_eq!(last_result(&checked(src)).len(),2);
    }
    #[test]
    fn projection_child_does_not_freeze_an_independent_scalar_owner(){
        let src="let mut a:Blob=Blob{n:1,other:2};\
            let mut b:Blob=Blob{n:3,other:4};let mut c:i64=0;\
            let p=if true{&mut a}else{&mut b};\
            let r=f(project(ew(p)));c=5;*r=9;";
        checked(src);
    }
    #[test]
    fn root_owner_cannot_write_to_projected_field_before_last_use(){
        assert!(rejected(&format!("{INPUT}let r=f(project(ew(p)));a.n=9;*r=5;"),|_|{}));
        assert!(rejected(&format!("{INPUT}let r=f(project(ew(p)));b.n=9;*r=5;"),|_|{}));
    }
    #[test]
    fn forged_projection_type_or_field_key_is_denied(){
        let src=format!("{INPUT}let r=f(project(ew(p)));*r=5;");
        assert!(rejected(&src,|calls|{
            calls.get_mut("project").unwrap().returned.as_mut().unwrap()
                .fields[0].aggregate=TypeId(999);
        }));
        assert!(rejected(&src,|calls|{
            calls.get_mut("project").unwrap().returned.as_mut().unwrap()
                .ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        }));
    }
    #[test]
    fn missing_conditional_effect_or_bad_return_origin_is_denied(){
        let src=format!("{INPUT}let r=f(project(ew(p)));*r=5;");
        assert!(rejected(&src,|calls|{
            calls.get_mut("ew").unwrap().path_cases[0].effects.clear();
        }));
        assert!(rejected(&src,|calls|{
            calls.get_mut("project").unwrap().returned.as_mut().unwrap().parameter=1;
        }));
    }
    #[test]
    fn forged_child_parent_fails_independent_provenance_verification(){
        let mut mir=checked(&format!("{INPUT}let r=f(project(ew(p)));*r=5;"));
        let mut found=false;
        for block in &mut mir.blocks {
            for stmt in &mut block.statements {
                if let Statement::Access(Event{op:Access::BorrowMut,
                    path,parent:Some(parent),..})=stmt {
                    if path.fields==vec![key(0)] {
                        *parent=SymbolId(u32::MAX);found=true;break;
                    }
                }
            }
            if found {break;}
        }
        assert!(found,"must mutate an actual projected reborrow");
        assert!(mir.verify().map_or(true,|errors|!errors.is_empty()));
    }
    #[test]
    fn excess_projection_depth_is_not_guessed(){
        let src=format!("{INPUT}let r=f(project(ew(p)));*r=5;");
        assert!(rejected(&src,|calls|{
            let fields=&mut calls.get_mut("project").unwrap()
                .returned.as_mut().unwrap().fields;
            fields.extend(std::iter::repeat(key(0)).take(17));
        }));
    }
}

#[cfg(test)]
mod ordered_interprocedural_proof_audit_0680_tests {
    use super::*;

    fn disjunctive()->FunctionMir {
        let a=Path::root(SymbolId(101));
        let b=Path::root(SymbolId(102));
        let binding=Path::root(SymbolId(103));
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let generation=SymbolId(104);
        let first=RefOption{loan:SymbolId(105),path:a.clone(),exclusive:true,parent:None};
        let second=RefOption{loan:SymbolId(106),path:b.clone(),exclusive:true,parent:None};
        let effect=VerifiedAppliedEffect{path:binding.clone(),
            kind:VerifiedEffectKind::Write,
            alternatives:vec![a.child(field),b.child(field)]};
        let phi=Statement::ValuePhi{
            ty:ConstType::RefMut(Box::new(ConstType::Named("Blob".into()))),
            predecessors:vec![1,2],check:Event{op:Access::Read,path:binding.clone(),
                loan:None,parent:None,token:1},
            generation:Some(generation),provenance:None,
            alternatives:vec![first,second],
        };
        let call=Statement::Call{name:"effectful".into(),token:2,
            events:vec![Event{op:Access::Write,path:binding,
                loan:Some(generation),parent:None,token:2}],
            effects:vec![effect.clone()],path_cases:vec![VerifiedAppliedPathCase{
                effects:vec![effect],returned:None,uninitialized:vec![],
            }],
        };
        FunctionMir{entry:0,loans:HashMap::from([
                (SymbolId(105),a),(SymbolId(106),b),
            ]),blocks:vec![BasicBlock{
                statements:vec![phi,call],terminator:Terminator::Return,
            }]}
    }
    fn single_write()->FunctionMir {
        let owner=Path::root(SymbolId(201));
        let loan=SymbolId(202);
        let field=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
        let path=owner.child(field);
        let effect=VerifiedAppliedEffect{path:path.clone(),
            kind:VerifiedEffectKind::Write,alternatives:vec![]};
        let borrow=Statement::Access(Event{op:Access::BorrowMut,
            path:owner.clone(),loan:Some(loan),parent:None,token:1});
        let call=Statement::Call{name:"write_field".into(),token:2,
            events:vec![Event{op:Access::Write,path,
                loan:Some(loan),parent:None,token:2}],
            effects:vec![effect.clone()],path_cases:vec![VerifiedAppliedPathCase{
                effects:vec![effect],returned:None,uninitialized:vec![],
            }],
        };
        FunctionMir{entry:0,loans:HashMap::from([(loan,owner)]),
            blocks:vec![BasicBlock{statements:vec![borrow,call],
                terminator:Terminator::Return}]}
    }
    #[test]
    fn phi_defined_before_call_remains_a_valid_disjunctive_witness(){
        assert!(disjunctive().validate_interprocedural_alias_proofs().is_ok());
    }
    #[test]
    fn a_phi_defined_after_call_cannot_certify_earlier_write(){
        let mut mir=disjunctive();
        mir.blocks[0].statements.swap(0,1);
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn a_phi_on_only_one_cfg_arm_cannot_certify_a_joined_call(){
        let mut mir=disjunctive();
        let phi=mir.blocks[0].statements.remove(0);
        let call=mir.blocks[0].statements.remove(0);
        mir.blocks=vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![phi],terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![call],terminator:Terminator::Return},
        ];
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn dominating_phi_in_an_earlier_block_can_certify_a_call(){
        let mut mir=disjunctive();
        let phi=mir.blocks[0].statements.remove(0);
        let call=mir.blocks[0].statements.remove(0);
        mir.blocks=vec![
            BasicBlock{statements:vec![phi],terminator:Terminator::Goto(vec![1])},
            BasicBlock{statements:vec![call],terminator:Terminator::Return},
        ];
        assert!(mir.validate_interprocedural_alias_proofs().is_ok());
    }
    #[test]
    fn correctly_staged_mutable_loan_can_certify_a_later_call(){
        assert!(single_write().validate_interprocedural_alias_proofs().is_ok());
    }
    #[test]
    fn mutable_loan_created_after_call_cannot_retroactively_certify_write(){
        let mut mir=single_write();
        mir.blocks[0].statements.swap(0,1);
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn mutable_loan_ended_before_call_cannot_certify_write(){
        let mut mir=single_write();
        mir.blocks[0].statements.insert(1,Statement::Access(Event{
            op:Access::EndLoan,path:Path::root(SymbolId(201)),
            loan:Some(SymbolId(202)),parent:None,token:2,
        }));
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn mutable_loan_ended_inside_call_cannot_certify_later_write(){
        let mut mir=single_write();
        let Statement::Call{events,..}=&mut mir.blocks[0].statements[1] else{unreachable!()};
        events.insert(0,Event{op:Access::EndLoan,path:Path::root(SymbolId(201)),
            loan:Some(SymbolId(202)),parent:None,token:2});
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn borrow_inside_call_must_precede_the_effect_write(){
        let mut mir=single_write();
        mir.blocks[0].statements.remove(0);
        if let Statement::Call{events,..}=&mut mir.blocks[0].statements[0] {
            events.push(Event{op:Access::BorrowMut,path:Path::root(SymbolId(201)),
                loan:Some(SymbolId(202)),parent:None,token:2});
        }else{unreachable!();}
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
        if let Statement::Call{events,..}=&mut mir.blocks[0].statements[0] {
            events.swap(0,1);
        }else{unreachable!();}
        assert!(mir.validate_interprocedural_alias_proofs().is_ok());
    }
    #[test]
    fn owner_storage_death_revokes_staged_call_witness(){
        let mut mir=single_write();
        mir.blocks[0].statements.insert(1,Statement::StorageDead(Event{
            op:Access::StorageDead,path:Path::root(SymbolId(201)),
            loan:None,parent:None,token:2,
        }));
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn unrelated_owner_changes_do_not_revoke_exclusive_capability(){
        let mut mir=single_write();
        mir.blocks[0].statements.insert(1,Statement::Access(Event{
            op:Access::Write,path:Path::root(SymbolId(301)),
            loan:None,parent:None,token:2,
        }));
        assert!(mir.validate_interprocedural_alias_proofs().is_ok());
    }
    #[test]
    fn tampered_disjunctive_case_cannot_replace_a_phi_owner(){
        let mut mir=disjunctive();
        let Statement::Call{path_cases,effects,..}=&mut mir.blocks[0].statements[1]
            else{unreachable!()};
        let path=Path::root(SymbolId(999)).child(FieldKey{
            aggregate:TypeId(0),field:FieldId(0),
        });
        effects[0].alternatives[0]=path.clone();
        path_cases[0].effects[0].alternatives[0]=path;
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    fn conditional_nested_program()->Option<FunctionMir> {
        use super::nested_interprocedural_nll_0671_tests::lower;
        let src="let mut a:Blob=Blob{n:1,other:2};            let mut b:Blob=Blob{n:3,other:4};            let p=if true{&mut a}else{&mut b};            let r=f(project(ew(ew(p))));*r=5;";
        lower(src,|calls|{
            let ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
            let writes=(0..2).map(|n|VerifiedParameterEffect{
                parameter:0,fields:vec![FieldKey{
                    aggregate:TypeId(0),field:FieldId(n),
                }],kind:VerifiedEffectKind::Write,
            }).collect::<Vec<_>>();
            calls.insert("ew".into(),VerifiedCallSummary{
                parameters:vec![ty.clone()],
                field_writes:writes.iter().map(|e|VerifiedFieldWrite{
                    parameter:e.parameter,fields:e.fields.clone(),
                }).collect(),
                parameter_effects:writes.clone(),
                returned:Some(VerifiedReturnedReference{
                    parameter:0,fields:vec![],ty,
                }),returned_alternatives:vec![],
                path_cases:writes.into_iter().map(|effect|VerifiedPathCase{
                    effects:vec![effect],returned:Some(0),uninitialized:vec![],
                }).collect(),
            });
        })
    }
    #[test]
    fn two_nested_conditional_write_calls_retain_independent_case_proofs(){
        let mir=conditional_nested_program().expect("nested conditional chain");
        assert!(mir.verify().expect("valid interprocedural proof").is_empty());
        let cases=mir.blocks.iter().flat_map(|b|b.statements.iter())
            .filter_map(|stmt|if let Statement::Call{name,path_cases,..}=stmt {
                (name=="ew").then_some(path_cases)
            }else{None}).collect::<Vec<_>>();
        assert_eq!(cases.len(),4);
        assert!(cases.iter().all(|cases|cases.len()==2 &&
            cases.iter().all(|case|case.returned==Some(0) &&
                case.effects.len()==1)));
    }
    #[test]
    fn a_nested_call_cannot_claim_another_calls_field_effect(){
        let mut mir=conditional_nested_program().expect("nested conditional chain");
        let mut forged=false;
        for statement in mir.blocks.iter_mut().flat_map(|b|b.statements.iter_mut()) {
            let Statement::Call{name,effects,path_cases,..}=statement else{continue};
            if name!="ew"{continue;}
            effects[0].path.owner=SymbolId(u32::MAX);
            path_cases[0].effects[0].path.owner=SymbolId(u32::MAX);
            forged=true;break;
        }
        assert!(forged);
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn nested_effectful_phi_return_remains_proven_under_new_auditor(){
        use super::nested_interprocedural_nll_0671_tests::lower;
        let blob="let mut a:Blob=Blob{n:1,other:2};            let mut b:Blob=Blob{n:3,other:4};";
        let program=format!("{blob}let p=if true{{&mut a}}else{{&mut b}};            let r=f(project(ew(p)));*r=5;");
        let mir=lower(&program,|calls|{
            let ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
            let key=FieldKey{aggregate:TypeId(0),field:FieldId(0)};
            let write=VerifiedParameterEffect{parameter:0,fields:vec![key],
                kind:VerifiedEffectKind::Write};
            calls.insert("ew".into(),VerifiedCallSummary{
                parameters:vec![ty.clone()],field_writes:vec![VerifiedFieldWrite{
                    parameter:0,fields:vec![key],
                }],parameter_effects:vec![write.clone()],
                returned:Some(VerifiedReturnedReference{parameter:0,
                    fields:vec![],ty}),returned_alternatives:vec![],
                path_cases:vec![VerifiedPathCase{effects:vec![write],
                    returned:Some(0),uninitialized:vec![]}],
            });
        }).expect("valid nested effectful PHI chain");
        assert!(mir.verify().expect("complete MIR verifier").is_empty());
    }
}

#[cfg(test)]
mod interprocedural_reborrow_suspension_0681_tests {
    use super::*;

    fn owner()->Path {Path::root(SymbolId(501))}
    fn field(n:u32)->FieldKey {
        FieldKey{aggregate:TypeId(0),field:FieldId(n)}
    }
    fn event(op:Access,path:Path,loan:SymbolId,parent:Option<SymbolId>)->Event {
        Event{op,path,loan:Some(loan),parent,token:1}
    }
    fn access(op:Access,path:Path,loan:SymbolId,parent:Option<SymbolId>)->Statement {
        Statement::Access(event(op,path,loan,parent))
    }
    fn write(path:Path,loan:SymbolId)->Statement {
        let effect=VerifiedAppliedEffect{path:path.clone(),
            kind:VerifiedEffectKind::Write,alternatives:Vec::new()};
        Statement::Call{name:"certified_write".into(),token:3,
            events:vec![event(Access::Write,path,loan,None)],
            effects:vec![effect.clone()],
            path_cases:vec![VerifiedAppliedPathCase{
                effects:vec![effect],returned:None,uninitialized:vec![],
            }],
        }
    }
    fn fixture()->FunctionMir {
        let root=owner();
        let n=root.child(field(0));
        let other=root.child(field(1));
        let unrelated=Path::root(SymbolId(601));
        FunctionMir{entry:0,loans:HashMap::from([
            (SymbolId(502),root.clone()),
            (SymbolId(503),root.clone()),
            (SymbolId(504),root.clone()),
            (SymbolId(505),n.clone()),
            (SymbolId(506),other),
            (SymbolId(602),unrelated),
        ]),blocks:vec![BasicBlock{statements:vec![
            access(Access::BorrowMut,root.clone(),SymbolId(502),None),
            write(n,SymbolId(502)),
        ],terminator:Terminator::Return}]}
    }
    fn insert(mir:&mut FunctionMir,op:Access,path:Path,id:u32,parent:Option<u32>){
        mir.blocks[0].statements.insert(1,access(op,path,SymbolId(id),parent.map(SymbolId)));
    }
    fn audit(mir:&FunctionMir)->bool {mir.validate_interprocedural_alias_proofs().is_ok()}
    #[test]
    fn ordinary_exclusive_loan_remains_an_ordered_write_witness(){
        assert!(audit(&fixture()));
    }
    #[test]
    fn live_mutable_child_suspends_parent_write_certificate(){
        let mut mir=fixture();
        insert(&mut mir,Access::BorrowMut,owner(),503,Some(502));
        assert!(!audit(&mir));
    }
    #[test]
    fn live_shared_child_also_suspends_mutable_parent(){
        let mut mir=fixture();
        insert(&mut mir,Access::BorrowShared,owner(),503,Some(502));
        assert!(!audit(&mir));
    }
    #[test]
    fn ending_child_reactivates_parent_at_next_call(){
        let mut mir=fixture();
        insert(&mut mir,Access::EndLoan,owner(),503,None);
        insert(&mut mir,Access::BorrowMut,owner(),503,Some(502));
        assert!(audit(&mir));
    }
    #[test]
    fn ending_child_after_the_write_does_not_retroactively_allow_it(){
        let mut mir=fixture();
        insert(&mut mir,Access::BorrowMut,owner(),503,Some(502));
        mir.blocks[0].statements.push(access(Access::EndLoan,owner(),SymbolId(503),None));
        assert!(!audit(&mir));
    }
    #[test]
    fn grandchild_suspends_all_its_active_ancestors(){
        let mut mir=fixture();
        insert(&mut mir,Access::BorrowMut,owner(),504,Some(503));
        insert(&mut mir,Access::BorrowMut,owner(),503,Some(502));
        assert!(!audit(&mir));
    }
    #[test]
    fn ending_only_grandchild_does_not_reactivate_grandparent(){
        let mut mir=fixture();
        insert(&mut mir,Access::EndLoan,owner(),504,None);
        insert(&mut mir,Access::BorrowMut,owner(),504,Some(503));
        insert(&mut mir,Access::BorrowMut,owner(),503,Some(502));
        assert!(!audit(&mir));
    }
    #[test]
    fn ending_both_descendants_restores_the_grandparent(){
        let mut mir=fixture();
        insert(&mut mir,Access::EndLoan,owner(),503,None);
        insert(&mut mir,Access::EndLoan,owner(),504,None);
        insert(&mut mir,Access::BorrowMut,owner(),504,Some(503));
        insert(&mut mir,Access::BorrowMut,owner(),503,Some(502));
        assert!(audit(&mir));
    }
    #[test]
    fn independent_owner_does_not_suspend_a_valid_write(){
        let mut mir=fixture();
        insert(&mut mir,Access::BorrowMut,Path::root(SymbolId(601)),602,None);
        assert!(audit(&mir));
    }
    #[test]
    fn disjoint_sibling_reborrow_does_not_suspend_its_sibling(){
        let mut mir=fixture();
        let a=owner().child(field(0));
        let b=owner().child(field(1));
        mir.blocks[0].statements[1]=write(a.clone(),SymbolId(505));
        insert(&mut mir,Access::BorrowMut,b,506,Some(502));
        insert(&mut mir,Access::BorrowMut,a,505,Some(502));
        assert!(audit(&mir));
    }
    #[test]
    fn local_child_borrow_before_call_write_suspends_parent(){
        let mut mir=fixture();
        let Statement::Call{events,..}=&mut mir.blocks[0].statements[1]
            else{unreachable!()};
        events.insert(0,event(Access::BorrowMut,owner(),SymbolId(503),Some(SymbolId(502))));
        assert!(!audit(&mir));
    }
    #[test]
    fn call_local_child_ended_before_write_restores_parent(){
        let mut mir=fixture();
        let Statement::Call{events,..}=&mut mir.blocks[0].statements[1]
            else{unreachable!()};
        events.insert(0,event(Access::EndLoan,owner(),SymbolId(503),None));
        events.insert(0,event(Access::BorrowMut,owner(),SymbolId(503),Some(SymbolId(502))));
        assert!(audit(&mir));
    }
    #[test]
    fn loan_borrowed_only_after_write_does_not_retroactively_suspend_it(){
        let mut mir=fixture();
        let Statement::Call{events,..}=&mut mir.blocks[0].statements[1]
            else{unreachable!()};
        events.push(event(Access::BorrowMut,owner(),SymbolId(503),Some(SymbolId(502))));
        assert!(audit(&mir));
    }
    #[test]
    fn shared_loan_cannot_certify_a_mutable_write_itself(){
        let mut mir=fixture();
        mir.blocks[0].statements[0]=access(Access::BorrowShared,owner(),SymbolId(502),None);
        assert!(!audit(&mir));
    }
    #[test]
    fn nested_staged_write_uses_child_capability_not_suspended_parent(){
        let mut mir=fixture();
        mir.blocks[0].statements[1]=write(owner().child(field(0)),SymbolId(503));
        insert(&mut mir,Access::BorrowMut,owner(),503,Some(502));
        assert!(audit(&mir));
    }
    #[test]
    fn forged_unparented_overlapping_loan_cannot_authorize_parent_write(){
        let mut mir=fixture();
        insert(&mut mir,Access::BorrowMut,owner(),503,None);
        assert!(!audit(&mir));
    }
    #[test]
    fn child_of_disjoint_field_still_suspends_whole_parent(){
        let mut mir=fixture();
        insert(&mut mir,Access::BorrowShared,owner().child(field(1)),506,Some(502));
        assert!(!audit(&mir));
    }
    #[test]
    fn ending_shared_child_restores_mutable_parent_witness(){
        let mut mir=fixture();
        insert(&mut mir,Access::EndLoan,owner(),503,None);
        insert(&mut mir,Access::BorrowShared,owner(),503,Some(502));
        assert!(audit(&mir));
    }
}

#[cfg(test)]
mod cross_call_phi_predicate_correlation_0682_tests {
    use super::*;
    const TOKENS:usize=100;
    fn root(n:u32)->Path{Path::root(SymbolId(n))}
    fn key(n:u32)->FieldKey{
        FieldKey{aggregate:TypeId(0),field:FieldId(n)}
    }
    fn borrow(path:Path,loan:u32)->Statement {
        Statement::Access(Event{op:Access::BorrowMut,path,
            loan:Some(SymbolId(loan)),parent:None,token:1})
    }
    fn phi(owner:u32,generation:u32,loans:[u32;2],paths:[Path;2])->Statement {
        Statement::ValuePhi{
            ty:ConstType::RefMut(Box::new(ConstType::Named("Blob".into()))),
            predecessors:vec![1,2],check:Event{op:Access::Read,
                path:root(owner),loan:None,parent:None,token:2},
            generation:Some(SymbolId(generation)),provenance:None,
            alternatives:loans.iter().zip(paths).map(|(loan,path)|RefOption{
                loan:SymbolId(*loan),path,exclusive:true,parent:None,
            }).collect(),
        }
    }
    fn sym_effect(owner:u32,paths:[Path;2],field:u32)->VerifiedAppliedEffect {
        VerifiedAppliedEffect{path:root(owner),kind:VerifiedEffectKind::Write,
            alternatives:paths.into_iter().map(|p|p.child(key(field))).collect()}
    }
    fn call(owner:u32,generation:u32,paths:[Path;2],fields:&[u32])->Statement {
        let effects=fields.iter().map(|&field|sym_effect(owner,paths.clone(),field))
            .collect::<Vec<_>>();
        Statement::Call{name:"certified_write".into(),token:3,
            events:vec![Event{op:Access::Write,path:root(owner),
                loan:Some(SymbolId(generation)),parent:None,token:3}],
            path_cases:effects.iter().map(|effect|VerifiedAppliedPathCase{
                effects:vec![effect.clone()],returned:None,uninitialized:vec![],
            }).collect(),effects,
        }
    }
    fn graph()->FunctionMir {
        let a=root(101);let b=root(102);let c=root(103);let d=root(104);
        let first=phi(210,310,[401,402],[a.clone(),b.clone()]);
        let second=phi(211,311,[403,404],[c.clone(),d.clone()]);
        let write_first=call(210,310,[a.clone(),b.clone()],&[0,1]);
        let write_second=call(211,311,[c.clone(),d.clone()],&[0]);
        FunctionMir{entry:0,loans:HashMap::from([
                (SymbolId(401),a.clone()),(SymbolId(402),b.clone()),
                (SymbolId(403),c.clone()),(SymbolId(404),d.clone()),
            ]),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![borrow(a,401),borrow(c,403)],
                terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![borrow(b,402),borrow(d,404)],
                terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![first,second,write_first,write_second],
                terminator:Terminator::Return},
        ]}
    }
    fn cases(mir:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        mir.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Blob".into())),
            ("b".into(),ConstType::Named("Blob".into())),
            ("c".into(),ConstType::Named("Blob".into())),
            ("d".into(),ConstType::Named("Blob".into())),
        ],&[])
    }
    fn effect(parameter:usize,field:u32)->VerifiedParameterEffect{
        VerifiedParameterEffect{parameter,fields:vec![key(field)],
            kind:VerifiedEffectKind::Write}
    }
    #[test]
    fn two_phis_share_one_predecessor_choice_across_two_calls(){
        let found=cases(&graph()).expect("exact correlated CFG certificate");
        assert_eq!(found.len(),4);
        assert!(found.iter().all(|case|{
            case.effects.len()==2 &&
            ((case.effects.contains(&effect(0,0)) ||
                case.effects.contains(&effect(0,1))) &&
                case.effects.contains(&effect(2,0)) ||
             (case.effects.contains(&effect(1,0)) ||
                case.effects.contains(&effect(1,1))) &&
                case.effects.contains(&effect(3,0)))
        }));
    }
    #[test]
    fn callee_conditional_write_cases_remain_independent(){
        let found=cases(&graph()).unwrap();
        for parameter in [0,1]{
            assert!(found.iter().any(|c|c.effects.contains(&effect(parameter,0))));
            assert!(found.iter().any(|c|c.effects.contains(&effect(parameter,1))));
        }
    }
    #[test]
    fn no_impossible_cross_predecessor_effect_pairs(){
        let found=cases(&graph()).unwrap();
        assert!(!found.iter().any(|c|c.effects.iter().any(|e|e.parameter==0) &&
            c.effects.iter().any(|e|e.parameter==3)));
        assert!(!found.iter().any(|c|c.effects.iter().any(|e|e.parameter==1) &&
            c.effects.iter().any(|e|e.parameter==2)));
    }
    #[test]
    fn swapping_one_symbolic_candidate_owner_rejects_certificate(){
        let mut mir=graph();
        if let Statement::Call{effects,path_cases,..}=&mut mir.blocks[3].statements[2] {
            effects[0].alternatives[0]=root(104).child(key(0));
            path_cases[0].effects[0]=effects[0].clone();
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn swapping_the_candidate_field_rejects_certificate(){
        let mut mir=graph();
        if let Statement::Call{effects,path_cases,..}=&mut mir.blocks[3].statements[2] {
            effects[0].alternatives[1]=root(102).child(key(1));
            path_cases[0].effects[0]=effects[0].clone();
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn invented_phi_generation_fails_closed(){
        let mut mir=graph();
        if let Statement::Call{events,..}=&mut mir.blocks[3].statements[2] {
            events[0].loan=Some(SymbolId(999));
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn losing_one_conditional_effect_witness_fails_closed(){
        let mut mir=graph();
        if let Statement::Call{path_cases,..}=&mut mir.blocks[3].statements[2] {
            path_cases.pop();
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn ending_selected_loan_before_second_call_fails_closed(){
        let mut mir=graph();
        mir.blocks[1].statements.push(Statement::Access(Event{
            op:Access::EndLoan,path:root(103),loan:Some(SymbolId(403)),
            parent:None,token:2,
        }));
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn missing_one_phi_source_on_branch_fails_closed(){
        let mut mir=graph();
        mir.blocks[2].statements.pop();
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn disjunctive_move_is_not_authenticated_as_mutable_write(){
        let mut mir=graph();
        if let Statement::Call{effects,path_cases,..}=&mut mir.blocks[3].statements[2] {
            effects[0].kind=VerifiedEffectKind::Move;
            path_cases[0].effects[0].kind=VerifiedEffectKind::Move;
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn symbolic_effect_without_complete_cases_is_not_certified(){
        let mut mir=graph();
        if let Statement::Call{path_cases,..}=&mut mir.blocks[3].statements[2] {
            path_cases.clear();
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn verifying_full_mir_cannot_use_forged_phi_effect_path(){
        let mut mir=graph();
        if let Statement::Call{effects,path_cases,..}=&mut mir.blocks[3].statements[2] {
            effects[0].alternatives[0]=root(999).child(key(0));
            path_cases[0].effects[0]=effects[0].clone();
        }
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn different_incoming_edges_are_not_conflated_by_equal_case_indexes(){
        let found=cases(&graph()).unwrap();
        assert_eq!(found.len(),4);
        assert!(found.iter().all(|c|c.returned.is_none()));
    }
    fn returned_graph()->FunctionMir {
        let a=root(101);let b=root(102);
        let direct=|path:Path,loan:u32,fields:&[u32]| {
            let effects=fields.iter().map(|field|VerifiedAppliedEffect{
                path:path.child(key(*field)),kind:VerifiedEffectKind::Write,
                alternatives:vec![],
            }).collect::<Vec<_>>();
            Statement::Call{name:"verified".into(),token:2,
                events:effects.iter().map(|effect|Event{op:Access::Write,
                    path:effect.path.clone(),loan:Some(SymbolId(loan)),
                    parent:None,token:2}).collect(),
                path_cases:effects.iter().map(|effect|VerifiedAppliedPathCase{
                    effects:vec![effect.clone()],returned:None,uninitialized:vec![],
                }).collect(),effects,
            }
        };
        FunctionMir{entry:0,
            loans:HashMap::from([(SymbolId(401),a.clone()),(SymbolId(402),b.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![borrow(a.clone(),401),
                    direct(a.clone(),401,&[0]),direct(a,401,&[1,2])],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![borrow(b.clone(),402),
                    direct(b.clone(),402,&[0]),direct(b,402,&[1,2])],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![phi(210,310,[401,402],[root(101),root(102)])],
                    terminator:Terminator::Return},
            ],
        }
    }
    fn return_cases(mir:&FunctionMir)->Option<Vec<VerifiedPathCase>>{
        let ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        mir.solve_path_cases(TOKENS,&[("a".into(),ty.clone()),("b".into(),ty.clone())],&[
            VerifiedReturnedReference{parameter:0,fields:vec![],ty:ty.clone()},
            VerifiedReturnedReference{parameter:1,fields:vec![],ty},
        ])
    }
    #[test]
    fn return_origin_inherits_predecessor_correlated_write_cases(){
        let found=return_cases(&returned_graph()).expect("exact return/effect cases");
        assert_eq!(found.len(),4);
        assert!(found.iter().all(|case|{
            case.effects.len()==2 && case.returned.is_some_and(|origin|origin<2) &&
            case.effects.iter().all(|effect|Some(effect.parameter)==case.returned)
        }));
    }
    #[test]
    fn independent_callee_effect_choice_does_not_change_return_origin(){
        let found=return_cases(&returned_graph()).unwrap();
        for index in 0..2 {
            assert_eq!(found.iter().filter(|c|c.returned==Some(index)).count(),2);
            assert!(found.iter().filter(|c|c.returned==Some(index)).any(|c|
                c.effects.contains(&effect(index,1))));
            assert!(found.iter().filter(|c|c.returned==Some(index)).any(|c|
                c.effects.contains(&effect(index,2))));
        }
    }
    #[test]
    fn forged_terminal_phi_parent_does_not_publish_return_origin(){
        let mut mir=returned_graph();
        if let Statement::ValuePhi{alternatives,..}=&mut mir.blocks[3].statements[0] {
            alternatives[1].loan=SymbolId(999);
        }
        assert!(return_cases(&mir).is_none());
    }
    #[test]
    fn forged_terminal_return_path_does_not_publish_case(){
        let mut mir=returned_graph();
        if let Statement::ValuePhi{alternatives,..}=&mut mir.blocks[3].statements[0] {
            alternatives[0].path=root(103);
        }
        assert!(return_cases(&mir).is_none());
    }
    #[test]
    fn omitted_outer_call_effect_case_refuses_return_certificate(){
        let mut mir=returned_graph();
        if let Statement::Call{path_cases,..}=&mut mir.blocks[1].statements[2] {
            path_cases.pop();
        }
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
    }
    #[test]
    fn duplicate_phi_generation_is_not_a_proof(){
        let mut mir=graph();
        if let Statement::ValuePhi{generation,..}=&mut mir.blocks[3].statements[1] {
            *generation=Some(SymbolId(310));
        }
        assert!(cases(&mir).is_none());
    }
}

#[cfg(test)]
mod transitive_late_phi_case_correlation_0683_tests {
    use super::*;
    const TOKENS:usize=100;
    fn root(n:u32)->Path {Path::root(SymbolId(n))}
    fn key(n:u32)->FieldKey {FieldKey{aggregate:TypeId(0),field:FieldId(n)}}
    fn ty()->ConstType {ConstType::RefMut(Box::new(ConstType::Named("Blob".into())))}
    fn option(loan:u32,path:Path,parent:Option<u32>)->RefOption {
        RefOption{loan:SymbolId(loan),path,exclusive:true,parent:parent.map(SymbolId)}
    }
    fn borrow(path:Path,loan:u32)->Statement {
        Statement::Access(Event{op:Access::BorrowMut,path,
            loan:Some(SymbolId(loan)),parent:None,token:1})
    }
    fn phi()->Statement {
        Statement::ValuePhi{ty:ty(),predecessors:vec![1,2],
            check:Event{op:Access::Read,path:root(210),loan:None,parent:None,token:2},
            generation:Some(SymbolId(310)),provenance:None,
            alternatives:vec![option(401,root(101),None),option(402,root(102),None)]}
    }
    fn stage(source:u32,generation:u32,owner:u32,loans:[u32;2],parents:[u32;2])->Statement {
        Statement::LatePhiReborrow{ty:ty(),source_generation:SymbolId(source),
            generation:SymbolId(generation),projection:None,
            children:vec![option(loans[0],root(101),Some(parents[0])),
                option(loans[1],root(102),Some(parents[1]))],
            event:Event{op:Access::BindPhiMut,path:root(owner),
                loan:Some(SymbolId(generation)),parent:Some(SymbolId(source)),token:3}}
    }
    fn effect(owner:u32,field:u32)->VerifiedAppliedEffect {
        VerifiedAppliedEffect{path:root(owner),kind:VerifiedEffectKind::Write,
            alternatives:vec![root(101).child(key(field)),root(102).child(key(field))]}
    }
    fn call(owner:u32,generation:u32,fields:&[u32])->Statement {
        let effects=fields.iter().map(|field|effect(owner,*field)).collect::<Vec<_>>();
        Statement::Call{name:"certified".into(),token:4,
            events:vec![Event{op:Access::Write,path:root(owner),
                loan:Some(SymbolId(generation)),parent:None,token:4}],
            path_cases:effects.iter().map(|item|VerifiedAppliedPathCase{
                effects:vec![item.clone()],returned:None,uninitialized:vec![]}).collect(),
            effects}
    }
    fn end(path:Path,loan:u32)->Statement {
        Statement::Access(Event{op:Access::EndLoan,path,loan:Some(SymbolId(loan)),
            parent:None,token:5})
    }
    fn graph(two_stages:bool)->FunctionMir {
        let mut loans=HashMap::from([
            (SymbolId(401),root(101)),(SymbolId(402),root(102)),
            (SymbolId(501),root(101)),(SymbolId(502),root(102)),
        ]);
        let mut statements=vec![phi(),stage(310,311,211,[501,502],[401,402])];
        if two_stages {
            loans.insert(SymbolId(601),root(101));
            loans.insert(SymbolId(602),root(102));
            statements.push(stage(311,312,212,[601,602],[501,502]));
            statements.push(call(212,312,&[0,1]));
            statements.push(call(212,312,&[0]));
        }else{
            statements.push(call(211,311,&[0,1]));
            statements.push(call(211,311,&[0]));
        }
        FunctionMir{entry:0,loans,blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![borrow(root(101),401)],
                terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![borrow(root(102),402)],
                terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements,terminator:Terminator::Return},
        ]}
    }
    fn cases(mir:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        mir.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Blob".into())),
            ("b".into(),ConstType::Named("Blob".into())),
        ],&[])
    }
    fn expected(parameter:usize,field:u32)->VerifiedParameterEffect {
        VerifiedParameterEffect{parameter,fields:vec![key(field)],kind:VerifiedEffectKind::Write}
    }
    #[test]
    fn late_phi_writes_retain_original_predecessor_on_both_calls(){
        let found=cases(&graph(false)).expect("late reborrow is authenticated");
        assert_eq!(found.len(),4);
        for case in found {
            assert!(case.effects.contains(&expected(0,0)) ||
                case.effects.contains(&expected(1,0)));
            let zero=case.effects.iter().any(|e|e.parameter==0);
            let one=case.effects.iter().any(|e|e.parameter==1);
            assert_ne!(zero,one,"one actual predecessor per execution");
        }
    }
    #[test]
    fn two_late_generations_preserve_transitive_owner_and_independent_cases(){
        let found=cases(&graph(true)).expect("two-level provenance");
        assert_eq!(found.len(),4);
        for case in &found {
            let parameter=case.effects[0].parameter;
            assert!(case.effects.contains(&expected(parameter,0)));
            assert!(case.effects.iter().all(|e|e.parameter==parameter));
            assert!((1..=2).contains(&case.effects.len()));
        }
        assert!(found.iter().any(|case|case.effects.len()==2));
    }
    #[test]
    fn later_call_can_use_child_not_suspended_parent(){
        let mir=graph(true);
        assert!(mir.validate_interprocedural_alias_proofs().is_ok());
        assert!(cases(&mir).is_some());
    }
    #[test]
    fn selected_parent_cannot_write_while_child_is_alive(){
        let mut mir=graph(true);
        mir.blocks[3].statements.push(call(211,311,&[0]));
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn ending_only_one_conditional_child_cannot_unsuspend_both_parents(){
        let mut mir=graph(true);
        mir.blocks[3].statements.push(end(root(101),601));
        mir.blocks[3].statements.push(call(211,311,&[0]));
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn unknown_source_generation_is_not_a_proof(){
        let mut mir=graph(false);
        if let Statement::LatePhiReborrow{source_generation,..}=&mut mir.blocks[3].statements[1]{
            *source_generation=SymbolId(999);
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn source_generation_cannot_be_claimed_by_another_stage(){
        let mut mir=graph(true);
        if let Statement::LatePhiReborrow{generation,..}=&mut mir.blocks[3].statements[2]{
            *generation=SymbolId(311);
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn wrong_child_parent_does_not_rebind_reference(){
        let mut mir=graph(false);
        if let Statement::LatePhiReborrow{children,..}=&mut mir.blocks[3].statements[1]{
            children[1].parent=Some(SymbolId(401));
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn child_cannot_escape_its_selected_parent_movepath(){
        let mut mir=graph(false);
        if let Statement::LatePhiReborrow{children,..}=&mut mir.blocks[3].statements[1]{
            children[0].path=root(102);
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn forged_parent_loan_is_never_implicitly_created(){
        let mut mir=graph(false);
        if let Statement::LatePhiReborrow{children,..}=&mut mir.blocks[3].statements[1]{
            children[0].parent=Some(SymbolId(999));
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn reusing_an_original_phi_loan_for_child_is_not_a_new_generation(){
        let mut mir=graph(false);
        if let Statement::LatePhiReborrow{children,..}=&mut mir.blocks[3].statements[1]{
            children[0].loan=SymbolId(402);
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn missing_one_child_is_not_a_complete_provenance_set(){
        let mut mir=graph(false);
        if let Statement::LatePhiReborrow{children,..}=&mut mir.blocks[3].statements[1]{
            children.pop();
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn endloan_before_the_late_binding_invalidates_the_source(){
        let mut mir=graph(false);
        mir.blocks[1].statements.push(end(root(101),401));
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn endloan_on_the_selected_child_invalidates_second_call(){
        let mut mir=graph(false);
        mir.blocks[3].statements.insert(2,end(root(101),501));
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn damaged_generation_on_call_does_not_use_another_phi(){
        let mut mir=graph(false);
        if let Statement::Call{events,..}=&mut mir.blocks[3].statements[2]{
            events[0].loan=Some(SymbolId(310));
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn swapping_one_effect_candidate_for_a_sibling_owner_is_denied(){
        let mut mir=graph(false);
        if let Statement::Call{effects,path_cases,..}=&mut mir.blocks[3].statements[2]{
            effects[0].alternatives[1]=root(101).child(key(0));
            path_cases[0].effects[0]=effects[0].clone();
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn omitted_conditional_case_cannot_certify_cross_call_effects(){
        let mut mir=graph(true);
        if let Statement::Call{path_cases,..}=&mut mir.blocks[3].statements[3]{
            path_cases.pop();
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn alias_auditor_accepts_authenticated_late_generation(){
        let mir=graph(false);
        assert!(mir.validate_interprocedural_alias_proofs().is_ok());
    }
    #[test]
    fn alias_auditor_rejects_late_generation_defined_after_call(){
        let mut mir=graph(false);
        mir.blocks[3].statements.swap(1,2);
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn terminal_return_loan_must_remain_live_through_return(){
        let mut mir=graph(false);
        mir.blocks[3].statements=vec![phi()];
        let origins=vec![
            VerifiedReturnedReference{parameter:0,fields:vec![],ty:ty()},
            VerifiedReturnedReference{parameter:1,fields:vec![],ty:ty()},
        ];
        let formals=vec![("a".into(),ty()),("b".into(),ty())];
        let valid=mir.solve_path_cases(TOKENS,&formals,&origins)
            .expect("terminal PHI return is initially live");
        assert_eq!(valid.len(),2);
        mir.blocks[3].statements.push(end(root(101),401));
        assert!(mir.solve_path_cases(TOKENS,&formals,&origins).is_none());
    }

}

#[cfg(test)]
mod correlated_whole_place_phi_write_0684_tests {
    use super::*;
    const TOKENS:usize=100;
    fn root(id:u32)->Path {Path::root(SymbolId(id))}
    fn key(index:u32)->FieldKey {
        FieldKey{aggregate:TypeId(0),field:FieldId(index)}
    }
    fn ty()->ConstType {
        ConstType::RefMut(Box::new(ConstType::Named("Blob".into())))
    }
    fn option(id:u32,path:Path,parent:Option<u32>)->RefOption {
        RefOption{loan:SymbolId(id),path,exclusive:true,parent:parent.map(SymbolId)}
    }
    fn borrow(path:Path,id:u32)->Statement {
        Statement::Access(Event{op:Access::BorrowMut,path,loan:Some(SymbolId(id)),
            parent:None,token:1})
    }
    fn end(path:Path,id:u32)->Statement {
        Statement::Access(Event{op:Access::EndLoan,path,loan:Some(SymbolId(id)),
            parent:None,token:2})
    }
    fn phi(owner:u32,generation:u32,ids:[u32;2],paths:[Path;2])->Statement {
        Statement::ValuePhi{ty:ty(),predecessors:vec![1,2],
            check:Event{op:Access::Read,path:root(owner),loan:None,parent:None,token:2},
            generation:Some(SymbolId(generation)),provenance:None,
            alternatives:ids.iter().zip(paths).map(|(id,path)|option(*id,path,None)).collect()}
    }
    fn stage(source:u32,generation:u32,owner:u32,ids:[u32;2],parents:[u32;2],
        paths:[Path;2])->Statement {
        Statement::LatePhiReborrow{ty:ty(),source_generation:SymbolId(source),
            generation:SymbolId(generation),projection:None,
            children:ids.iter().zip(parents).zip(paths).map(|((id,parent),path)|
                option(*id,path,Some(parent))).collect(),
            event:Event{op:Access::BindPhiMut,path:root(owner),
                loan:Some(SymbolId(generation)),parent:Some(SymbolId(source)),token:3}}
    }
    fn write_effect(owner:u32,paths:[Path;2],field:Option<u32>)->VerifiedAppliedEffect {
        VerifiedAppliedEffect{path:root(owner),kind:VerifiedEffectKind::Write,
            alternatives:paths.into_iter().map(|p|match field {
                Some(f)=>p.child(key(f)),None=>p,
            }).collect()}
    }
    fn call(owner:u32,generation:u32,paths:[Path;2],fields:&[Option<u32>])->Statement {
        let effects=fields.iter().map(|field|write_effect(owner,paths.clone(),*field))
            .collect::<Vec<_>>();
        Statement::Call{name:"verified_conditional_writer".into(),token:4,
            events:vec![Event{op:Access::Write,path:root(owner),
                loan:Some(SymbolId(generation)),parent:None,token:4}],
            path_cases:effects.iter().map(|e|VerifiedAppliedPathCase{
                effects:vec![e.clone()],returned:None,uninitialized:vec![],
            }).collect(),effects}
    }
    fn graph(late:bool,deep:bool,two_groups:bool,conditional:bool)->FunctionMir {
        let a=root(101);let b=root(102);let c=root(103);let d=root(104);
        let mut loans=HashMap::from([(SymbolId(401),a.clone()),
            (SymbolId(402),b.clone()),(SymbolId(403),c.clone()),
            (SymbolId(404),d.clone())]);
        let mut statements=vec![phi(210,310,[401,402],[a.clone(),b.clone()])];
        if two_groups {
            statements.push(phi(211,311,[403,404],[c.clone(),d.clone()]));
        }
        let mut owner=210;let mut generation=310;
        if late {
            statements.push(stage(310,320,220,[501,502],[401,402],
                [a.clone(),b.clone()]));
            loans.insert(SymbolId(501),a.clone());loans.insert(SymbolId(502),b.clone());
            owner=220;generation=320;
        }
        if deep {
            assert!(late);
            statements.push(stage(320,321,221,[601,602],[501,502],
                [a.clone(),b.clone()]));
            loans.insert(SymbolId(601),a.clone());loans.insert(SymbolId(602),b.clone());
            owner=221;generation=321;
        }
        let cases=if conditional {vec![None,Some(0)]}else{vec![None]};
        statements.push(call(owner,generation,[a.clone(),b.clone()],&cases));
        if two_groups {
            statements.push(call(211,311,[c.clone(),d.clone()],&cases));
        }else if conditional {
            statements.push(call(owner,generation,[a.clone(),b.clone()],&[None]));
        }
        FunctionMir{entry:0,loans,blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:if two_groups {
                vec![borrow(a,401),borrow(c,403)]
            }else{vec![borrow(a,401)]},terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:if two_groups {
                vec![borrow(b,402),borrow(d,404)]
            }else{vec![borrow(b,402)]},terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements,terminator:Terminator::Return},
        ]}
    }
    fn cases(mir:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        mir.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Blob".into())),
            ("b".into(),ConstType::Named("Blob".into())),
            ("c".into(),ConstType::Named("Blob".into())),
            ("d".into(),ConstType::Named("Blob".into())),
        ],&[])
    }
    fn expected(parameter:usize,field:Option<u32>)->VerifiedParameterEffect {
        VerifiedParameterEffect{parameter,
            fields:field.map(|f|vec![key(f)]).unwrap_or_default(),
            kind:VerifiedEffectKind::Write}
    }
    #[test]
    fn direct_phi_can_write_the_whole_selected_referent() {
        let mir=graph(false,false,false,false);
        assert!(mir.validate_interprocedural_alias_proofs().is_ok());
        let found=cases(&mir).expect("both predecessor witnesses are exact");
        assert_eq!(found.len(),2);
        assert!(found.iter().any(|c|c.effects==vec![expected(0,None)]));
        assert!(found.iter().any(|c|c.effects==vec![expected(1,None)]));
    }
    #[test]
    fn late_phi_can_write_whole_referent_via_its_child_loan() {
        let mir=graph(true,false,false,false);
        assert!(mir.validate_interprocedural_alias_proofs().is_ok());
        let found=cases(&mir).expect("late child preserves original owner");
        assert_eq!(found.len(),2);
        assert!(found.iter().any(|c|c.effects==vec![expected(0,None)]));
        assert!(found.iter().any(|c|c.effects==vec![expected(1,None)]));
    }
    #[test]
    fn two_late_generations_keep_the_actual_owner_for_root_write() {
        let mir=graph(true,true,false,false);
        let found=cases(&mir).expect("transitive whole-referent loan");
        assert_eq!(found.len(),2);
        assert!(found.iter().all(|c|c.effects.len()==1 && c.effects[0].fields.is_empty()));
    }
    #[test]
    fn same_predecessor_controls_two_independent_root_write_groups() {
        let mir=graph(true,false,true,false);
        let found=cases(&mir).expect("two independently witnessed PHI groups");
        assert_eq!(found.len(),2);
        for c in found {
            assert!(c.effects==vec![expected(0,None),expected(2,None)] ||
                c.effects==vec![expected(1,None),expected(3,None)]);
        }
    }
    #[test]
    fn root_and_field_conditional_cases_do_not_merge_between_calls() {
        let mir=graph(true,false,true,true);
        let found=cases(&mir).expect("independent callee case choices");
        assert_eq!(found.len(),8);
        for c in found {
            let params=c.effects.iter().map(|e|e.parameter).collect::<HashSet<_>>();
            assert!(params==HashSet::from([0,2]) || params==HashSet::from([1,3]));
            assert_eq!(c.effects.len(),2);
        }
    }
    #[test]
    fn root_effect_cannot_claim_the_other_predecessor_owner() {
        let mut mir=graph(false,false,false,false);
        if let Statement::Call{effects,path_cases,..}=&mut mir.blocks[3].statements[1] {
            effects[0].alternatives[1]=root(101);
            path_cases[0].effects[0]=effects[0].clone();
        }
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn mixing_whole_object_and_field_projection_is_not_a_uniform_effect() {
        let mut mir=graph(false,false,false,false);
        if let Statement::Call{effects,path_cases,..}=&mut mir.blocks[3].statements[1] {
            effects[0].alternatives[1]=root(102).child(key(0));
            path_cases[0].effects[0]=effects[0].clone();
        }
        assert!(mir.validate_interprocedural_alias_proofs().is_err());
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn late_child_cannot_borrow_an_unrelated_parent_loan() {
        let mut mir=graph(true,false,false,false);
        if let Statement::LatePhiReborrow{children,..}=&mut mir.blocks[3].statements[1] {
            children[0].parent=Some(SymbolId(402));
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn ending_a_selected_child_before_root_write_invalidates_the_effect() {
        let mut mir=graph(true,false,false,false);
        mir.blocks[3].statements.insert(2,end(root(101),501));
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn root_write_cannot_use_a_suspended_parent_loan() {
        let mut mir=graph(true,false,false,false);
        mir.blocks[3].statements.push(call(210,310,
            [root(101),root(102)],&[None]));
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn moved_referent_cannot_be_silently_authenticated_as_root_write() {
        let mut mir=graph(false,false,false,false);
        mir.blocks[3].statements.insert(1,Statement::Access(Event{
            op:Access::Move,path:root(101),loan:None,parent:None,token:3,
        }));
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn wrong_phi_generation_cannot_witness_a_root_write() {
        let mut mir=graph(false,false,false,false);
        if let Statement::Call{events,..}=&mut mir.blocks[3].statements[1] {
            events[0].loan=Some(SymbolId(999));
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn missing_root_write_case_is_not_a_certificate() {
        let mut mir=graph(true,false,false,true);
        if let Statement::Call{path_cases,..}=&mut mir.blocks[3].statements[2] {
            path_cases.pop();
        }
        assert!(cases(&mir).is_none());
    }
    #[test]
    fn forged_field_suffix_cannot_be_hidden_in_a_second_call() {
        let mut mir=graph(true,false,true,true);
        if let Statement::Call{effects,path_cases,..}=&mut mir.blocks[3].statements[4] {
            effects[1].alternatives[0]=root(103).child(key(1));
            path_cases[1].effects[0]=effects[1].clone();
        }
        assert!(cases(&mir).is_none());
    }
}

#[cfg(test)]
mod conditional_call_ownership_0685_tests {
    use super::*;
    const TOKENS:usize=100;
    fn root()->Path { Path::root(SymbolId(101)) }
    fn key(n:u32)->FieldKey { FieldKey{aggregate:TypeId(1),field:FieldId(n)} }
    fn left()->Path {root().child(key(0))}
    fn right()->Path {root().child(key(1))}
    fn eff(path:Path,kind:VerifiedEffectKind)->VerifiedAppliedEffect {
        VerifiedAppliedEffect{path,kind,alternatives:Vec::new()}
    }
    fn branch(effects:Vec<VerifiedAppliedEffect>,dead:Vec<Path>)->VerifiedAppliedPathCase {
        VerifiedAppliedPathCase{effects,returned:None,uninitialized:dead}
    }
    fn call(cases:Vec<VerifiedAppliedPathCase>)->Statement {
        let mut effects=Vec::new();
        for case in &cases {for effect in &case.effects {
            if !effects.contains(effect){effects.push(effect.clone());}
        }}
        Statement::Call{name:"verified".into(),token:1,events:Vec::new(),effects,
            path_cases:cases}
    }
    fn statement(op:Access,path:Path)->Statement {
        Statement::Access(Event{op,path,loan:None,parent:None,token:2})
    }
    fn mir(stmts:Vec<Statement>)->FunctionMir {
        FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![BasicBlock{
            statements:stmts,terminator:Terminator::Return,
        }]}
    }
    fn solve(mir:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        mir.solve_path_cases(TOKENS,&[("p".into(),ConstType::Named("Pair".into()))],&[])
    }
    fn moved(field:u32)->VerifiedParameterPath {
        VerifiedParameterPath{parameter:0,fields:vec![key(field)]}
    }
    #[test]
    fn conditional_move_is_preserved_only_on_its_actual_case() {
        let m=mir(vec![call(vec![
            branch(vec![eff(left(),VerifiedEffectKind::Move)],vec![left()]),
            branch(vec![eff(right(),VerifiedEffectKind::Write)],vec![]),
        ])]);
        let cases=solve(&m).expect("all cases have finite ownership states");
        assert_eq!(cases.len(),2);
        assert!(cases.iter().any(|c|c.uninitialized==vec![moved(0)] &&
            c.effects.iter().any(|e|e.kind==VerifiedEffectKind::Move)));
        assert!(cases.iter().any(|c|c.uninitialized.is_empty() &&
            c.effects.iter().any(|e|e.kind==VerifiedEffectKind::Write)));
    }
    #[test]
    fn read_of_maybe_moved_field_is_rejected_after_the_call() {
        let m=mir(vec![call(vec![
            branch(vec![eff(left(),VerifiedEffectKind::Move)],vec![left()]),
            branch(vec![eff(right(),VerifiedEffectKind::Write)],vec![]),
        ]),statement(Access::Read,left())]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn unrelated_field_remains_available_after_conditional_move() {
        let m=mir(vec![call(vec![
            branch(vec![eff(left(),VerifiedEffectKind::Move)],vec![left()]),
            branch(vec![eff(right(),VerifiedEffectKind::Write)],vec![]),
        ]),statement(Access::Read,right())]);
        assert_eq!(solve(&m).unwrap().len(),2);
    }
    #[test]
    fn conditional_drop_has_the_same_liveness_effect_as_move() {
        let m=mir(vec![call(vec![
            branch(vec![eff(left(),VerifiedEffectKind::Drop)],vec![left()]),
            branch(vec![],vec![]),
        ]),statement(Access::Read,left())]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn effect_case_cannot_claim_uninitialized_path_without_consuming_it() {
        let m=mir(vec![call(vec![branch(vec![eff(right(),VerifiedEffectKind::Write)],
            vec![left()])])]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn unknown_independent_call_choices_must_not_be_correlated() {
        let first=call(vec![
            branch(vec![eff(left(),VerifiedEffectKind::Move)],vec![left()]),
            branch(vec![eff(right(),VerifiedEffectKind::Move)],vec![right()]),
        ]);
        let second=call(vec![
            branch(vec![eff(left(),VerifiedEffectKind::Write)],vec![]),
            branch(vec![eff(right(),VerifiedEffectKind::Write)],vec![]),
        ]);
        assert!(solve(&mir(vec![first,second,statement(Access::Read,left())])).is_none());
    }
    #[test]
    fn exact_write_reinitializes_previously_moved_field() {
        let m=mir(vec![statement(Access::Move,left()),
            call(vec![branch(vec![eff(left(),VerifiedEffectKind::Write)],vec![])]),
            statement(Access::Read,left())]);
        let cases=solve(&m).expect("the field is written on every path");
        assert_eq!(cases.len(),1);
        assert!(cases[0].uninitialized.is_empty());
    }
    #[test]
    fn by_value_transfer_does_not_resurrect_the_caller_after_callee_write() {
        let transfer=Event{op:Access::Move,path:root(),loan:None,parent:None,token:1};
        let write=eff(left(),VerifiedEffectKind::Write);
        let m=mir(vec![Statement::Call{name:"consuming_writer".into(),token:1,
            events:vec![transfer],effects:vec![write.clone()],
            path_cases:vec![branch(vec![write],vec![])]},
            statement(Access::Read,left())]);
        assert!(solve(&m).is_none(),"caller cannot access consumed owned argument");
    }
    #[test]
    fn case_move_inside_transferred_argument_is_not_a_second_move() {
        let transfer=Event{op:Access::Move,path:root(),loan:None,parent:None,token:1};
        let partial=eff(left(),VerifiedEffectKind::Move);
        let m=mir(vec![Statement::Call{name:"consuming_move".into(),token:1,
            events:vec![transfer],effects:vec![partial.clone()],
            path_cases:vec![branch(vec![partial],vec![left()])]}]);
        let cases=solve(&m).expect("by-value transfer is applied exactly once");
        assert_eq!(cases.len(),1);
        assert_eq!(cases[0].uninitialized,vec![VerifiedParameterPath{
            parameter:0,fields:vec![],
        }],"callee partial move must not reinitialize transferred root");
    }
    fn returned_phi_graph(consume_first:bool)->FunctionMir {
        let a=Path::root(SymbolId(101));
        let b=Path::root(SymbolId(102));
        let ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        let first_effect=eff(a.clone(),if consume_first {
            VerifiedEffectKind::Move
        }else{VerifiedEffectKind::Write});
        let second_effect=eff(b.clone(),VerifiedEffectKind::Write);
        let first_case=branch(vec![first_effect.clone()],if consume_first {
            vec![a.clone()]
        }else{vec![]});
        let second_case=branch(vec![second_effect.clone()],vec![]);
        let option_a=RefOption{loan:SymbolId(201),path:a.clone(),
            exclusive:true,parent:None};
        let option_b=RefOption{loan:SymbolId(202),path:b.clone(),
            exclusive:true,parent:None};
        let first=vec![Statement::Access(Event{
            op:Access::BorrowMut,path:a.clone(),loan:Some(SymbolId(201)),
            parent:None,token:1,
        }),call(vec![first_case,branch(vec![],vec![])])];
        let second=vec![Statement::Access(Event{
            op:Access::BorrowMut,path:b.clone(),loan:Some(SymbolId(202)),
            parent:None,token:1,
        }),call(vec![second_case,branch(vec![],vec![])])];
        FunctionMir{entry:0,loans:HashMap::from([
            (SymbolId(201),a.clone()),(SymbolId(202),b.clone()),
        ]),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:first,terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:second,terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![Statement::ValuePhi{
                ty,predecessors:vec![1,2],generation:Some(SymbolId(301)),
                check:Event{op:Access::Read,path:Path::root(SymbolId(300)),
                    loan:None,parent:None,token:3},
                provenance:None,alternatives:vec![option_a,option_b],
            }],terminator:Terminator::Return},
        ]}
    }
    fn returned_origins()->Vec<VerifiedReturnedReference> {
        let ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        vec![VerifiedReturnedReference{parameter:0,fields:vec![],ty:ty.clone()},
            VerifiedReturnedReference{parameter:1,fields:vec![],ty}]
    }
    fn solve_return(mir:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        mir.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Blob".into())),
            ("b".into(),ConstType::Named("Blob".into())),
        ],&returned_origins())
    }
    #[test]
    fn two_return_origins_retain_branch_local_effect_cases() {
        let found=solve_return(&returned_phi_graph(false))
            .expect("effect cases must retain their own PHI owner");
        assert_eq!(found.len(),4);
        for case in &found {
            assert!(case.uninitialized.is_empty());
            match case.returned {
                Some(0)=>assert!(case.effects.iter().all(|e|e.parameter==0)),
                Some(1)=>assert!(case.effects.iter().all(|e|e.parameter==1)),
                _=>panic!("forged or lost return-origin"),
            }
        }
        assert_eq!(found.iter().filter(|c|c.returned==Some(0)).count(),2);
        assert_eq!(found.iter().filter(|c|c.returned==Some(1)).count(),2);
    }
    #[test]
    fn conditional_consumption_cannot_certify_a_returned_phi_owner() {
        let mir=returned_phi_graph(true);
        assert!(solve_return(&mir).is_none());
    }
    #[test]
    fn may_write_without_exact_path_cases_cannot_resurrect_a_move() {
        let maybe=VerifiedAppliedEffect{path:left(),kind:VerifiedEffectKind::Write,
            alternatives:Vec::new()};
        let m=mir(vec![statement(Access::Move,left()),Statement::Call{
            name:"uncorrelated".into(),token:1,events:Vec::new(),
            effects:vec![maybe],path_cases:Vec::new(),
        },statement(Access::Read,left())]);
        assert!(solve(&m).is_none());
    }
}

#[cfg(test)]
mod conditional_consumption_regions_0686_tests {
    use super::*;
    const TOKENS:usize=100;
    fn root(id:u32)->Path {Path::root(SymbolId(id))}
    fn field(id:u32,index:u32)->Path {
        root(id).child(FieldKey{aggregate:TypeId(0),field:FieldId(index)})
    }
    fn borrow(path:Path,id:u32,parent:Option<u32>,exclusive:bool)->Statement {
        Statement::Access(Event{
            op:if exclusive{Access::BorrowMut}else{Access::BorrowShared},
            path,loan:Some(SymbolId(id)),parent:parent.map(SymbolId),token:1,
        })
    }
    fn end(path:Path,id:u32)->Statement {
        Statement::Access(Event{op:Access::EndLoan,path,
            loan:Some(SymbolId(id)),parent:None,token:2})
    }
    fn exact(path:Path,kind:VerifiedEffectKind)->Statement {
        let effect=VerifiedAppliedEffect{path:path.clone(),kind,alternatives:Vec::new()};
        Statement::Call{name:"verified_case".into(),token:3,events:vec![],
            effects:vec![effect.clone()],path_cases:vec![VerifiedAppliedPathCase{
                effects:vec![effect],returned:None,
                uninitialized:if matches!(kind,VerifiedEffectKind::Move|VerifiedEffectKind::Drop){
                    vec![path]
                }else{vec![]},
            }]}
    }
    fn mir(stmts:Vec<Statement>,loans:Vec<(u32,Path)>)->FunctionMir {
        FunctionMir{entry:0,loans:loans.into_iter()
            .map(|(id,path)|(SymbolId(id),path)).collect(),
            blocks:vec![BasicBlock{statements:stmts,terminator:Terminator::Return}]}
    }
    fn solve(m:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        m.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Pair".into())),
            ("b".into(),ConstType::Named("Pair".into())),
        ],&[])
    }
    #[test]
    fn conditional_move_cannot_consume_a_live_mutable_referent() {
        let p=field(101,0);
        let m=mir(vec![borrow(p.clone(),501,None,true),
            exact(p.clone(),VerifiedEffectKind::Move)],vec![(501,p)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn conditional_drop_cannot_consume_a_live_shared_referent() {
        let p=field(101,0);
        let m=mir(vec![borrow(p.clone(),501,None,false),
            exact(p.clone(),VerifiedEffectKind::Drop)],vec![(501,p)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn disjoint_field_move_remains_legal_with_live_sibling_loan() {
        let left=field(101,0);let right=field(101,1);
        let m=mir(vec![borrow(left.clone(),501,None,true),
            exact(right,VerifiedEffectKind::Move)],vec![(501,left)]);
        let cases=solve(&m).expect("sibling fields do not overlap");
        assert_eq!(cases.len(),1);
        assert_eq!(cases[0].uninitialized,vec![VerifiedParameterPath{
            parameter:0,fields:vec![FieldKey{aggregate:TypeId(0),field:FieldId(1)}],
        }]);
    }
    #[test]
    fn independent_owner_drop_remains_legal_with_live_mutable_loan() {
        let left=root(101);let right=root(102);
        let m=mir(vec![borrow(left.clone(),501,None,true),
            exact(right,VerifiedEffectKind::Drop)],vec![(501,left)]);
        let cases=solve(&m).expect("independent owners are disjoint");
        assert_eq!(cases[0].uninitialized.len(),1);
        assert_eq!(cases[0].uninitialized[0].parameter,1);
    }
    #[test]
    fn ended_loan_allows_a_later_move_of_its_referent() {
        let p=field(101,0);
        let m=mir(vec![borrow(p.clone(),501,None,true),end(p.clone(),501),
            exact(p.clone(),VerifiedEffectKind::Move)],vec![(501,p)]);
        assert!(solve(&m).is_some());
    }
    #[test]
    fn ending_a_child_does_not_release_its_live_parent() {
        let p=root(101);
        let m=mir(vec![borrow(p.clone(),501,None,true),
            borrow(field(101,0),502,Some(501),true),end(field(101,0),502),
            exact(p.clone(),VerifiedEffectKind::Move)],vec![
                (501,p),(502,field(101,0)),
            ]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn ending_the_complete_loan_chain_allows_subsequent_move() {
        let p=root(101);
        let m=mir(vec![borrow(p.clone(),501,None,true),
            borrow(field(101,0),502,Some(501),true),end(field(101,0),502),end(p.clone(),501),
            exact(p.clone(),VerifiedEffectKind::Move)],vec![
                (501,p),(502,field(101,0)),
            ]);
        assert!(solve(&m).is_some());
    }
    #[test]
    fn unknown_live_loan_cannot_prove_non_aliasing_for_a_move() {
        let p=field(101,0);
        let m=mir(vec![borrow(p.clone(),501,None,true),
            exact(field(102,0),VerifiedEffectKind::Move)],vec![]);
        assert!(solve(&m).is_none());
    }
    fn two_source_return(first_consumed:Path,second_consumed:Path)
        ->FunctionMir {
        let a=root(101);let b=root(102);
        let ty=ConstType::RefMut(Box::new(ConstType::Named("Pair".into())));
        let returned_phi=Statement::ValuePhi{ty,
            predecessors:vec![1,2],generation:Some(SymbolId(601)),
            check:Event{op:Access::Read,path:root(600),loan:None,
                parent:None,token:4},provenance:None,
            alternatives:vec![
                RefOption{loan:SymbolId(501),path:a.clone(),exclusive:true,parent:None},
                RefOption{loan:SymbolId(502),path:b.clone(),exclusive:true,parent:None},
            ],
        };
        FunctionMir{entry:0,loans:HashMap::from([
            (SymbolId(501),a.clone()),(SymbolId(502),b.clone()),
        ]),blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:vec![borrow(a,501,None,true),
                exact(first_consumed,VerifiedEffectKind::Move)],
                terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![borrow(b,502,None,true),
                exact(second_consumed,VerifiedEffectKind::Drop)],
                terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:vec![returned_phi],terminator:Terminator::Return},
        ]}
    }
    fn multi_return_cases(m:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        let ty=ConstType::RefMut(Box::new(ConstType::Named("Pair".into())));
        m.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Pair".into())),
            ("b".into(),ConstType::Named("Pair".into())),
        ],&[
            VerifiedReturnedReference{parameter:0,fields:vec![],ty:ty.clone()},
            VerifiedReturnedReference{parameter:1,fields:vec![],ty},
        ])
    }
    #[test]
    fn multiple_return_origins_keep_independent_consumption_on_their_edges() {
        let m=two_source_return(root(102),root(101));
        let cases=multi_return_cases(&m).expect("each arm consumes only the other owner");
        assert_eq!(cases.len(),2);
        assert!(cases.iter().any(|c|c.returned==Some(0) &&
            c.uninitialized.iter().any(|p|p.parameter==1)));
        assert!(cases.iter().any(|c|c.returned==Some(1) &&
            c.uninitialized.iter().any(|p|p.parameter==0)));
    }
    #[test]
    fn multiple_return_origins_reject_consumption_of_first_referent() {
        let m=two_source_return(root(101),root(101));
        assert!(multi_return_cases(&m).is_none());
    }
    #[test]
    fn multiple_return_origins_reject_consumption_of_second_referent() {
        let m=two_source_return(root(102),root(102));
        assert!(multi_return_cases(&m).is_none());
    }
    #[test]
    fn uncertified_second_may_move_cannot_reuse_a_consumed_field() {
        let p=field(101,0);
        let possible=VerifiedAppliedEffect{path:p.clone(),
            kind:VerifiedEffectKind::Move,alternatives:Vec::new()};
        let may_call=Statement::Call{name:"uncorrelated".into(),token:3,
            events:Vec::new(),effects:vec![possible],path_cases:Vec::new()};
        let m=mir(vec![exact(p,VerifiedEffectKind::Move),may_call],vec![]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn a_move_on_only_one_branch_cannot_be_excused_by_the_other_branch() {
        let p=root(101);
        let m=FunctionMir{entry:0,loans:HashMap::from([(SymbolId(501),p.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![borrow(p.clone(),501,None,true)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![exact(p,VerifiedEffectKind::Move)],
                    terminator:Terminator::Return},
            ]};
        assert!(solve(&m).is_none());
    }
}

#[cfg(test)]
mod cfg_region_boundary_0687_tests {
    use super::*;
    const TOKENS:usize=100;
    fn root(id:u32)->Path{Path::root(SymbolId(id))}
    fn field(id:u32,index:u32)->Path{
        root(id).child(FieldKey{aggregate:TypeId(0),field:FieldId(index)})
    }
    fn access(op:Access,path:Path,loan:Option<u32>,parent:Option<u32>)->Statement{
        Statement::Access(Event{op,path,loan:loan.map(SymbolId),
            parent:parent.map(SymbolId),token:0})
    }
    fn borrow(path:Path,id:u32,parent:Option<u32>)->Statement{
        access(Access::BorrowMut,path,Some(id),parent)
    }
    fn shared(path:Path,id:u32,parent:Option<u32>)->Statement{
        access(Access::BorrowShared,path,Some(id),parent)
    }
    fn end(path:Path,id:u32)->Statement{
        access(Access::EndLoan,path,Some(id),None)
    }
    fn effect(path:Path,kind:VerifiedEffectKind)->Statement{
        let applied=VerifiedAppliedEffect{path:path.clone(),kind,
            alternatives:Vec::new()};
        Statement::Call{name:"certified_region_effect".into(),token:0,
            events:Vec::new(),effects:vec![applied.clone()],
            path_cases:vec![VerifiedAppliedPathCase{
                effects:vec![applied],returned:None,
                uninitialized:if matches!(kind,VerifiedEffectKind::Move|VerifiedEffectKind::Drop){
                    vec![path]
                }else{Vec::new()},
            }]}
    }
    fn solve(m:&FunctionMir)->Option<Vec<VerifiedPathCase>>{
        m.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Pair".into())),
            ("b".into(),ConstType::Named("Pair".into())),
        ],&[])
    }
    fn diamond(first:Vec<Statement>,second:Vec<Statement>,
        joined:Vec<Statement>,loans:&[(u32,Path)])->FunctionMir{
        let loans=loans.iter().map(|(id,path)|(SymbolId(*id),path.clone())).collect();
        FunctionMir{entry:0,loans,blocks:vec![
            BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
            BasicBlock{statements:first,terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:second,terminator:Terminator::Goto(vec![3])},
            BasicBlock{statements:joined,terminator:Terminator::Return},
        ]}
    }
    fn nested_chain()->(Vec<Statement>,Vec<(u32,Path)>){
        let a=root(101);let first=field(101,0);let deep=first.child(
            FieldKey{aggregate:TypeId(1),field:FieldId(0)});
        (vec![borrow(a.clone(),501,None),borrow(first.clone(),502,Some(501)),
            borrow(deep.clone(),503,Some(502))],
            vec![(501,a),(502,first),(503,deep)])
    }
    #[test]
    fn both_predecessors_can_release_their_last_mutable_loan(){
        let a=root(101);
        let m=diamond(vec![borrow(a.clone(),501,None),end(a.clone(),501)],
            vec![borrow(a.clone(),502,None),end(a.clone(),502)],
            vec![effect(a.clone(),VerifiedEffectKind::Move)],
            &[(501,a.clone()),(502,a)]);
        let cases=solve(&m).expect("each path ends its own borrow");
        assert_eq!(cases.len(),1);
        assert_eq!(cases[0].uninitialized.len(),1);
    }
    #[test]
    fn a_loan_still_live_on_one_predecessor_blocks_consumption(){
        let a=root(101);
        let m=diamond(vec![borrow(a.clone(),501,None),end(a.clone(),501)],
            vec![borrow(a.clone(),502,None)],
            vec![effect(a.clone(),VerifiedEffectKind::Move)],
            &[(501,a.clone()),(502,a)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn reborrow_child_ending_on_one_edge_does_not_end_parent(){
        let a=root(101);let f=field(101,0);
        let m=diamond(vec![borrow(a.clone(),501,None),borrow(f.clone(),502,Some(501)),
                end(f.clone(),502)],
            vec![borrow(a.clone(),501,None)],
            vec![effect(a.clone(),VerifiedEffectKind::Move)],
            &[(501,a.clone()),(502,f)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn child_then_parent_release_before_join_allows_consumption(){
        let a=root(101);let f=field(101,0);
        let m=diamond(vec![borrow(a.clone(),501,None),borrow(f.clone(),502,Some(501)),
                end(f.clone(),502),end(a.clone(),501)],
            vec![borrow(a.clone(),501,None),end(a.clone(),501)],
            vec![effect(a.clone(),VerifiedEffectKind::Move)],
            &[(501,a.clone()),(502,f)]);
        assert!(solve(&m).is_some());
    }
    #[test]
    fn parent_cannot_end_while_child_is_active_on_a_single_path(){
        let a=root(101);let f=field(101,0);
        let m=diamond(vec![borrow(a.clone(),501,None),borrow(f.clone(),502,Some(501)),
                end(a.clone(),501)],vec![],vec![],
            &[(501,a),(502,f)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn a_shared_child_also_blocks_premature_parent_end(){
        let a=root(101);let f=field(101,0);
        let m=diamond(vec![borrow(a.clone(),501,None),shared(f.clone(),502,Some(501)),
                end(a.clone(),501)],vec![],vec![],
            &[(501,a),(502,f)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn release_in_wrong_order_cannot_be_fixed_retroactively(){
        let (mut seq,loans)=nested_chain();
        seq.push(end(root(101),501));
        seq.push(end(field(101,0).child(FieldKey{aggregate:TypeId(1),field:FieldId(0)}),503));
        let m=diamond(seq,vec![],vec![],&loans);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn leaf_middle_root_release_order_is_accepted(){
        let (mut seq,loans)=nested_chain();
        let deep=field(101,0).child(FieldKey{aggregate:TypeId(1),field:FieldId(0)});
        seq.extend([end(deep,503),end(field(101,0),502),end(root(101),501)]);
        seq.push(effect(root(101),VerifiedEffectKind::Drop));
        let m=diamond(seq,vec![],vec![],&loans);
        assert!(solve(&m).is_some());
    }
    #[test]
    fn forged_endloan_cannot_release_another_referent(){
        let a=root(101);
        let m=diamond(vec![borrow(a.clone(),501,None),end(root(102),501)],
            vec![],vec![],&[(501,a)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn unknown_endloan_is_not_a_release_witness(){
        let a=root(101);
        let m=diamond(vec![borrow(a.clone(),501,None),end(a.clone(),999)],
            vec![],vec![effect(a.clone(),VerifiedEffectKind::Move)],&[(501,a)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn reborrow_from_parent_absent_on_this_cfg_branch_is_rejected(){
        let a=root(101);let f=field(101,0);
        let m=diamond(vec![borrow(a.clone(),501,None)],
            vec![borrow(f.clone(),502,Some(501))],vec![],
            &[(501,a),(502,f)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn child_reborrow_cannot_escape_parent_movepath(){
        let a=field(101,0);let b=field(101,1);
        let m=diamond(vec![borrow(a.clone(),501,None),borrow(b.clone(),502,Some(501))],
            vec![],vec![],&[(501,a),(502,b)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn reborrow_can_restart_after_child_end_without_ending_parent(){
        let a=root(101);let f=field(101,0);
        let seq=vec![borrow(a.clone(),501,None),borrow(f.clone(),502,Some(501)),
            end(f.clone(),502),borrow(f.clone(),503,Some(501)),end(f,503),
            end(a.clone(),501),effect(a.clone(),VerifiedEffectKind::Move)];
        let m=diamond(seq,vec![],vec![],&[(501,a),(502,field(101,0)),
            (503,field(101,0))]);
        assert!(solve(&m).is_some());
    }
    #[test]
    fn disjoint_field_consumption_is_still_permitted_with_live_reborrow(){
        let a=root(101);let left=field(101,0);let right=field(101,1);
        let m=diamond(vec![borrow(a.clone(),501,None),borrow(left.clone(),502,Some(501)),
                effect(root(102),VerifiedEffectKind::Move)],
            vec![],vec![],&[(501,a),(502,left)]);
        assert!(solve(&m).is_some());
        let mut changed=m;
        if let Statement::Call{effects,path_cases,..}=&mut changed.blocks[1].statements[2]{
            effects[0].path=right.clone();
            path_cases[0].effects[0].path=right.clone();
            path_cases[0].uninitialized=vec![right];
        }
        assert!(solve(&changed).is_none());
    }
}

#[cfg(test)]
mod automatic_nll_statement_edges_0688_tests {
    use super::*;
    fn path(id:u32)->Path {Path::root(SymbolId(id))}
    fn ev(op:Access,path:Path,loan:Option<u32>,parent:Option<u32>,token:usize)->Statement {
        Statement::Access(Event{op,path,loan:loan.map(SymbolId),
            parent:parent.map(SymbolId),token})
    }
    fn function(stmts:Vec<Statement>,loans:&[(u32,Path)])->FunctionMir {
        FunctionMir{entry:0,
            loans:loans.iter().map(|(id,p)|(SymbolId(*id),p.clone())).collect(),
            blocks:vec![
                BasicBlock{statements:stmts,terminator:Terminator::Goto(vec![1])},
                BasicBlock{statements:vec![],terminator:Terminator::Return},
            ]}
    }
    fn errors(m:&FunctionMir)->Vec<cfg_borrow::Conflict> {m.verify().expect("structurally valid MIR")}
    #[test]
    fn final_use_in_same_block_ends_before_unborrowed_owner_write() {
        let p=path(31);
        let m=function(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None,0),
            ev(Access::Read,p.clone(),Some(501),None,1),
            ev(Access::Write,p.clone(),None,None,2),
        ],&[(501,p)]);
        assert!(errors(&m).is_empty());
    }
    #[test]
    fn loan_with_later_use_cannot_end_before_owner_write() {
        let p=path(31);
        let m=function(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None,0),
            ev(Access::Read,p.clone(),Some(501),None,1),
            ev(Access::Write,p.clone(),None,None,2),
            ev(Access::Read,p.clone(),Some(501),None,3),
        ],&[(501,p)]);
        assert!(errors(&m).iter().any(|e|e.token==2));
    }
    #[test]
    fn unused_temporary_mutable_borrow_ends_at_its_creation_statement() {
        let p=path(31);
        let m=function(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None,0),
            ev(Access::Write,p.clone(),None,None,1),
        ],&[(501,p)]);
        assert!(errors(&m).is_empty());
    }
    #[test]
    fn child_expires_before_parent_and_owner_becomes_available() {
        let p=path(31);
        let m=function(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None,0),
            ev(Access::BorrowMut,p.clone(),Some(502),Some(501),1),
            ev(Access::Write,p.clone(),Some(502),None,2),
            ev(Access::Write,p.clone(),None,None,3),
        ],&[(501,p.clone()),(502,p)]);
        assert!(errors(&m).is_empty());
    }
    #[test]
    fn later_child_use_keeps_parent_chain_live() {
        let p=path(31);
        let m=function(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None,0),
            ev(Access::BorrowMut,p.clone(),Some(502),Some(501),1),
            ev(Access::Write,p.clone(),None,None,2),
            ev(Access::Write,p.clone(),Some(502),None,3),
        ],&[(501,p.clone()),(502,p)]);
        assert!(errors(&m).iter().any(|e|e.token==2));
    }
    #[test]
    fn explicit_early_parent_end_is_not_hidden_by_automatic_nll() {
        let p=path(31);
        let m=function(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None,0),
            ev(Access::BorrowMut,p.clone(),Some(502),Some(501),1),
            ev(Access::EndLoan,p.clone(),Some(501),None,2),
            ev(Access::EndLoan,p.clone(),Some(502),None,3),
        ],&[(501,p.clone()),(502,p)]);
        assert!(errors(&m).iter().any(|e|e.token==2));
    }
    #[test]
    fn independent_cfg_edges_terminate_only_their_dead_loans() {
        let p=path(31);
        let m=FunctionMir{entry:0,loans:HashMap::from([(SymbolId(501),p.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![ev(Access::BorrowMut,p.clone(),Some(501),None,0)],
                    terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![ev(Access::Read,p.clone(),Some(501),None,1)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![ev(Access::Write,p.clone(),None,None,3)],
                    terminator:Terminator::Return},
            ]};
        assert!(errors(&m).is_empty());
    }
    fn phi_with_post_join_ops(post:Vec<Statement>)->FunctionMir {
        let a=path(31);let b=path(32);let binding=path(40);
        let mut merged=vec![Statement::ValuePhi{
            ty:ConstType::RefMut(Box::new(ConstType::I64)),
            predecessors:vec![1,2],
            check:Event{op:Access::Read,path:binding.clone(),loan:None,
                parent:None,token:3},
            generation:Some(SymbolId(600)),provenance:None,
            alternatives:vec![
                RefOption{loan:SymbolId(501),path:a.clone(),exclusive:true,parent:None},
                RefOption{loan:SymbolId(502),path:b.clone(),exclusive:true,parent:None},
            ],
        }];
        merged.extend(post);
        FunctionMir{entry:0,loans:HashMap::from([
            (SymbolId(501),a.clone()),(SymbolId(502),b.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![ev(Access::BorrowMut,a,Some(501),None,1)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![ev(Access::BorrowMut,b,Some(502),None,2)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:merged,terminator:Terminator::Goto(vec![4])},
                BasicBlock{statements:vec![],terminator:Terminator::Return},
            ]}
    }
    #[test]
    fn unneeded_phi_generation_releases_both_alternatives_before_owner_write() {
        let m=phi_with_post_join_ops(vec![
            ev(Access::Read,path(40),Some(600),None,4),
            ev(Access::Write,path(31),None,None,5),
        ]);
        assert!(errors(&m).is_empty());
    }
    #[test]
    fn phi_source_is_not_released_before_a_later_phi_use() {
        let m=phi_with_post_join_ops(vec![
            ev(Access::Write,path(31),None,None,4),
            ev(Access::Read,path(40),Some(600),None,5),
        ]);
        assert!(errors(&m).iter().any(|e|e.token==4));
    }
    #[test]
    fn two_returned_phi_origins_cannot_be_expired_on_incoming_edges() {
        let a=path(31);let b=path(32);let binding=path(40);
        let ty=ConstType::RefMut(Box::new(ConstType::I64));
        let options=vec![
            RefOption{loan:SymbolId(501),path:a.clone(),exclusive:true,parent:None},
            RefOption{loan:SymbolId(502),path:b.clone(),exclusive:true,parent:None},
        ];
        let m=FunctionMir{entry:0,loans:HashMap::from([
            (SymbolId(501),a.clone()),(SymbolId(502),b.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![ev(Access::BorrowMut,a,Some(501),None,1)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![ev(Access::BorrowMut,b,Some(502),None,2)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![Statement::ValuePhi{
                    ty,predecessors:vec![1,2],
                    check:Event{op:Access::Read,path:binding,loan:None,parent:None,token:3},
                    generation:Some(SymbolId(600)),provenance:None,alternatives:options,
                }],terminator:Terminator::Return},
            ]};
        assert!(errors(&m).is_empty());
    }
}

#[cfg(test)]
mod interprocedural_inferred_nll_0689_tests {
    use super::*;
    const TOKENS:usize=100;
    fn p(id:u32)->Path {Path::root(SymbolId(id))}
    fn e(op:Access,path:Path,loan:Option<u32>,parent:Option<u32>)->Statement {
        Statement::Access(Event{op,path,loan:loan.map(SymbolId),
            parent:parent.map(SymbolId),token:1})
    }
    fn borrow(path:Path,id:u32,parent:Option<u32>)->Statement {
        e(Access::BorrowMut,path,Some(id),parent)
    }
    fn read(path:Path,id:u32)->Statement {e(Access::Read,path,Some(id),None)}
    fn exact(kind:VerifiedEffectKind,path:Path)->Statement {
        let effect=VerifiedAppliedEffect{path:path.clone(),kind,alternatives:vec![]};
        let op=match kind {
            VerifiedEffectKind::Move=>Access::Move,
            VerifiedEffectKind::Drop=>Access::Move,
            VerifiedEffectKind::Write=>Access::Write,
        };
        Statement::Call{name:"verified_case".into(),token:2,
            events:vec![Event{op,path:path.clone(),loan:None,parent:None,token:2}],
            effects:vec![effect.clone()],path_cases:vec![VerifiedAppliedPathCase{
                effects:vec![effect],returned:None,
                uninitialized:if matches!(kind,VerifiedEffectKind::Move|VerifiedEffectKind::Drop){
                    vec![path]
                }else{vec![]},
            }]}
    }
    fn plain(stmts:Vec<Statement>,loans:&[(u32,Path)])->FunctionMir {
        FunctionMir{entry:0,loans:loans.iter().map(|(id,path)|
            (SymbolId(*id),path.clone())).collect(),blocks:vec![
            BasicBlock{statements:stmts,terminator:Terminator::Goto(vec![1])},
            BasicBlock{statements:vec![],terminator:Terminator::Return},
        ]}
    }
    fn solve(mir:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        mir.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Blob".into())),
            ("b".into(),ConstType::Named("Blob".into())),
        ],&[])
    }
    #[test]
    fn unobserved_borrow_cannot_be_automatically_released_for_a_move() {
        let a=p(101);
        let m=plain(vec![borrow(a.clone(),501,None),
            exact(VerifiedEffectKind::Move,a.clone())],&[(501,a)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn unobserved_child_cannot_be_auto_ended_before_explicit_parent_end() {
        let a=p(101);
        let m=plain(vec![borrow(a.clone(),501,None),
            borrow(a.clone(),502,Some(501)),
            e(Access::EndLoan,a.clone(),Some(501),None)],
            &[(501,a.clone()),(502,a)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn statement_last_use_before_effectful_move_releases_loan() {
        let a=p(101);
        let m=plain(vec![borrow(a.clone(),501,None),read(a.clone(),501),
            exact(VerifiedEffectKind::Move,a.clone())],&[(501,a)]);
        assert!(m.verify().unwrap().is_empty());
        let cases=solve(&m).expect("last-use boundary is available to the call solver");
        assert_eq!(cases.len(),1);
        assert_eq!(cases[0].uninitialized,vec![VerifiedParameterPath{
            parameter:0,fields:vec![],
        }]);
    }
    #[test]
    fn later_use_keeps_loan_live_across_conditional_move() {
        let a=p(101);
        let m=plain(vec![borrow(a.clone(),501,None),
            exact(VerifiedEffectKind::Move,a.clone()),read(a.clone(),501)],&[(501,a)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn nested_child_and_parent_expire_in_dependency_order() {
        let a=p(101);
        let m=plain(vec![borrow(a.clone(),501,None),
            borrow(a.clone(),502,Some(501)),read(a.clone(),502),
            exact(VerifiedEffectKind::Drop,a.clone())],
            &[(501,a.clone()),(502,a)]);
        assert!(m.verify().unwrap().is_empty());
        assert!(solve(&m).is_some());
    }
    #[test]
    fn child_used_later_prevents_parent_expiry() {
        let a=p(101);
        let m=plain(vec![borrow(a.clone(),501,None),
            borrow(a.clone(),502,Some(501)),
            exact(VerifiedEffectKind::Move,a.clone()),read(a.clone(),502)],
            &[(501,a.clone()),(502,a)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn explicit_parent_end_still_fails_when_child_is_used() {
        let a=p(101);
        let m=plain(vec![borrow(a.clone(),501,None),
            borrow(a.clone(),502,Some(501)),
            e(Access::EndLoan,a.clone(),Some(501),None),read(a.clone(),502)],
            &[(501,a.clone()),(502,a)]);
        assert!(solve(&m).is_none());
        assert!(!m.verify().unwrap().is_empty());
    }
    fn diamond(last_use_at_join:bool)->FunctionMir {
        let a=p(101);
        FunctionMir{entry:0,loans:HashMap::from([(SymbolId(501),a.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![borrow(a.clone(),501,None)],
                    terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![read(a.clone(),501)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:if last_use_at_join {
                    vec![exact(VerifiedEffectKind::Move,a.clone()),read(a,501)]
                }else{vec![exact(VerifiedEffectKind::Move,a)]},
                    terminator:Terminator::Return},
            ]}
    }
    #[test]
    fn each_cfg_edge_releases_only_its_own_dead_loan() {
        let m=diamond(false);
        assert!(m.verify().unwrap().is_empty());
        assert!(solve(&m).is_some());
    }
    #[test]
    fn join_use_prevents_early_expiry_on_both_incoming_edges() {
        assert!(solve(&diamond(true)).is_none());
    }
    #[test]
    fn loop_backedge_keeps_loan_live_until_exit_edge() {
        let a=p(101);
        let m=FunctionMir{entry:0,
            loans:HashMap::from([(SymbolId(501),a.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![borrow(a.clone(),501,None)],
                    terminator:Terminator::Goto(vec![1])},
                BasicBlock{statements:vec![read(a.clone(),501)],
                    terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![exact(VerifiedEffectKind::Move,a)],
                    terminator:Terminator::Return},
            ]};
        assert!(m.verify().unwrap().is_empty());
        assert!(solve(&m).is_some());
    }
    #[test]
    fn independent_paths_are_not_rejected_by_loan_from_other_owner() {
        let a=p(101);let b=p(102);
        let m=plain(vec![borrow(a.clone(),501,None),read(a.clone(),501),
            exact(VerifiedEffectKind::Move,b)],&[(501,a)]);
        assert!(solve(&m).is_some());
    }
    #[test]
    fn independent_callee_effect_cases_remain_distinct_after_last_use() {
        let a=p(101);let b=p(102);
        let m=FunctionMir{entry:0,
            loans:HashMap::from([(SymbolId(501),a.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![borrow(a.clone(),501,None)],
                    terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![read(a.clone(),501),
                    exact(VerifiedEffectKind::Move,a.clone())],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![read(a.clone(),501),
                    exact(VerifiedEffectKind::Drop,b)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![],terminator:Terminator::Return},
            ]};
        assert!(m.verify().unwrap().is_empty());
        let cases=solve(&m).expect("each branch's exact call is independently valid");
        assert_eq!(cases.len(),2);
        assert!(cases.iter().any(|case|case.uninitialized.iter()
            .any(|path|path.parameter==0)));
        assert!(cases.iter().any(|case|case.uninitialized.iter()
            .any(|path|path.parameter==1)));
    }
    fn shared_phi_diamond(move_before_last_read:bool)->FunctionMir {
        let a=p(101);let b=p(102);let binding=p(600);
        let phi=Statement::ValuePhi{
            ty:ConstType::Ref(Box::new(ConstType::Named("Blob".into()))),
            predecessors:vec![1,2],generation:Some(SymbolId(610)),
            check:Event{op:Access::Read,path:binding.clone(),
                loan:None,parent:None,token:3},provenance:None,
            alternatives:vec![
                RefOption{loan:SymbolId(501),path:a.clone(),
                    exclusive:false,parent:None},
                RefOption{loan:SymbolId(502),path:b.clone(),
                    exclusive:false,parent:None},
            ],
        };
        let phi_use=read(binding,610);
        let move_a=exact(VerifiedEffectKind::Move,a.clone());
        let after=if move_before_last_read {vec![phi,move_a,phi_use]}
            else{vec![phi,phi_use,move_a]};
        FunctionMir{entry:0,loans:HashMap::from([
            (SymbolId(501),a.clone()),(SymbolId(502),b.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![e(Access::BorrowShared,a,Some(501),None)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![e(Access::BorrowShared,b,Some(502),None)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:after,terminator:Terminator::Goto(vec![4])},
                BasicBlock{statements:vec![],terminator:Terminator::Return},
            ]}
    }
    #[test]
    fn shared_phi_last_use_allows_later_owned_transfer() {
        let m=shared_phi_diamond(false);
        assert!(m.verify().unwrap().is_empty());
        assert!(solve(&m).is_some());
    }
    #[test]
    fn future_shared_phi_use_blocks_owned_transfer_on_possible_owner() {
        assert!(solve(&shared_phi_diamond(true)).is_none());
    }
    #[test]
    fn returned_phi_sources_remain_live_through_cleanup_edges() {
        let a=p(101);let b=p(102);
        let ty=ConstType::RefMut(Box::new(ConstType::Named("Blob".into())));
        let m=FunctionMir{entry:0,loans:HashMap::from([
            (SymbolId(501),a.clone()),(SymbolId(502),b.clone())]),
            blocks:vec![
                BasicBlock{statements:vec![],terminator:Terminator::Goto(vec![1,2])},
                BasicBlock{statements:vec![borrow(a.clone(),501,None)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![borrow(b.clone(),502,None)],
                    terminator:Terminator::Goto(vec![3])},
                BasicBlock{statements:vec![Statement::ValuePhi{
                    ty:ty.clone(),predecessors:vec![1,2],generation:Some(SymbolId(600)),
                    check:Event{op:Access::Read,path:p(601),loan:None,
                        parent:None,token:3},provenance:None,
                    alternatives:vec![
                        RefOption{loan:SymbolId(501),path:a,exclusive:true,parent:None},
                        RefOption{loan:SymbolId(502),path:b,exclusive:true,parent:None},
                    ],
                }],terminator:Terminator::Goto(vec![4])},
                BasicBlock{statements:vec![],terminator:Terminator::Return},
            ]};
        let origins=[VerifiedReturnedReference{parameter:0,fields:vec![],ty:ty.clone()},
            VerifiedReturnedReference{parameter:1,fields:vec![],ty}];
        assert!(m.verify().unwrap().is_empty());
        let cases=m.solve_path_cases(TOKENS,&[
            ("a".into(),ConstType::Named("Blob".into())),
            ("b".into(),ConstType::Named("Blob".into())),
        ],&origins).expect("cleanup must preserve the chosen return loan");
        assert_eq!(cases.len(),2);
        assert!(cases.iter().any(|case|case.returned==Some(0)));
        assert!(cases.iter().any(|case|case.returned==Some(1)));
    }
}

#[cfg(test)]
mod borrow_architecture_validation_0691_tests {
    use super::*;
    const TOKENS: usize = 100;
    fn root(id:u32)->Path {Path::root(SymbolId(id))}
    fn field(id:u32,n:u32)->Path {
        root(id).child(FieldKey{aggregate:TypeId(0),field:FieldId(n)})
    }
    fn ev(op:Access,path:Path,loan:Option<u32>,parent:Option<u32>)->Statement {
        Statement::Access(Event{op,path,loan:loan.map(SymbolId),
            parent:parent.map(SymbolId),token:0})
    }
    fn body(stmts:Vec<Statement>,loans:Vec<(u32,Path)>)->FunctionMir {
        FunctionMir{entry:0,loans:loans.into_iter().map(|(id,path)|
            (SymbolId(id),path)).collect(),blocks:vec![
            BasicBlock{statements:stmts,terminator:Terminator::Goto(vec![1])},
            BasicBlock{statements:vec![],terminator:Terminator::Return},
        ]}
    }
    fn solve(m:&FunctionMir)->Option<Vec<VerifiedPathCase>> {
        m.solve_path_cases(TOKENS,&[
            ("p".into(),ConstType::Named("Pair".into())),
            ("q".into(),ConstType::Named("Pair".into())),
        ],&[])
    }
    fn rejected(m:&FunctionMir)->bool {
        m.verify().map_or(true,|conflicts|!conflicts.is_empty())
    }
    #[test]
    fn owner_write_before_later_shared_read_is_rejected_by_both_analyzers() {
        let p=root(101);
        let m=body(vec![
            ev(Access::BorrowShared,p.clone(),Some(501),None),
            ev(Access::Write,p.clone(),None,None),
            ev(Access::Read,p.clone(),Some(501),None),
        ],vec![(501,p)]);
        assert!(rejected(&m),"CFG verifier must reject direct owner write");
        assert!(solve(&m).is_none(),"path-case must not certify an owner-write conflict");
    }
    #[test]
    fn owner_write_before_later_mutable_read_is_rejected_by_both_analyzers() {
        let p=root(101);
        let m=body(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None),
            ev(Access::Write,p.clone(),None,None),
            ev(Access::Read,p.clone(),Some(501),None),
        ],vec![(501,p)]);
        assert!(rejected(&m));
        assert!(solve(&m).is_none());
    }
    #[test]
    fn disjoint_owner_field_write_preserves_both_analyzers() {
        let borrowed=field(101,0);
        let free=field(101,1);
        let m=body(vec![
            ev(Access::BorrowShared,borrowed.clone(),Some(501),None),
            ev(Access::Write,free,None,None),
            ev(Access::Read,borrowed.clone(),Some(501),None),
        ],vec![(501,borrowed)]);
        assert!(m.verify().unwrap().is_empty());
        assert!(solve(&m).is_some());
    }
    #[test]
    fn independent_owner_write_preserves_both_analyzers() {
        let borrowed=root(101);
        let other=root(102);
        let m=body(vec![
            ev(Access::BorrowShared,borrowed.clone(),Some(501),None),
            ev(Access::Write,other,None,None),
            ev(Access::Read,borrowed.clone(),Some(501),None),
        ],vec![(501,borrowed)]);
        assert!(m.verify().unwrap().is_empty());
        assert!(solve(&m).is_some());
    }
    #[test]
    fn unknown_loan_end_cannot_publish_a_case_certificate() {
        let p=root(101);
        let m=body(vec![
            ev(Access::BorrowShared,p.clone(),Some(501),None),
            ev(Access::EndLoan,p.clone(),Some(999),None),
            ev(Access::Move,p.clone(),None,None),
        ],vec![(501,p)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn mismatched_endloan_path_cannot_publish_a_case_certificate() {
        let p=root(101);
        let m=body(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None),
            ev(Access::EndLoan,root(102),Some(501),None),
            ev(Access::Move,p.clone(),None,None),
        ],vec![(501,p)]);
        assert!(solve(&m).is_none());
    }
    #[test]
    fn premature_parent_end_before_child_use_fails_closed() {
        let p=root(101);
        let m=body(vec![
            ev(Access::BorrowMut,p.clone(),Some(501),None),
            ev(Access::BorrowMut,p.clone(),Some(502),Some(501)),
            ev(Access::EndLoan,p.clone(),Some(501),None),
            ev(Access::Read,p.clone(),Some(502),None),
        ],vec![(501,p.clone()),(502,p)]);
        assert!(rejected(&m));
        assert!(solve(&m).is_none());
    }
    #[test]
    fn bad_cfg_target_cannot_publish_a_case_certificate() {
        let m=FunctionMir{entry:0,loans:HashMap::new(),blocks:vec![
            BasicBlock{statements:Vec::new(),terminator:Terminator::Goto(vec![99])},
        ]};
        assert!(solve(&m).is_none());
    }
}
