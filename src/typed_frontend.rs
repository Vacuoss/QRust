//Opt-in typed Rust host surface
use std::collections::{HashMap, HashSet};
use std::{rc::Rc, cell::RefCell, ops::Range, borrow::Cow};
use crate::{cfg_nll::{FlowPlan,PlaceAccessKind,TypedPlace}, ids::SymbolId, region_infer::{RegionSignature,ProvenanceVariables,RegionConstraintSolver}, ir::{ConstType, ConstValue, TypeId, FieldId, VariantId, Place, RefSlot, RefLease, RefValue, ReturnOriginGuard}, syntax::{self, Token, TokenKind as K, Diagnostic, Position, Expr, Stmt}};

fn reference_if_tail_arms(tokens:&[Token<'_>],range:Range<usize>)
    ->Option<Vec<(Option<usize>,Range<usize>)>>{
    let mut i=range.start;
    let mut arms=Vec::new();
    let mut has_else=false;
    loop {
        if tokens.get(i)?.kind!=K::Ident("if"){return None;}
        i+=1;
        let cond=i;
        let mut parentheses=0usize;
        while i<range.end {
            match tokens[i].kind {
                K::LParen=>parentheses+=1,
                K::RParen=>parentheses=parentheses.checked_sub(1)?,
                K::LBrace if parentheses==0=>break,
                K::Semi|K::RBrace if parentheses==0=>return None,
                _=>(),
            }
            i+=1;
        }
        if i!=cond+1 || i>=range.end ||
            !matches!(tokens[cond].kind,K::Ident(_)) {return None;}
        let open=i;
        i+=1;
        let mut depth=1usize;
        while i<range.end && depth>0 {
            match tokens[i].kind {
                K::LBrace=>depth+=1,
                K::RBrace=>depth-=1,
                _=>(),
            }
            if depth>0{i+=1;}
        }
        if depth!=0{return None;}
        let arm=open+1..i;
        if arm.is_empty() || tokens[arm.clone()].iter().any(|t|t.kind==K::Semi){return None;}
        arms.push((Some(cond),arm));
        i+=1;
        if tokens.get(i).is_none_or(|t|t.kind!=K::Ident("else")){break;}
        i+=1;
        if tokens.get(i)?.kind==K::Ident("if") {continue;}
        if tokens.get(i)?.kind!=K::LBrace{return None;}
        let open=i;
        i+=1;
        let mut depth=1usize;
        while i<range.end && depth>0 {
            match tokens[i].kind {
                K::LBrace=>depth+=1,
                K::RBrace=>depth-=1,
                _=>(),
            }
            if depth>0{i+=1;}
        }
        if depth!=0{return None;}
        let arm=open+1..i;
        if arm.is_empty() || tokens[arm.clone()].iter().any(|t|t.kind==K::Semi){return None;}
        arms.push((None,arm));
        has_else=true;
        i+=1;
        break;
    }
    if has_else && i==range.end {Some(arms)}else{None}
}


fn reference_match_tail_arms(tokens:&[Token<'_>],range:Range<usize>)
    ->Option<Vec<(Option<bool>,Range<usize>)>>{
    let mut i=range.start;
    if tokens.get(i)?.kind!=K::Ident("match"){return None;}
    i+=1;
    if !matches!(tokens.get(i)?.kind,K::Ident(_)) {return None;}
    i+=1;
    if tokens.get(i)?.kind!=K::LBrace{return None;}
    i+=1;
    let mut arms=Vec::new();
    let (mut seen_true,mut seen_false,mut seen_wildcard)=(false,false,false);
    while i<range.end && tokens[i].kind!=K::RBrace {
        let pattern=match tokens[i].kind {
            K::Ident("true") if !seen_true && !seen_wildcard=>{
                seen_true=true;Some(true)
            },
            K::Ident("false") if !seen_false && !seen_wildcard=>{
                seen_false=true;Some(false)
            },
            K::Ident("_") if !seen_wildcard=>{seen_wildcard=true;None},
            _=>return None,
        };
        i+=1;
        if tokens.get(i)?.kind!=K::FatArrow{return None;}
        i+=1;
        if tokens.get(i)?.kind!=K::LBrace{return None;}
        i+=1;
        let begin=i;
        let mut depth=1usize;
        while i<range.end && depth>0 {
            match tokens[i].kind {
                K::LBrace=>depth+=1,
                K::RBrace=>depth-=1,
                _=>(),
            }
            if depth>0{i+=1;}
        }
        if depth!=0 || begin==i || tokens[begin..i].iter().any(|t|t.kind==K::Semi){return None;}
        arms.push((pattern,begin..i));
        i+=1;
        if tokens.get(i).is_some_and(|t|t.kind==K::Comma){i+=1;}
    }
    if tokens.get(i)?.kind!=K::RBrace || i+1!=range.end ||
        !(seen_wildcard || (seen_true && seen_false)) || arms.is_empty() {
        return None;
    }
    Some(arms)
}

fn err(at: Position, msg: impl Into<String>) -> Diagnostic { Diagnostic { at, message: msg.into() } }
fn at(tokens: &[Token<'_>], i: usize) -> Position {
    tokens.get(i).or_else(||tokens.last()).map(|t|t.at).unwrap_or(Position { line: 1, column: 1 })
}
//These are only the built-in, compiler-verified host trait bounds User-defined traits and dynamic
//dispatch must not be silently accepted
#[derive(Clone)]
struct GenericParameter { name: String, bounds: Vec<String> }
#[derive(Clone)]
struct Function { name: String, params: Vec<(String, ConstType)>, ret: Option<ConstType>,
    generics: Vec<GenericParameter>, regions: Option<RegionSignature>, body: Range<usize> }

fn transparent_reference_chain(functions:&[Rc<Function>],tokens:&[Token<'_>],
    name:&str,remaining:usize)->bool{
    if remaining==0{return false;}
    let Some(fun)=functions.iter().find(|fun|fun.name==name)else{return false;};
    if fun.params.len()!=1 || fun.ret.as_ref()!=Some(&fun.params[0].1) ||
        !matches!(&fun.params[0].1,ConstType::Ref(_)|ConstType::RefMut(_)) {
        return false;
    }
    if !fun.regions.as_ref().is_some_and(|regions|matches!(
        (regions.param.first(),regions.result),
        (Some(Some(source)),Some(target)) if regions.permits(*source,target))) {
        return false;
    }
    let body=&tokens[fun.body.clone()];
    if body.len()==1 {
        return matches!(body[0].kind,K::Ident(arg) if arg==fun.params[0].0);
    }
    //A reborrow has the *same underlying owner* as its reference parameter, but creates a child loan
    if body.len()==3 {
        if let (K::Amp,K::Star,K::Ident(arg))=
            (body[0].kind,body[1].kind,body[2].kind) {
            return arg==fun.params[0].0 &&
                matches!(&fun.params[0].1,ConstType::Ref(_));
        }
    }
    if body.len()==4 {
        if let (K::Amp,K::Ident("mut"),K::Star,K::Ident(arg))=
            (body[0].kind,body[1].kind,body[2].kind,body[3].kind) {
            return arg==fun.params[0].0 &&
                matches!(&fun.params[0].1,ConstType::RefMut(_));
        }
        if let (K::Ident(next),K::LParen,K::Ident(arg),K::RParen)=
            (body[0].kind,body[1].kind,body[2].kind,body[3].kind) {
            return arg==fun.params[0].0 &&
                transparent_reference_chain(functions,tokens,next,remaining-1);
        }
    }
    false
}


#[derive(Clone,Copy)]
struct ReferenceAlias<'src> {name:&'src str,origin:usize,exclusive:bool}
struct ReferenceAliases<'src> {
    bindings:Vec<ReferenceAlias<'src>>,
    moved:HashSet<&'src str>,
}
impl<'src> ReferenceAliases<'src> {
    fn origin(&self,fun:&Function,name:&str)->Option<(usize,bool)> {
        if self.moved.contains(name) {return None;}
        fun.params.iter().enumerate().find_map(|(index,(formal,ty))|{
            if formal!=name {return None;}
            match ty {
                ConstType::Ref(_)=>Some((index,false)),
                ConstType::RefMut(_)=>Some((index,true)),
                _=>None,
            }
        }).or_else(||self.bindings.iter().find(|alias|alias.name==name)
            .map(|alias|(alias.origin,alias.exclusive)))
    }
    fn index(&self,fun:&Function,name:&str)->Option<usize>{
        self.origin(fun,name).map(|(index,_)|index)
    }
}
fn reference_aliases<'src>(tokens:&[Token<'src>],fun:&Function)
    ->Option<(ReferenceAliases<'src>,Range<usize>)>{
    let mut i=fun.body.start;
    let mut aliases=ReferenceAliases{bindings:Vec::new(),moved:HashSet::new()};
    while i<fun.body.end && tokens.get(i)?.kind==K::Ident("let") {
        if aliases.bindings.len()>=16 || i+5>fun.body.end{return None;}
        let (K::Ident(alias),K::Equal,K::Ident(source),K::Semi)=(
            tokens.get(i+1)?.kind,tokens.get(i+2)?.kind,
            tokens.get(i+3)?.kind,tokens.get(i+4)?.kind) else{return None;};
        if fun.params.iter().any(|(name,_)|name==alias) ||
            aliases.bindings.iter().any(|entry|entry.name==alias) {return None;}
        let (origin,exclusive)=aliases.origin(fun,source)?;
        if exclusive {aliases.moved.insert(source);}
        aliases.bindings.push(ReferenceAlias{name:alias,origin,exclusive});
        i+=5;
    }
    if i>=fun.body.end{return None;}
    Some((aliases,i..fun.body.end))
}
fn has_mutable_alias_prefix(tokens:&[Token<'_>],fun:&Function)->bool {
    let mut i=fun.body.start;
    while i+4<fun.body.end && tokens[i].kind==K::Ident("let") {
        let (K::Ident(_),K::Equal,K::Ident(source),K::Semi)=(
            tokens[i+1].kind,tokens[i+2].kind,tokens[i+3].kind,tokens[i+4].kind)
            else{break;};
        if fun.params.iter().any(|(name,ty)|name==source &&
            matches!(ty,ConstType::RefMut(_))) {return true;}
        i+=5;
    }
    false
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ReferencePathOrigin {
    parameter: usize,
    path: Vec<crate::cfg_borrow::FieldKey>,
}

fn checked_reference_projection(input:&ConstType, names:&[&str],
    types:&HashMap<String,Vec<(String,ConstType)>>,
    type_ids:&HashMap<String,TypeId>,type_names:&[String])
    ->Option<(Vec<crate::cfg_borrow::FieldKey>,ConstType,bool)>{
    let (mut ty,exclusive)=match input {
        ConstType::Ref(inner)=>(*inner.clone(),false),
        ConstType::RefMut(inner)=>(*inner.clone(),true),
        _=>return None,
    };
    if names.is_empty() || names.len()>16{return None;}
    let mut path=Vec::with_capacity(names.len());
    for field_name in names {
        let (name,id)=match &ty {
            ConstType::Named(name)=>(name.as_str(),*type_ids.get(name)?),
            ConstType::Resolved(id)=>(type_names.get(id.0 as usize)?.as_str(),*id),
            _=>return None,
        };
        let (index,(_,field_type))=types.get(name)?.iter().enumerate()
            .find(|(_, (field,_))|field.as_str()==*field_name)?;
        path.push(crate::cfg_borrow::FieldKey{
            aggregate:id,field:FieldId(u32::try_from(index).ok()?),
        });
        ty=field_type.clone();
    }
    Some((path,ty,exclusive))
}
fn same_projected_type(left:&ConstType,right:&ConstType,
    type_ids:&HashMap<String,TypeId>)->bool {
    if left==right{return true;}
    match (left,right) {
        (ConstType::Named(name),ConstType::Resolved(id))|
        (ConstType::Resolved(id),ConstType::Named(name))=>type_ids.get(name)==Some(id),
        _=>false,
    }
}

fn effectful_return_field_origin(solver:&mut ReferenceSummarySolver<'_,'_>,
    fun:&Function)->Option<crate::typed_mir::VerifiedReturnedReference>{
    if !fun.generics.is_empty(){return None;}
    let tokens=solver.tokens;
    let mut tail_end=fun.body.end;
    if tail_end<=fun.body.start{return None;}
    if tokens.get(tail_end-1)?.kind==K::Semi {tail_end-=1;}
    let tail_start=(fun.body.start..tail_end).rev()
        .find(|&at|tokens[at].kind==K::Semi)?+1;
    if tail_start<=fun.body.start || tail_start>=fun.body.end{return None;}
    let mut cursor=fun.body.start;
    while cursor<tail_start {
        let K::Ident(root)=tokens.get(cursor)?.kind else{return None;};
        let index=fun.params.iter().position(|(name,ty)|
            name==root && matches!(ty,ConstType::RefMut(_)))?;
        cursor+=1;
        let mut fields=Vec::new();
        while tokens.get(cursor).is_some_and(|t|t.kind==K::Dot) {
            let K::Ident(field)=tokens.get(cursor+1)?.kind else{return None;};
            fields.push(field);
            cursor+=2;
        }
        if fields.is_empty() || tokens.get(cursor)?.kind!=K::Equal {return None;}
        cursor+=1;
        match tokens.get(cursor)?.kind {
            K::Number(_)|K::Ident("true"|"false")=>cursor+=1,
            _=>return None,
        }
        if tokens.get(cursor)?.kind!=K::Semi{return None;}
        cursor+=1;
        if index>=64{return None;}
    }
    if cursor!=tail_start{return None;}
    let aliases=ReferenceAliases{bindings:Vec::new(),moved:HashSet::new()};
    let tail=tail_start..fun.body.end;
    let mask=reference_expression_origins(solver,fun,&aliases,tail.clone())?;
    let paths=reference_expression_paths(solver,fun,&aliases,tail)?;
    let [origin]=paths.as_slice() else{return None;};
    if mask!=1u64.checked_shl(origin.parameter as u32)? {return None;}
    let region=fun.regions.as_ref()?;
    let source=region.param.get(origin.parameter).copied().flatten()?;
    let target=region.result?;
    if !region.permits(source,target){return None;}
    let ty=fun.ret.as_ref()?.clone();
    Some(crate::typed_mir::VerifiedReturnedReference{
        parameter:origin.parameter,fields:origin.path.clone(),ty,
    })
}

fn checked_forwarding_prefix(tokens:&[Token<'_>],fun:&Function,
    start:usize,end:usize)->bool {
    fn closing(tokens:&[Token<'_>],at:usize,end:usize)->Option<usize>{
        if tokens.get(at)?.kind!=K::LBrace{return None;}
        let mut depth=0usize;
        for i in at..end {match tokens[i].kind {
            K::LBrace=>depth+=1,
            K::RBrace=>{
                depth=depth.checked_sub(1)?;
                if depth==0{return Some(i);}
            },
            _=>(),
        }}
        None
    }
    fn conditional(tokens:&[Token<'_>],fun:&Function,
        at:usize,end:usize,depth:usize)->Option<usize>{
        if depth>32 || tokens.get(at)?.kind!=K::Ident("if"){return None;}
        let mut parens=0usize;
        let mut brace=None;
        for i in at+1..end {match tokens[i].kind {
            K::LParen=>parens+=1,
            K::RParen=>parens=parens.checked_sub(1)?,
            K::LBrace if parens==0=>{brace=Some(i);break;},
            K::Semi|K::RBrace if parens==0=>return None,
            _=>(),
        }}
        let brace=brace?;
        if brace==at+1 || parens!=0{return None;}
        let last=closing(tokens,brace,end)?;
        if !prefix(tokens,fun,brace+1,last,depth+1){return None;}
        let mut next=last+1;
        if next<end && tokens[next].kind==K::Ident("else") {
            next+=1;
            match tokens.get(next)?.kind {
                K::Ident("if")=>return conditional(tokens,fun,next,end,depth+1),
                K::LBrace=>{
                    let last=closing(tokens,next,end)?;
                    if !prefix(tokens,fun,next+1,last,depth+1){return None;}
                    next=last+1;
                },
                _=>return None,
            }
        }
        Some(next)
    }
    fn prefix(tokens:&[Token<'_>],fun:&Function,
        start:usize,end:usize,depth:usize)->bool {
        if depth>32{return false;}
        let mut cursor=start;
        while cursor<end {
            if tokens[cursor].kind==K::Ident("if") {
                let Some(next)=conditional(tokens,fun,cursor,end,depth+1)else{return false;};
                cursor=next;continue;
            }
            if tokens[cursor].kind==K::LBrace {
                let Some(last)=closing(tokens,cursor,end)else{return false;};
                if !prefix(tokens,fun,cursor+1,last,depth+1){return false;}
                cursor=last+1;continue;
            }
            let Some(semi)=(cursor..end).find(|&i|tokens[i].kind==K::Semi)else{return false};
            if semi==cursor{return false;}
            let K::Ident(name)=tokens[cursor].kind else{return false};
            if tokens.get(cursor+1).is_some_and(|t|t.kind==K::LParen) {
                let mut parens=0usize;
                for i in cursor+1..semi {match tokens[i].kind {
                    K::LParen=>parens+=1,
                    K::RParen=>{
                        let Some(next)=parens.checked_sub(1)else{return false};
                        parens=next;
                        if parens==0 && i!=semi-1{return false;}
                    },
                    K::LBrace|K::RBrace|K::Semi=>return false,
                    _=>(),
                }}
                if parens!=0{return false;}
            }else{
                let Some((_,ty))=fun.params.iter().find(|(formal,_)|formal==name)
                    else{return false;};
                if !matches!(ty,ConstType::RefMut(_)){return false;}
                let mut i=cursor+1;
                let mut fields=Vec::new();
                while i+1<semi && tokens[i].kind==K::Dot {
                    let K::Ident(field)=tokens[i+1].kind else{return false};
                    fields.push(field);i+=2;
                }
                if fields.is_empty() || i+2!=semi || tokens[i].kind!=K::Equal ||
                    !matches!(tokens[i+1].kind,K::Number(_)|K::Ident("true"|"false")){
                    return false;
                }
            }
            cursor=semi+1;
        }
        cursor==end
    }
    prefix(tokens,fun,start,end,0)
}

fn forwarded_return_field_origin(tokens:&[Token<'_>],fun:&Function,
    callee_name:&str,callee:&Function,
    origin:&crate::typed_mir::VerifiedReturnedReference)
    ->Option<crate::typed_mir::VerifiedReturnedReference>{
    if !fun.generics.is_empty() || !callee.generics.is_empty() || fun.ret!=callee.ret {
        return None;
    }
    let mut end=fun.body.end;
    if tokens.get(end-1)?.kind==K::Semi {end-=1;}
    if end<=fun.body.start || tokens.get(end-1)?.kind!=K::RParen{return None;}
    let mut nesting=0usize;
    let mut open=None;
    for i in (fun.body.start..end).rev(){match tokens[i].kind {
        K::RParen=>nesting+=1,
        K::LParen=>{
            nesting=nesting.checked_sub(1)?;
            if nesting==0{open=Some(i);break;}
        },
        _=>(),
    }}
    let paren=open?;
    if paren<=fun.body.start || tokens.get(paren-1)?.kind!=K::Ident(callee_name){
        return None;
    }
    let start=paren-1;
    let prefix_end=if start>fun.body.start && tokens[start-1].kind==K::Ident("return"){
        start-1
    }else{start};
    if !checked_forwarding_prefix(tokens,fun,fun.body.start,prefix_end){return None;}
    let mut actuals=Vec::new();
    let mut index=paren+1;
    while index<end-1 {
        let K::Ident(name)=tokens.get(index)?.kind else{return None;};
        let actual=fun.params.iter().position(|(candidate,_)|candidate==name)?;
        if callee.params.get(actuals.len())?.1!=fun.params[actual].1{return None;}
        if matches!(&fun.params[actual].1,ConstType::RefMut(_)) &&
            actuals.contains(&actual){return None;}
        actuals.push(actual);
        index+=1;
        if index<end-1 {
            if tokens.get(index)?.kind!=K::Comma{return None;}
            index+=1;
        }
    }
    if actuals.len()!=callee.params.len(){return None;}
    let parameter=*actuals.get(origin.parameter)?;
    let region=fun.regions.as_ref()?;
    let source=region.param.get(parameter).copied().flatten()?;
    if !region.permits(source,region.result?){return None;}
    Some(crate::typed_mir::VerifiedReturnedReference{
        parameter,fields:origin.fields.clone(),ty:origin.ty.clone(),
    })
}

struct ReferenceSummarySolver<'defs,'src> {
    functions:&'defs [Rc<Function>],
    tokens:&'defs [Token<'src>],
    resolved:HashMap<String,Option<u64>>,
    path_resolved:HashMap<String,Vec<ReferencePathOrigin>>,
    types:&'defs HashMap<String,Vec<(String,ConstType)>>,
    type_ids:&'defs HashMap<String,TypeId>,
    type_names:&'defs [String],
    visiting:HashSet<String>,
}
impl<'defs,'src> ReferenceSummarySolver<'defs,'src> {
    fn new(functions:&'defs [Rc<Function>],tokens:&'defs [Token<'src>],
        types:&'defs HashMap<String,Vec<(String,ConstType)>>,
        type_ids:&'defs HashMap<String,TypeId>,type_names:&'defs [String])->Self{
        Self{functions,tokens,resolved:HashMap::new(),path_resolved:HashMap::new(),
            types,type_ids,type_names,visiting:HashSet::new()}
    }
    fn projected(&mut self,name:&str)->Option<&[ReferencePathOrigin]> {
        self.prove(name)?;
        self.path_resolved.get(name).map(Vec::as_slice)
    }
    fn projection(&self,input:&ConstType,names:&[&str])
        ->Option<(Vec<crate::cfg_borrow::FieldKey>,ConstType,bool)>{
        checked_reference_projection(input,names,self.types,self.type_ids,self.type_names)
    }
    fn prove(&mut self,name:&str)->Option<u64>{
        if let Some(&cached)=self.resolved.get(name){return cached;}
        //128 acyclic helper calls are more than the host runtime's bounded depth. Cycles and deeper graphs fail
        //closed without stack overflow
        if self.visiting.len()>=128 || !self.visiting.insert(name.to_owned()){
            return None;
        }
        let result=self.prove_function(name);
        self.visiting.remove(name);
        self.resolved.insert(name.to_owned(),result);
        result
    }
    fn prove_function(&mut self,name:&str)->Option<u64>{
        let fun=Rc::clone(self.functions.iter().find(|f|f.name==name)?);
        if fun.params.len()>64 || !fun.generics.is_empty() ||
            !matches!(fun.ret.as_ref(),Some(ConstType::Ref(_)|ConstType::RefMut(_))) {
            return None;
        }
        let tokens=self.tokens;
        let (aliases,tail)=reference_aliases(tokens,&fun)?;
        let mask=reference_expression_origins(self,&fun,&aliases,tail.clone())?;
        if mask==0{return None;}
        //This second proof retains the precise field projections through pure branches and calls
        if let Some(mut paths)=reference_expression_paths(self,&fun,&aliases,tail) {
            paths.sort_by(|a,b|a.parameter.cmp(&b.parameter)
                .then_with(||a.path.len().cmp(&b.path.len()))
                .then_with(||a.path.iter().map(|key|(key.aggregate.0,key.field.0))
                    .cmp(b.path.iter().map(|key|(key.aggregate.0,key.field.0)))));
            paths.dedup();
            let path_mask=paths.iter().fold(0u64,|bits,origin|bits|(1u64<<origin.parameter));
            if path_mask!=mask{return None;}
            self.path_resolved.insert(name.to_owned(),paths);
        }
        //Each summary is checked against the function's own outlives bounds, not just against the lifetime
        //contract of whichever caller uses it
        let signature=fun.regions.as_ref()?;
        let mut actual=[0u64;64];
        for (i,source) in actual[..fun.params.len()].iter_mut().enumerate(){
            if matches!(fun.params[i].1,ConstType::Ref(_)|ConstType::RefMut(_)) {
                *source=1u64<<i;
            }
        }
        let mut solver=RegionConstraintSolver::new(signature);
        let result=solver.instantiate_call_sources(mask,&actual[..fun.params.len()]).ok()?;
        solver.solve_and_verify_return(result).ok()?;
        Some(mask)
    }
}

fn pure_reference_condition(tokens:&[Token<'_>],fun:&Function,at:usize)->bool{
    match tokens.get(at).map(|token|token.kind){
        Some(K::Ident("true"|"false"))=>true,
        Some(K::Ident(value))=>fun.params.iter().any(|(name,ty)|
            name==value && *ty==ConstType::Bool),
        _=>false,
    }
}

fn reference_expression_origins(solver:&mut ReferenceSummarySolver<'_,'_>,
    fun:&Function,aliases:&ReferenceAliases<'_>,range:Range<usize>)->Option<u64>{
    if range.is_empty(){return None;}
    let tokens=solver.tokens;
    let first=tokens.get(range.start)?.kind;
    //A terminal explicit `return value;` has the same provenance as a tail `value`, but only when the
    //return is the WHOLE remaining expression
    if first==K::Ident("return") && range.end>=range.start+3 &&
        tokens.get(range.end-1)?.kind==K::Semi {
        return reference_expression_origins(solver,fun,aliases,
            range.start+1..range.end-1);
    }
    if first==K::Ident("if") {
        let arms=reference_if_tail_arms(tokens,range.clone())?;
        let mut mask=0;
        for (condition,arm) in arms {
            if let Some(condition)=condition {
                if !pure_reference_condition(tokens,fun,condition){return None;}
            }
            mask|=reference_expression_origins(solver,fun,aliases,arm)?;
        }
        return Some(mask);
    }
    if first==K::Ident("match") {
        let subject=match tokens.get(range.start+1)?.kind {
            K::Ident("true"|"false")=>true,
            K::Ident(value)=>fun.params.iter().any(|(name,ty)|
                name==value && *ty==ConstType::Bool),
            _=>false,
        };
        if !subject{return None;}
        let arms=reference_match_tail_arms(tokens,range)?;
        let mut mask=0;
        for (_,arm) in arms {
            mask |= reference_expression_origins(solver,fun,aliases,arm)?;
        }
        return Some(mask);
    }
    let reference_param=|name:&str|aliases.index(fun,name);
    if range.end==range.start+1 {
        if let K::Ident(name)=first {
            let index=reference_param(name)?;
            if Some(&fun.params[index].1)==fun.ret.as_ref() {return Some(1u64<<index);}
        }
        return None;
    }
    if first==K::Amp {
        let mut i=range.start+1;
        let exclusive=tokens.get(i)?.kind==K::Ident("mut");
        if exclusive{i+=1;}
        if let K::Ident(name)=tokens.get(i)?.kind {
            let index=reference_param(name)?;
            i+=1;
            let mut names=Vec::new();
            while i+1<range.end && tokens[i].kind==K::Dot {
                let K::Ident(field)=tokens[i+1].kind else{return None;};
                names.push(field);i+=2;
            }
            if i==range.end && !names.is_empty(){
                let (_path,field_ty,source_mut)=solver.projection(&fun.params[index].1,&names)?;
                if exclusive && !source_mut{return None;}
                let output=fun.ret.as_ref()?;
                let target=match output {
                    ConstType::Ref(inner) if !exclusive=>inner.as_ref(),
                    ConstType::RefMut(inner) if exclusive=>inner.as_ref(),
                    _=>return None,
                };
                if !same_projected_type(&field_ty,target,solver.type_ids){return None;}
                return Some(1u64<<index);
            }
        }
    }
    let borrow=match tokens.get(range.start)?.kind {
        K::Amp=>true,_=>false,
    };
    if borrow {
        let (exclusive,star,name)=match tokens.get(range.start+1)?.kind {
            K::Star if range.end==range.start+3=>(false,range.start+1,range.start+2),
            K::Ident("mut") if range.end==range.start+4 &&
                tokens.get(range.start+2)?.kind==K::Star =>
                (true,range.start+2,range.start+3),
            _=>return None,
        };
        if tokens.get(star)?.kind!=K::Star{return None;}
        let K::Ident(name)=tokens.get(name)?.kind else{return None;};
        let index=reference_param(name)?;
        let input=&fun.params[index].1;
        let output=fun.ret.as_ref()?;
        let pointee=match input {
            ConstType::Ref(ty)|ConstType::RefMut(ty)=>ty.as_ref(),_=>return None,
        };
        let allowed=if exclusive {
            matches!(input,ConstType::RefMut(_)) &&
                matches!(output,ConstType::RefMut(ty) if ty.as_ref()==pointee)
        }else{
            matches!(output,ConstType::Ref(ty) if ty.as_ref()==pointee)
        };
        return if allowed{Some(1u64<<index)}else{None};
    }
    let K::Ident(callee_name)=first else{return None;};
    if tokens.get(range.start+1)?.kind!=K::LParen ||
        tokens.get(range.end-1)?.kind!=K::RParen {return None;}
    let callee=Rc::clone(solver.functions.iter().find(|f|f.name==callee_name)?);
    if callee.ret!=fun.ret || callee.params.len()>64{return None;}
    let mut actual=Vec::with_capacity(callee.params.len());
    let mut exclusive_sources=0u64;
    let mut i=range.start+2;
    while i<range.end-1 {
        let K::Ident(name)=tokens.get(i)?.kind else{return None;};
        let param=fun.params.iter().position(|(formal,_)|formal==name)
            .filter(|_|!aliases.moved.contains(name))
            .or_else(||aliases.index(fun,name))?;
        if callee.params.get(actual.len())?.1!=fun.params[param].1{return None;}
        //Passing one &mut binding twice in the same call would create simultaneous exclusive reborrows;
        //matching parameter types alone must never certify that call
        if matches!(&fun.params[param].1,ConstType::RefMut(_)) {
            let bit=1u64.checked_shl(u32::try_from(param).ok()?)?;
            if exclusive_sources & bit != 0 {return None;}
            exclusive_sources |= bit;
        }
        actual.push(param);
        i+=1;
        if i<range.end-1 {
            if tokens.get(i)?.kind!=K::Comma{return None;}
            i+=1;
        }
    }
    if actual.len()!=callee.params.len(){return None;}
    let callee_sources=solver.prove(callee_name)?;
    let mut masks=[0u64;64];
    for (slot,&caller) in masks.iter_mut().zip(actual.iter()) {
        *slot=1u64.checked_shl(u32::try_from(caller).ok()?)?;
    }
    let mut constraints=ProvenanceVariables::new();
    let result=constraints.instantiate_call_sources(callee_sources,&masks[..actual.len()]).ok()?;
    constraints.solve().ok()?;
    constraints.origins(result)
}

//Companion to the lifetime may-origin graph: exact projected paths for pure reference-return
//expressions
fn reference_expression_paths(solver:&mut ReferenceSummarySolver<'_,'_>,
    fun:&Function,aliases:&ReferenceAliases<'_>,range:Range<usize>)
    ->Option<Vec<ReferencePathOrigin>>{
    if range.is_empty(){return None;}
    let tokens=solver.tokens;
    let first=tokens.get(range.start)?.kind;
    if first==K::Ident("return") && range.end>=range.start+3 &&
        tokens.get(range.end-1)?.kind==K::Semi {
        return reference_expression_paths(solver,fun,aliases,range.start+1..range.end-1);
    }
    if first==K::Ident("if") {
        let arms=reference_if_tail_arms(tokens,range)?;
        let mut result=Vec::new();
        for (condition,arm) in arms {
            if condition.is_some_and(|i|!pure_reference_condition(tokens,fun,i)){return None;}
            result.extend(reference_expression_paths(solver,fun,aliases,arm)?);
            if result.len()>256{return None;}
        }
        return Some(result);
    }
    if first==K::Ident("match") {
        let arms=reference_match_tail_arms(tokens,range)?;
        let mut result=Vec::new();
        for (_,arm) in arms {
            result.extend(reference_expression_paths(solver,fun,aliases,arm)?);
            if result.len()>256{return None;}
        }
        return Some(result);
    }
    let origin=|name:&str|aliases.index(fun,name);
    if range.end==range.start+1 {
        let K::Ident(name)=first else{return None;};
        return Some(vec![ReferencePathOrigin{parameter:origin(name)?,path:Vec::new()}]);
    }
    if first==K::Amp {
        let mut i=range.start+1;
        if tokens.get(i)?.kind==K::Ident("mut"){i+=1;}
        if tokens.get(i)?.kind==K::Star && i+2==range.end {
            let K::Ident(name)=tokens.get(i+1)?.kind else{return None;};
            return Some(vec![ReferencePathOrigin{parameter:origin(name)?,path:Vec::new()}]);
        }
        let K::Ident(name)=tokens.get(i)?.kind else{return None;};
        let index=origin(name)?;
        i+=1;
        let mut fields=Vec::new();
        while i+1<range.end && tokens[i].kind==K::Dot {
            let K::Ident(field)=tokens[i+1].kind else{return None;};
            fields.push(field);i+=2;
        }
        if i!=range.end || fields.is_empty(){return None;}
        let (path,_,_)=solver.projection(&fun.params[index].1,&fields)?;
        return Some(vec![ReferencePathOrigin{parameter:index,path}]);
    }
    let K::Ident(callee_name)=first else{return None;};
    if tokens.get(range.start+1)?.kind!=K::LParen ||
        tokens.get(range.end-1)?.kind!=K::RParen{return None;}
    //First prove the callee's complete outlives mask, then obtain its exact path alternatives
    let callee=Rc::clone(solver.functions.iter().find(|f|f.name==callee_name)?);
    let callee_paths=solver.projected(callee_name)?.to_vec();
    let mut actuals=Vec::new();
    let mut i=range.start+2;
    while i<range.end-1 {
        let K::Ident(name)=tokens.get(i)?.kind else{return None;};
        //Boolean selector parameters carry no reference origin, but must still be checked as exact actuals at
        //the same call-site position
        let index=fun.params.iter().position(|(formal,_)|formal==name)
            .filter(|_|!aliases.moved.contains(name))
            .or_else(||aliases.index(fun,name))?;
        if callee.params.get(actuals.len())?.1!=fun.params[index].1{return None;}
        actuals.push(index);i+=1;
        if i<range.end-1 {
            if tokens.get(i)?.kind!=K::Comma{return None;}
            i+=1;
        }
    }
    if actuals.len()!=callee.params.len(){return None;}
    let mut result=Vec::new();
    for source in callee_paths {
        result.push(ReferencePathOrigin{
            parameter:*actuals.get(source.parameter)?,path:source.path,
        });
        if result.len()>256{return None;}
    }
    Some(result)
}

#[derive(Clone)]
struct Slot {
    cell: Rc<RefCell<RefSlot>>,
    symbol: SymbolId,
    //Borrowed enum-pattern binding: release under CFG/NLL only when the selected arm's declaration and
    //owner were proven by FlowPlan
    pattern_loan: bool,
}
struct Cursor<'a> { tokens: Rc<Vec<Token<'a>>>, i: usize, end: usize }
impl<'a> Cursor<'a> {
    fn view(tokens:Rc<Vec<Token<'a>>>, range:Range<usize>)->Self {
        Self {tokens,i:range.start,end:range.end}
    }
    fn peek(&self)->Option<K<'a>> {if self.i<self.end {self.tokens.get(self.i).map(|x|x.kind)}else{None}}
    fn ahead(&self,n:usize)->Option<K<'a>> {let i=self.i.saturating_add(n);if i<self.end {self.tokens.get(i).map(|x|x.kind)}else{None}}
    fn pos(&self)->Position {at(&self.tokens,self.i.min(self.end))}
    fn eat(&mut self,k:K<'a>)->bool {if self.peek()==Some(k) {self.i+=1;true} else {false}}
    fn need(&mut self,k:K<'a>, msg:&str)->Result<(),Diagnostic>{if self.eat(k){Ok(())}else{Err(err(self.pos(),msg))}}
    fn word_borrowed(&mut self)->Result<&'a str,Diagnostic>{
        let p=self.pos();match self.peek(){Some(K::Ident(s))=>{self.i+=1;Ok(s)},_=>Err(err(p,"expected identifier"))}
    }
    fn word(&mut self)->Result<String,Diagnostic>{Ok(self.word_borrowed()?.to_owned())}
    fn body(&mut self)->Result<Range<usize>,Diagnostic> {
        self.need(K::LBrace,"expected '{'")?;
        let start=self.i;let mut depth=1usize;
        while self.i<self.end {
            match self.peek(){Some(K::LBrace)=>depth+=1,Some(K::RBrace)=>{depth-=1;if depth==0 {
                let body=start..self.i;self.i+=1;return Ok(body);
            }},_=>{}}
            self.i+=1;
        }
        Err(err(self.pos(),"unclosed function body"))
    }
    fn ty(&mut self,generics:Option<&[String]>)->Result<ConstType,Diagnostic>{
        Ok(self.ty_region(generics,false)?.0)
    }
    fn ty_region(&mut self,generics:Option<&[String]>,signature:bool)
        ->Result<(ConstType,Option<String>),Diagnostic> {
        let mut borrows:Vec<(bool,Option<String>)>=Vec::new();
        loop {
            if self.eat(K::AndAnd) {
                if borrows.len()>14 {return Err(err(self.pos(),"reference nesting limit exceeded"));}
                borrows.push((false,None));
                let lifetime=match self.peek(){Some(K::Lifetime(s))=>{self.i+=1;Some(s.to_owned())},_=>None};
                let exclusive=self.eat(K::Ident("mut"));
                borrows.push((exclusive,lifetime));
            } else if self.eat(K::Amp) {
                if borrows.len()>=16 {return Err(err(self.pos(),"reference nesting limit exceeded"));}
                let lifetime=match self.peek(){Some(K::Lifetime(s))=>{self.i+=1;Some(s.to_owned())},_=>None};
                let exclusive=self.eat(K::Ident("mut"));
                borrows.push((exclusive,lifetime));
            } else {break;}
        }
        if borrows.iter().any(|(_,region)|region.is_some()) && !signature {
            return Err(err(self.pos(),"named lifetimes in local types are not yet supported"));
        }
        if borrows.iter().skip(1).any(|(_,region)|region.is_some()) {
            return Err(err(self.pos(),"nested named lifetimes are not yet supported"));
        }
        let region=borrows.first().and_then(|(_,region)|region.clone());
        let word=self.word()?;
        let mut ty=match word.as_str(){"i64"=>ConstType::I64,"u64"=>ConstType::U64,
            "bool"=>ConstType::Bool,_ if generics.is_some_and(|names|names.iter().any(|name|name==&word))=>ConstType::Generic(word),
            _=>ConstType::Named(word)};
        for (exclusive,_) in borrows.into_iter().rev(){
            ty=if exclusive{ConstType::RefMut(Box::new(ty))}else{ConstType::Ref(Box::new(ty))};
        }
        Ok((ty,region))
    }
    fn builtin_bound(name:String,pos:Position)->Result<String,Diagnostic>{
        if matches!(name.as_str(),"Copy"|"Eq"|"PartialEq") {Ok(name)}
        else {Err(err(pos,format!("unsupported trait bound '{name}' (only Copy, Eq, PartialEq)")))}
    }
    fn function(&mut self,owner:Option<String>)->Result<Function,Diagnostic>{
        self.need(K::Ident("fn"),"expected fn")?;
        let name=self.word()?;
        let mut lifetimes=Vec::new();
        let mut generics=Vec::<GenericParameter>::new();
        if self.eat(K::Less) {loop {
            match self.peek(){
                Some(K::Lifetime(s))=>{self.i+=1;lifetimes.push(s.to_owned());},
                Some(K::Ident(_))=>{
                    let name=self.word()?;
                    if generics.iter().any(|g|g.name==name){return Err(err(self.pos(),"duplicate type parameter"));}
                    if generics.len()>=16{return Err(err(self.pos(),"maximum 16 type parameters"));}
                    let mut bounds=Vec::new();
                    if self.eat(K::Colon){loop {
                        bounds.push(Self::builtin_bound(self.word()?,self.pos())?);
                        if !self.eat(K::Plus){break;}
                    }}
                    generics.push(GenericParameter{name,bounds});
                }
                _=>return Err(err(self.pos(),"expected lifetime or type parameter")),
            }
            if self.eat(K::Greater){break;}
            self.need(K::Comma,"expected ',' between generic parameters")?;
            if self.eat(K::Greater){break;}
        }}
        let generic_names=generics.iter().map(|g|g.name.clone()).collect::<Vec<_>>();
        self.need(K::LParen,"expected '('")?;
        let mut params=Vec::new();
        let mut param_regions=Vec::<Option<String>>::new();
        if !self.eat(K::RParen) {loop{
            if params.len()>=32 {return Err(err(self.pos(),"maximum 32 function parameters"));}
            let receiver_reference=self.eat(K::Amp);
            let receiver_region=if receiver_reference {match self.peek(){
                Some(K::Lifetime(s))=>{self.i+=1;Some(s.to_owned())},_=>None,
            }}else{None};
            let receiver_mut=receiver_reference && self.eat(K::Ident("mut"));
            let param=self.word()?;
            let (ty,region)=if param=="self" && owner.is_some() && self.peek()!=Some(K::Colon) {
                if !params.is_empty(){return Err(err(self.pos(),"self must be first parameter"));}
                let inner=ConstType::Named(owner.as_ref().unwrap().clone());
                let ty=if receiver_mut {ConstType::RefMut(Box::new(inner))}
                    else if receiver_reference{ConstType::Ref(Box::new(inner))}else{inner};
                (ty,receiver_region)
            } else {
                if receiver_reference{return Err(err(self.pos(),"& parameters require an explicit name and type"));}
                self.need(K::Colon,"expected ':' after parameter")?;
                self.ty_region(Some(&generic_names),true)?
            };
            params.push((param,ty));param_regions.push(region);
            if self.eat(K::RParen){break;}self.need(K::Comma,"expected ','")?;
            if self.eat(K::RParen){break;}
        }}
        let (ret,mut result_region)=if self.eat(K::Minus) {
            self.need(K::Greater,"expected '->' return type")?;
            let (ty,region)=self.ty_region(Some(&generic_names),true)?;
            (Some(ty),region)
        }else{(None,None)};
        let mut bounds=Vec::<(String,String)>::new();
        if self.eat(K::Ident("where")) {loop {
            match self.peek() {
                Some(K::Lifetime(s))=>{
                    self.i+=1;let left=s.to_owned();
                    self.need(K::Colon,"expected ':' in outlives bound")?;
                    let right=match self.peek(){Some(K::Lifetime(s))=>{self.i+=1;s.to_owned()},
                        _=>return Err(err(self.pos(),"expected lifetime after ':'"))};
                    bounds.push((left,right));
                }
                Some(K::Ident(_))=>{
                    let name=self.word()?;
                    self.need(K::Colon,"expected ':' after type parameter")?;
                    let Some(generic)=generics.iter_mut().find(|g|g.name==name)else{
                        return Err(err(self.pos(),"where bound requires declared type parameter"));
                    };
                    loop {
                        generic.bounds.push(Self::builtin_bound(self.word()?,self.pos())?);
                        if !self.eat(K::Plus){break;}
                    }
                }
                _=>return Err(err(self.pos(),"expected lifetime or type parameter in where clause")),
            }
            if !self.eat(K::Comma){break;}
        }}
        //Rust lifetime elision: each anonymous input lifetime is distinct; single input (or &self receiver)
        //determines an elided output
        let returns_ref=matches!(ret.as_ref(),Some(ConstType::Ref(_)|ConstType::RefMut(_)));
        //Every reference return needs a declared or elided lifetime, even when the function has NO reference
        //parameters
        let regions=if returns_ref || !lifetimes.is_empty() || !bounds.is_empty() ||
            result_region.is_some() {
            for (i,((_,ty),region)) in params.iter().zip(param_regions.iter_mut()).enumerate() {
                if matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_)) && region.is_none(){
                    let inferred=format!("@elided:{i}");
                    lifetimes.push(inferred.clone());*region=Some(inferred);
                }
            }
            if matches!(ret.as_ref(),Some(ConstType::Ref(_)|ConstType::RefMut(_))) && result_region.is_none(){
                let receiver=params.first().and_then(|(name,_)|if name=="self"{param_regions[0].clone()}else{None});
                let single=param_regions.iter().filter_map(|r|r.as_ref()).count()==1;
                result_region=receiver.or_else(||if single{param_regions.iter().find_map(Clone::clone)}else{None});
                if result_region.is_none() {
                    return Err(err(self.pos(),"missing lifetime specifier on reference return"));
                }
            }
            Some(RegionSignature::new(&lifetimes,&param_regions,result_region,&bounds)
                .map_err(|message|err(self.pos(),message))?)
        }else{None};
        let body=self.body()?;
        Ok(Function{name,params,ret,generics,regions,body})
    }

}
#[derive(Clone,Debug)]
enum HostFlow { Break, Continue, Return(Option<ConstValue>) }
#[derive(Clone,Copy,Debug,PartialEq,Eq,Hash)]
struct FunctionId(u32);
struct Front<'a>{cur:Cursor<'a>, types:HashMap<String,Vec<(String,ConstType)>>,
    enums:HashMap<String,Vec<String>>,enum_payloads:HashMap<String,Vec<Vec<ConstType>>>,type_ids:HashMap<String,TypeId>,type_names:Vec<String>,functions:HashMap<String,FunctionId>,
    methods:HashMap<TypeId,HashMap<String,FunctionId>>, fn_defs:Vec<Rc<Function>>,
    verified_return_paths:HashMap<String,Vec<ReferencePathOrigin>>,
    quantum:Vec<Stmt>, quantum_names:HashSet<String>, scopes:Vec<HashMap<String,Slot>>,
    pending_variant_bindings:Vec<(String,ConstValue,SymbolId)>,
    scope_cache:Vec<HashMap<String,Slot>>, calls:usize, block_depth:usize, flow_stack:Vec<FlowPlan>, loop_depth:usize, host_flow:Option<HostFlow>, return_stack:Vec<ConstType> }
impl<'a> Front<'a>{
    fn new(tokens:Vec<Token<'a>>)->Self{let end=tokens.len();let tokens=Rc::new(tokens);Self{
        cur:Cursor::view(tokens,0..end),types:HashMap::new(),enums:HashMap::new(),enum_payloads:HashMap::new(),
        type_ids:HashMap::new(),type_names:Vec::new(),functions:HashMap::new(),methods:HashMap::new(),fn_defs:Vec::new(),
        verified_return_paths:HashMap::new(),quantum:Vec::new(),quantum_names:HashSet::new(),
        scopes:vec![HashMap::new()],pending_variant_bindings:Vec::new(),scope_cache:Vec::new(),calls:0,block_depth:0,flow_stack:Vec::new(),loop_depth:0,host_flow:None,return_stack:Vec::new()}}
    fn definition(&mut self)->Result<(),Diagnostic>{
        if self.cur.eat(K::Ident("struct")){
            let name=self.cur.word()?;
            if self.types.contains_key(&name)||self.enums.contains_key(&name){return Err(err(self.cur.pos(),"duplicate type"));}
            self.cur.need(K::LBrace,"expected '{' after struct")?;
            let mut fields=Vec::new();
            while !self.cur.eat(K::RBrace){
                if self.cur.peek().is_none(){return Err(err(self.cur.pos(),"unclosed struct"));}
                if fields.len()>=128{return Err(err(self.cur.pos(),"too many fields"));}
                let key=self.cur.word()?;self.cur.need(K::Colon,"expected ':'")?;
                let ty=self.cur.ty(None)?;
                if let ConstType::Named(ref aggregate)=ty {
                    if !self.types.contains_key(aggregate) && !self.enums.contains_key(aggregate) {
                        return Err(err(self.cur.pos(),"struct field requires an already declared type"));
                    }
                }
                if matches!(ty,ConstType::Generic(_)) {
                    return Err(err(self.cur.pos(),"generic struct fields are not yet supported"));
                }
                if fields.iter().any(|(n,_)|n==&key){return Err(err(self.cur.pos(),"duplicate field"));}
                fields.push((key,ty));
                if !self.cur.eat(K::RBrace){self.cur.need(K::Comma,"expected ','")?;}
                else {break;}
            }
            let id=TypeId(u32::try_from(self.type_ids.len()).map_err(|_|err(self.cur.pos(),"too many aggregate types"))?);
            self.type_ids.insert(name.clone(),id);
            self.type_names.push(name.clone());
            self.types.insert(name,fields);
        } else if self.cur.eat(K::Ident("enum")) {
            let name=self.cur.word()?;
            if self.types.contains_key(&name)||self.enums.contains_key(&name){return Err(err(self.cur.pos(),"duplicate type"));}
            self.cur.need(K::LBrace,"expected '{' after enum")?;
            let mut variants=Vec::new();
            let mut payloads=Vec::new();
            while !self.cur.eat(K::RBrace){
                if self.cur.peek().is_none(){return Err(err(self.cur.pos(),"unclosed enum"));}
                if variants.len()>=128{return Err(err(self.cur.pos(),"too many variants"));}
                let v=self.cur.word()?;
                if variants.contains(&v){return Err(err(self.cur.pos(),"duplicate variant"));}
                let mut fields=Vec::new();
                if self.cur.eat(K::LParen){
                    if self.cur.peek()==Some(K::RParen){return Err(err(self.cur.pos(),"empty tuple variant: use a unit variant"));}
                    loop {
                        if fields.len()>=8{return Err(err(self.cur.pos(),"maximum eight tuple-variant fields"));}
                        let ty=self.cur.ty(None)?;
                        if !self.owned_enum_payload_type(&ty){
                            return Err(err(self.cur.pos(),
                                "enum payload needs a previously declared, reference-free value type"));
                        }
                        fields.push(ty);
                        if self.cur.eat(K::RParen){break;}
                        self.cur.need(K::Comma,"expected ',' between tuple-variant fields")?;
                        if self.cur.eat(K::RParen){break;}
                    }
                }
                if self.cur.peek()==Some(K::LBrace){
                    return Err(err(self.cur.pos(),"named enum fields require typed pattern and MovePath support"));
                }
                variants.push(v);payloads.push(fields);
                if !self.cur.eat(K::RBrace){self.cur.need(K::Comma,"expected ','")?;}
                else{break;}
            }
            if variants.is_empty(){return Err(err(self.cur.pos(),"empty enum"));}
            let id=TypeId(u32::try_from(self.type_ids.len()).map_err(|_|err(self.cur.pos(),"too many aggregate types"))?);
            self.type_ids.insert(name.clone(),id);
            self.type_names.push(name.clone());
            self.enum_payloads.insert(name.clone(),payloads);
            self.enums.insert(name,variants);
        } else if self.cur.eat(K::Ident("impl")) {
            let owner=self.cur.word()?;
            if !self.types.contains_key(&owner){return Err(err(self.cur.pos(),"impl requires declared struct"));}
            let owner_id=*self.type_ids.get(&owner).expect("registered struct type");
            self.cur.need(K::LBrace,"expected '{' after impl")?;
            while !self.cur.eat(K::RBrace){
                if self.cur.peek().is_none(){return Err(err(self.cur.pos(),"unclosed impl"));}
                let fun=self.cur.function(Some(owner.clone()))?;
                if !fun.generics.is_empty(){return Err(err(self.cur.pos(),"generic methods not yet supported"));}
                let methods=self.methods.entry(owner_id).or_default();
                if methods.contains_key(&fun.name){return Err(err(self.cur.pos(),"duplicate method"));}
                let id=FunctionId(u32::try_from(self.fn_defs.len()).map_err(|_|err(self.cur.pos(),"too many functions"))?);
                methods.insert(fun.name.clone(),id);
                self.fn_defs.push(Rc::new(fun));
            }
        } else if self.cur.peek()==Some(K::Ident("fn")){
            let fun=self.cur.function(None)?;
            if self.functions.contains_key(&fun.name){return Err(err(self.cur.pos(),"duplicate function"));}
            let id=FunctionId(u32::try_from(self.fn_defs.len()).map_err(|_|err(self.cur.pos(),"too many functions"))?);
            self.functions.insert(fun.name.clone(),id);
            self.fn_defs.push(Rc::new(fun));
        } else{return Err(err(self.cur.pos(),"expected fn, struct, enum or impl"));}
        Ok(())
    }
    fn push_scope(&mut self) {
        let scope=self.scope_cache.pop().unwrap_or_default();
        debug_assert!(scope.is_empty());
        self.scopes.push(scope);
    }
    fn pop_scope(&mut self)->Result<(),Diagnostic> {
        let mut scope=self.scopes.pop().expect("scope stack balanced");
        if scope.values().all(|slot|slot.cell.borrow().loans.is_empty()) {
            scope.clear();
            self.scope_cache.push(scope);
            return Ok(());
        }
        let owners:Vec<_>=scope.values().map(|slot|Rc::clone(&slot.cell)).collect();
        //Detect only references that really outlive this scope
        for owner in &owners {owner.borrow_mut().alive=false;}
        for owner in &owners {
            let value=owner.borrow_mut().val.take();
            drop(value); //RefLease::drop releases its borrow on the owner
        }
        let escaped=owners.iter().any(|owner|!owner.borrow().loans.is_empty());
        scope.clear();
        self.scope_cache.push(scope);
        if escaped {Err(err(self.cur.pos(),"reference escapes the lifetime of a local value"))}
        else{Ok(())}
    }
    fn end_dead_local_borrows(&mut self) {
        let Some(flow)=self.flow_stack.last() else {return;};
        if flow.live_at(self.cur.i).is_none(){return;}
        let scope_base=flow.scope_base;
        let mut ended=Vec::<SymbolId>::new();
        loop {
            let mut released=false;
            for scope in self.scopes.iter_mut().skip(scope_base).rev() {
                for slot in scope.values_mut() {
                    //Pattern bindings have their own CFG entry/definition and solved region. If construction failed, keep
                    //the previous conservative arm-scoped lifetime
                    if slot.pattern_loan && !flow.verified_pattern_loan(slot.symbol) {continue;}
                    //The solved local region may extend a parent loan through a live reborrow even when direct USE/DEF
                    //marks the parent's binding dead at this boundary
                    if flow.loan_live_at(self.cur.i,slot.symbol).unwrap_or(true) {continue;}
                    let mut cell=slot.cell.borrow_mut();
                    if !cell.alive || !cell.loans.is_empty(){continue;}
                    let can_end=matches!(cell.val.as_ref(),Some(ConstValue::Ref(r))
                        if r.0.active_children.get()==0);
                    if !can_end {continue;}
                    let dead=cell.val.take();
                    drop(cell);
                    drop(dead);
                    ended.push(slot.symbol);
                    released=true;
                }
            }
            if !released {break;}
        }
        if let Some(flow)=self.flow_stack.last_mut(){
            for binding in ended {flow.record_verified_loan_end(binding,self.cur.i);}
        }
    }
    fn start_flow(&mut self,range:Range<usize>,include_current_scope:bool){
        //Not a compiler-wide pass. Only typed function bodies are analysed; the legacy and direct quantum
        //parsers never construct this graph
        let scope_base=self.scopes.len()-usize::from(include_current_scope);
        let has_parameter_refs=self.scopes.iter().skip(scope_base).any(|scope|scope.values().any(|slot|
            matches!(slot.cell.borrow().val.as_ref(),Some(ConstValue::Ref(_)))));
        let has_borrows=self.cur.tokens[range.clone()].iter().any(|t|matches!(t.kind,K::Amp|K::AndAnd|K::Dot));
        let parameters=if include_current_scope {self.scopes.last().unwrap().iter()
            .map(|(name,slot)|(name.clone(),slot.symbol)).collect::<Vec<_>>()}
            else{Vec::new()};
        self.flow_stack.push(FlowPlan::new(&self.cur.tokens,range,
            has_parameter_refs||has_borrows,scope_base,&parameters));
    }
    fn owned_enum_payload_type(&self,ty:&ConstType)->bool {
        let mut pending=vec![ty.clone()];
        let mut seen=HashSet::<String>::new();
        while let Some(next)=pending.pop(){
            match next {
                ConstType::I64|ConstType::U64|ConstType::Bool=>{},
                ConstType::Named(name)=>{
                    if !seen.insert(name.clone()){continue;}
                    if let Some(fields)=self.types.get(&name){
                        pending.extend(fields.iter().map(|(_,ty)|ty.clone()));
                    }else if let Some(variants)=self.enum_payloads.get(&name){
                        pending.extend(variants.iter().flat_map(|fields|fields.iter().cloned()));
                    }else{return false;}
                },
                ConstType::Resolved(id)=>{
                    let Some(name)=self.type_names.get(id.0 as usize)else{return false;};
                    pending.push(ConstType::Named(name.clone()));
                },
                _=>return false,
            }
        }
        true
    }
    fn resolved_type(&self, ty:&ConstType)->ConstType {
        match ty {
            ConstType::Named(name) => self.type_ids.get(name)
                .map(|id|ConstType::Resolved(*id)).unwrap_or_else(||ty.clone()),
            ConstType::Ref(inner)=>ConstType::Ref(Box::new(self.resolved_type(inner))),
            ConstType::RefMut(inner)=>ConstType::RefMut(Box::new(self.resolved_type(inner))),
            _ => ty.clone(),
        }
    }
    fn value_matches(&self,val:&ConstValue,ty:&ConstType)->bool {
        val.matches(&self.resolved_type(ty))
    }
    //One monotonic unification table per call; a type parameter is bound exactly once. Repeated T
    //occurrences must agree on one concrete type
    fn bind_type(expected:&ConstType,actual:&ConstType,
        bindings:&mut HashMap<String,ConstType>)->Result<(),String>{
        match (expected,actual){
            (ConstType::Generic(name),ty)=>match bindings.get(name){
                Some(existing) if existing!=ty=>Err(format!("generic type mismatch for {name}")),
                Some(_)=>Ok(()),
                None=>{bindings.insert(name.clone(),ty.clone());Ok(())}
            },
            (ConstType::Ref(inner),ConstType::Ref(actual)) |
            (ConstType::RefMut(inner),ConstType::RefMut(actual))=>
                Self::bind_type(inner,actual,bindings),
            _=>Ok(()),
        }
    }
    fn instantiate(ty:&ConstType,bindings:&HashMap<String,ConstType>)->ConstType {
        match ty {
            ConstType::Generic(name)=>bindings.get(name).cloned().unwrap_or_else(||ty.clone()),
            ConstType::Ref(inner)=>ConstType::Ref(Box::new(Self::instantiate(inner,bindings))),
            ConstType::RefMut(inner)=>ConstType::RefMut(Box::new(Self::instantiate(inner,bindings))),
            _=>ty.clone(),
        }
    }
    fn has_unbound(ty:&ConstType)->bool {
        match ty {
            ConstType::Generic(_)=>true,
            ConstType::Ref(inner)|ConstType::RefMut(inner)=>Self::has_unbound(inner),
            _=>false,
        }
    }
    fn satisfies_builtin_trait(ty:&ConstType,bound:&str)->bool {
        match bound {
            "Copy"=>matches!(ty,ConstType::I64|ConstType::U64|ConstType::Bool|ConstType::Ref(_)),
            "Eq"|"PartialEq"=>matches!(ty,ConstType::I64|ConstType::U64|ConstType::Bool),
            _=>false,
        }
    }
    fn field_id(&self,owner:TypeId,field:&str)->Option<FieldId> {
        let name=self.type_names.get(owner.0 as usize)?;
        self.types.get(name)?.iter().position(|(n,_)|n==field)
            .and_then(|i|u32::try_from(i).ok()).map(FieldId)
    }
    fn declared_field_type(&self,id:TypeId,field:FieldId)->Option<ConstType>{
        let owner=self.type_names.get(id.0 as usize)?;
        let field_type=&self.types.get(owner)?.get(field.0 as usize)?.1;
        Some(self.resolved_type(field_type))
    }
    fn cell(&self,name:&str)->Result<Rc<RefCell<RefSlot>>,Diagnostic>{
        self.scopes.iter().rev().find_map(|scope|scope.get(name).map(|s|Rc::clone(&s.cell)))
            .ok_or_else(||err(self.cur.pos(),format!("unknown typed variable '{name}'")))
    }
    fn place_field(&self,cell:&Rc<RefCell<RefSlot>>,name:&str,where_at:Position)->Result<FieldId,Diagnostic>{
        let owner=cell.borrow();
        let Some(ConstValue::Struct(id,_))=owner.val.as_ref() else {
            return Err(err(where_at,"field access requires struct"));
        };
        self.field_id(*id,name).ok_or_else(||err(where_at,"unknown struct field"))
    }
    fn typed_place_of(&self,owner:&Rc<RefCell<RefSlot>>,place:Place)->Option<TypedPlace> {
        let symbol=self.scopes.iter().rev().flat_map(|scope|scope.values())
            .find(|s|Rc::ptr_eq(&s.cell,owner))?.symbol;
        let ty=match owner.borrow().val.as_ref() {
            Some(ConstValue::Struct(id,_))=>Some(*id),_=>None,
        };
        TypedPlace::new(symbol,ty,place)
    }
    fn typed_path_of(&self,owner:&Rc<RefCell<RefSlot>>,place:Place)
        ->Option<crate::cfg_borrow::Path> {
        let symbol=self.scopes.iter().rev().flat_map(|scope|scope.values())
            .find(|slot|Rc::ptr_eq(&slot.cell,owner))?.symbol;
        let mut result=crate::cfg_borrow::Path::root(symbol);
        let ids=place.indices();
        if ids.is_empty(){return Some(result);}
        let id=match owner.borrow().val.as_ref(){
            Some(ConstValue::Struct(id,_))|Some(ConstValue::EnumData(id,_,_))=>*id,
            _=>return None,
        };
        let mut aggregate=id;
        for (i,&field) in ids.iter().enumerate(){
            result.fields.push(crate::cfg_borrow::FieldKey{aggregate,field});
            if i+1<ids.len(){
                let next_ty=if field.0&0x8000_0000!=0 {
                    let name=self.type_names.get(aggregate.0 as usize)?;
                    self.enum_payloads.get(name)?
                        .get(((field.0>>4)&0x7f) as usize)?
                        .get((field.0&0xf) as usize)?.clone()
                }else{self.declared_field_type(aggregate,field)?};
                match self.resolved_type(&next_ty){
                    ConstType::Resolved(next)=>aggregate=next,
                    _=>return None,
                }
            }
        }
        Some(result)
    }
    fn record_checked_access(&mut self,token:usize,owner:&Rc<RefCell<RefSlot>>,
        place:Place,kind:PlaceAccessKind) {
        if self.flow_stack.is_empty(){return;}
        if let Some(path)=self.typed_path_of(owner,place){
            if let Some(flow)=self.flow_stack.last_mut(){flow.record_verified_path(token,path,kind);}
        }
        if let Some(typed)=self.typed_place_of(owner,place) {
            if let Some(flow)=self.flow_stack.last_mut(){let _=flow.record_typed_access(token,typed,kind);}
        }
    }
    fn verified_edge_conflict(&self,name:&str,at:usize,place:Place,
        kind:PlaceAccessKind,actual:&RefSlot)->bool {
        let Some(binding)=self.scopes.iter().rev().find_map(|scope|scope.get(name)) else {return false;};
        if actual.loans.is_empty(){return false;}
        let ty=match actual.val.as_ref(){Some(ConstValue::Struct(id,_))=>Some(*id),_=>None};
        let Some(typed)=TypedPlace::new(binding.symbol,ty,place)else{return false;};
        self.flow_stack.last().and_then(|flow|
            flow.conflicting_typed_access(at,typed,kind))
            .is_some_and(|candidates|!candidates.is_empty())
    }
    fn borrow_place(&mut self,name:&str,field:Option<&str>,exclusive:bool)->Result<ConstValue,Diagnostic>{
        let p=self.cur.pos();let cell=self.cell(name)?;
        let source_reference={let owner=cell.borrow();match owner.val.as_ref(){
            Some(ConstValue::Ref(reference))=>Some(reference.clone()),_=>None,
        }};
        if let (Some(parent),Some(field))=(source_reference,field) {
            return self.reborrow_reference(parent,Some(field),exclusive,true,p);
        }
        let field_id=if let Some(name)=field{Some(self.place_field(&cell,name,p)?)}else{None};
        let mut owner=cell.borrow_mut();
        if !owner.alive || owner.val.is_none(){return Err(err(p,"borrow of moved or dead value"));}
        if field_id.map_or(!owner.move_paths.whole_initialized(),|id|!owner.move_paths.field_initialized(id)) {
            return Err(err(p,"cannot borrow partially moved or uninitialized place"));
        }
        if exclusive && !owner.mutable {return Err(err(p,"cannot mutably borrow an immutable binding"));}
        let dynamic_conflict=owner.loans.iter().any(|(_,is_mut,f)|
            f.overlaps(Place::from_field(field_id))&&(exclusive||*is_mut));
        if dynamic_conflict {
            //A CFG candidate can corroborate a conflict, but a negative or unavailable CFG analysis must not bypass
            //RefLease
            let access=if exclusive {PlaceAccessKind::BorrowExclusive}
                else {PlaceAccessKind::BorrowShared};
            let _cfg_candidate=self.verified_edge_conflict(name,self.cur.i.saturating_sub(1),
                Place::from_field(field_id),access,&owner);
            return Err(err(p,"conflicting shared/mutable borrow"));
        }
        let value=owner.val.as_ref().unwrap();
        let ty=if let Some(index)=field_id {
            let ConstValue::Struct(_,fields)=value else {return Err(err(p,"expected struct"));};
            fields[index.0 as usize].ty()
        } else {value.ty()};
        let key=owner.next_loan;
        owner.next_loan=owner.next_loan.checked_add(1).ok_or_else(||err(p,"borrow ID overflow"))?;
        owner.loans.push((key,exclusive,Place::from_field(field_id)));
        drop(owner);
        self.record_checked_access(self.cur.i.saturating_sub(1),&cell,
            Place::from_field(field_id),if exclusive {PlaceAccessKind::BorrowExclusive}
                else {PlaceAccessKind::BorrowShared});
        Ok(ConstValue::Ref(RefValue(Rc::new(RefLease{owner:cell,place:Place::from_field(field_id),mutable:exclusive,item_type:ty,key,parent:None,registered:true,
            active_children:std::cell::Cell::new(0),active_exclusive_child:std::cell::Cell::new(false),return_origin_guards:RefCell::new(Vec::new())}))))
    }
    fn take_enum_pattern_field(&mut self,name:&str,fields:&[FieldId],token:usize)
        ->Result<ConstValue,Diagnostic> {
        let p=self.cur.pos();
        if fields.is_empty(){return Err(err(p,"enum move requires a payload field"));}
        let cell=self.cell(name)?;
        let mut slot=cell.borrow_mut();
        if !slot.alive || slot.val.is_none(){return Err(err(p,"use of moved enum"));}
        if !slot.move_paths.path_initialized(fields){return Err(err(p,"use of moved enum payload"));}
        let place=Place::from_fields(fields).ok_or_else(||err(p,"enum path depth exceeded"))?;
        if slot.loans.iter().any(|(_,_,loan)|loan.overlaps(place)){
            return Err(err(p,"cannot move enum payload while borrowed"));
        }
        let value=slot.val.as_mut().and_then(|root|Self::nested_value_mut(root,fields))
            .ok_or_else(||err(p,"invalid enum payload move path"))?;
        if value.is_copy(){return Err(err(p,"expected non-Copy enum payload"));}
        let moved=std::mem::replace(value,ConstValue::Unit);
        if !slot.move_paths.mark_path_moved(fields){
            return Err(err(p,"enum payload already moved"));
        }
        drop(slot);
        self.record_checked_access(token,&cell,place,PlaceAccessKind::Move);
        Ok(moved)
    }
    fn borrow_enum_path(&mut self,name:&str,fields:&[FieldId],
        exclusive:bool,token:usize)->Result<ConstValue,Diagnostic>{
        let p=self.cur.pos();
        if fields.is_empty(){return Err(err(p,"enum payload reference needs a field"));}
        let place=Place::from_fields(fields)
            .ok_or_else(||err(p,"nested enum pattern path too deep"))?;
        let cell=self.cell(name)?;
        let mut owner=cell.borrow_mut();
        if !owner.alive{return Err(err(p,"borrow of expired enum"));}
        if exclusive && !owner.mutable{return Err(err(p,"cannot mutably borrow immutable enum"));}
        let ty={
            let root=owner.val.as_ref().ok_or_else(||err(p,"borrow of moved enum"))?;
            if !matches!(root,ConstValue::Enum(..)|ConstValue::EnumData(..)) {
                return Err(err(p,"enum payload reference requires an enum owner"));
            }
            Self::nested_value(root,fields).ok_or_else(||err(p,"invalid nested enum payload path"))?.ty()
        };
        if !owner.move_paths.path_initialized(fields){return Err(err(p,"borrow of moved enum field"));}
        if owner.loans.iter().any(|(_,is_mut,other)|other.overlaps(place)&&(exclusive||*is_mut)){
            return Err(err(p,"conflicting nested enum payload borrow"));
        }
        let key=owner.next_loan;
        owner.next_loan=owner.next_loan.checked_add(1).ok_or_else(||err(p,"enum loan overflow"))?;
        owner.loans.push((key,exclusive,place));
        drop(owner);
        self.record_checked_access(token,&cell,place,
            if exclusive{PlaceAccessKind::BorrowExclusive}else{PlaceAccessKind::BorrowShared});
        Ok(ConstValue::Ref(RefValue(Rc::new(RefLease{
            owner:cell,place,mutable:exclusive,item_type:ty,key,parent:None,registered:true,
            active_children:std::cell::Cell::new(0),
            active_exclusive_child:std::cell::Cell::new(false),return_origin_guards:RefCell::new(Vec::new()),
        }))))
    }
    fn reborrow_reference(&self,parent:RefValue,field:Option<&str>,exclusive:bool,
        explicit_place:bool,p:Position)->Result<ConstValue,Diagnostic>{
        if !explicit_place {return Err(err(p,"&reference would require nested &&T support; use &*reference"));}
        if exclusive && !parent.0.mutable{return Err(err(p,"cannot mutably reborrow a shared reference"));}
        //A mutable parent may have several shared children simultaneously; an exclusive child prevents all new
        //siblings until it is released
        if parent.0.active_exclusive_child.get() ||
            (exclusive && parent.0.active_children.get()!=0) {
            return Err(err(p,"reference is already reborrowed"));
        }
        let (new_place,new_type)=if let Some(field_name)=field {
            let owner=parent.0.owner.borrow();
            if !owner.alive{return Err(err(p,"dangling reference"));}
            let root=owner.val.as_ref().ok_or_else(||err(p,"reference to moved owner"))?;
            let mut indices=parent.0.place.indices().to_vec();
            let current=Self::nested_value(root,&indices)
                .ok_or_else(||err(p,"field borrow requires initialized struct"))?;
            let ConstValue::Struct(id,_) = current else {
                return Err(err(p,"field borrow requires struct"));
            };
            let fid=self.field_id(*id,field_name).ok_or_else(||err(p,"unknown struct field"))?;
            indices.push(fid);
            if !owner.move_paths.path_initialized(&indices){return Err(err(p,"borrow of moved field"));}
            let ty=self.declared_field_type(*id,fid)
                .ok_or_else(||err(p,"unknown field type"))?;
            let place=Place::from_fields(&indices)
                .ok_or_else(||err(p,"field path depth exceeded"))?;
            (place,ty)
        }else{(parent.0.place,parent.0.item_type.clone())};
        if parent.0.mutable {
            parent.0.active_children.set(parent.0.active_children.get()+1);
            if exclusive {parent.0.active_exclusive_child.set(true);}
        }
        Ok(ConstValue::Ref(RefValue(Rc::new(RefLease{
            owner:Rc::clone(&parent.0.owner),place:new_place,mutable:exclusive,
            item_type:new_type,key:parent.0.key,parent:Some(Rc::clone(&parent.0)),
            registered:false,active_children:std::cell::Cell::new(0),
            active_exclusive_child:std::cell::Cell::new(false),return_origin_guards:RefCell::new(Vec::new()),
        }))))
    }
    fn deref_value(&self,name:&str,levels:usize)->Result<ConstValue,Diagnostic>{
        let p=self.cur.pos();
        let cell=self.cell(name)?;
        let mut value={let slot=cell.borrow();
            slot.val.as_ref().cloned().ok_or_else(||err(p,"dereference of moved value"))?
        };
        for _ in 0..levels {
            let ConstValue::Ref(reference)=value else {
                return Err(err(p,"dereference requires &T or &mut T"));
            };
            if reference.0.active_children.get()!=0 {
                return Err(err(p,"reference suspended by reborrow"));
            }
            let owner=reference.0.owner.borrow();
            if !owner.alive {return Err(err(p,"dangling reference: owner is out of scope"));}
            let Some(referent)=owner.val.as_ref() else {
                return Err(err(p,"reference to moved value"));
            };
            let path=reference.0.place.indices();
            if !owner.move_paths.path_initialized(path) {
                return Err(err(p,"dereference of partially moved place"));
            }
            let referent=Self::nested_value(referent,path)
                .ok_or_else(||err(p,"reference points to uninitialized field"))?;
            //A nested shared reference is Copy. Exclusive references and aggregates cannot be moved out of a
            //reference by dereferencing
            if !referent.is_copy() {
                return Err(err(p,"cannot move non-Copy value out of a reference"));
            }
            value=referent.clone();
        }
        Ok(value)
    }
    fn nested_ids(&self,root:&ConstValue,names:&[String],p:Position)
        ->Result<(Vec<FieldId>,ConstType),Diagnostic> {
        let mut current=root;
        let mut ids=Vec::with_capacity(names.len());
        let mut ty=root.ty();
        for name in names {
            let ConstValue::Struct(type_id,values)=current else {
                return Err(err(p,"nested field access requires an initialized struct"));
            };
            let id=self.field_id(*type_id,name).ok_or_else(||err(p,"unknown struct field"))?;
            ty=self.declared_field_type(*type_id,id).ok_or_else(||err(p,"unknown field type"))?;
            ids.push(id);
            current=values.get(id.0 as usize).ok_or_else(||err(p,"unknown field index"))?;
        }
        Ok((ids,ty))
    }
    fn nested_value<'v>(mut value:&'v ConstValue,ids:&[FieldId])->Option<&'v ConstValue>{
        for &id in ids {
            value=match value {
                ConstValue::Struct(_,fields)=>fields.get(id.0 as usize)?,
                ConstValue::EnumData(_,variant,fields) if id.0&0x8000_0000!=0 &&
                    ((id.0>>4)&0x7f)==variant.0 && (id.0&0xf)<8=>
                    fields.get((id.0&0xf) as usize)?,
                _=>return None,
            };
        }
        Some(value)
    }
    fn nested_value_mut<'v>(mut value:&'v mut ConstValue,ids:&[FieldId])->Option<&'v mut ConstValue>{
        for &id in ids {
            value=match value {
                ConstValue::Struct(_,fields)=>fields.get_mut(id.0 as usize)?,
                ConstValue::EnumData(_,variant,fields) if id.0&0x8000_0000!=0 &&
                    ((id.0>>4)&0x7f)==variant.0 && (id.0&0xf)<8=>
                    fields.get_mut((id.0&0xf) as usize)?,
                _=>return None,
            };
        }
        Some(value)
    }
    fn access_nested_path(&mut self,name:&str,names:&[String],p:Position)
        ->Result<ConstValue,Diagnostic> {
        let source=self.cell(name)?;
        let reference={let slot=source.borrow();match slot.val.as_ref(){
            Some(ConstValue::Ref(r))=>Some(r.clone()),_=>None
        }};
        let owner=reference.as_ref().map_or_else(||Rc::clone(&source),|r|Rc::clone(&r.0.owner));
        if let Some(r)=&reference {
            if r.0.active_children.get()!=0 {return Err(err(p,"reference suspended by reborrow"));}
        }
        let mut slot=owner.borrow_mut();
        if !slot.alive {return Err(err(p,"dangling reference"));}
        let root=slot.val.as_ref().ok_or_else(||err(p,"use of moved value"))?;
        let mut full=reference.as_ref().map(|r|r.0.place.indices().to_vec()).unwrap_or_default();
        let base=Self::nested_value(root,&full).ok_or_else(||err(p,"reference to moved place"))?;
        let (suffix,_ty)=self.nested_ids(base,names,p)?;
        full.extend(suffix);
        if !slot.move_paths.path_initialized(&full){return Err(err(p,"use of moved field"));}
        let place=Place::from_fields(&full).ok_or_else(||err(p,"field path depth exceeded"))?;
        let field=Self::nested_value(root,&full).ok_or_else(||err(p,"uninitialized field"))?;
        let copy=field.is_copy();
        if !copy && reference.is_some(){return Err(err(p,"cannot move non-Copy field out of a reference"));}
        if slot.loans.iter().any(|(_,exclusive,borrowed)|
            borrowed.overlaps(place) && (!copy||*exclusive) && reference.is_none()) {
            return Err(err(p,"cannot move field while borrowed"));
        }
        let result=if copy {field.clone()} else {
            let Some(value)=slot.val.as_mut().and_then(|root|Self::nested_value_mut(root,&full)) else {
                return Err(err(p,"invalid field path"));
            };
            let result=std::mem::replace(value,ConstValue::Unit);
            if !slot.move_paths.mark_path_moved(&full){return Err(err(p,"use of moved field"));}
            result
        };
        drop(slot);
        self.record_checked_access(self.cur.i.saturating_sub(1),&owner,place,
            if copy{PlaceAccessKind::Read}else{PlaceAccessKind::Move});
        Ok(result)
    }
    fn nested_hint(&self,name:&str,names:&[String],p:Position)->Result<ConstType,Diagnostic>{
        let source=self.cell(name)?;
        let reference={let slot=source.borrow();match slot.val.as_ref(){
            Some(ConstValue::Ref(r))=>Some(r.clone()),_=>None
        }};
        let owner=reference.as_ref().map_or_else(||Rc::clone(&source),|r|Rc::clone(&r.0.owner));
        let slot=owner.borrow();
        let mut prefix=reference.as_ref().map(|r|r.0.place.indices().to_vec()).unwrap_or_default();
        let root=slot.val.as_ref().ok_or_else(||err(p,"assignment to moved value"))?;
        let mut current=Self::nested_value(root,&prefix).ok_or_else(||err(p,"field parent is uninitialized"))?;
        let mut field_ty=None;
        for (i,field) in names.iter().enumerate(){
            let ConstValue::Struct(id,values)=current else{return Err(err(p,"nested assignment requires struct"));};
            let fid=self.field_id(*id,field).ok_or_else(||err(p,"unknown struct field"))?;
            field_ty=Some(self.declared_field_type(*id,fid).ok_or_else(||err(p,"unknown field type"))?);
            prefix.push(fid);
            if i+1<names.len() {
                if !slot.move_paths.ancestors_present(&prefix){return Err(err(p,"uninitialized parent field"));}
                current=values.get(fid.0 as usize).ok_or_else(||err(p,"field index out of range"))?;
            }
        }
        field_ty.ok_or_else(||err(p,"missing assignment field"))
    }
    fn assign_nested(&mut self,name:&str,names:&[String],op:K<'a>,rhs:ConstValue,p:Position,token:usize)
        ->Result<(),Diagnostic>{
        let source=self.cell(name)?;
        let reference={let slot=source.borrow();match slot.val.as_ref(){
            Some(ConstValue::Ref(r))=>Some(r.clone()),_=>None
        }};
        let owner=reference.as_ref().map_or_else(||Rc::clone(&source),|r|Rc::clone(&r.0.owner));
        let hint=self.nested_hint(name,names,p)?;
        let mut slot=owner.borrow_mut();
        if !slot.alive{return Err(err(p,"assignment to expired owner"));}
        if let Some(r)=&reference {
            if !r.0.mutable{return Err(err(p,"assignment requires &mut T"));}
            if r.0.active_children.get()!=0{return Err(err(p,"reference suspended by reborrow"));}
        }else if !slot.mutable{return Err(err(p,"cannot assign to immutable variable"));}
        let mut prefix=reference.as_ref().map(|r|r.0.place.indices().to_vec()).unwrap_or_default();
        let root=slot.val.as_ref().ok_or_else(||err(p,"assignment to moved owner"))?;
        let base=Self::nested_value(root,&prefix).ok_or_else(||err(p,"uninitialized parent"))?;
        let (suffix,_)=self.nested_ids(base,names,p)?;
        prefix.extend(suffix);
        if !slot.move_paths.ancestors_present(&prefix){return Err(err(p,"write through an uninitialized parent"));}
        let place=Place::from_fields(&prefix).ok_or_else(||err(p,"field path depth exceeded"))?;
        if slot.loans.iter().any(|(key,_,loan_place)|
            loan_place.overlaps(place) && reference.as_ref().map_or(true,|r|
                r.0.key!=*key && !r.0.owns_return_origin_guard(&owner,*key))) {
            return Err(err(p,"cannot assign while place is borrowed"));
        }
        let was_moved=!slot.move_paths.path_initialized(&prefix);
        if was_moved && op!=K::Equal{return Err(err(p,"compound assignment to moved field"));}
        let old=slot.val.as_mut().and_then(|root|Self::nested_value_mut(root,&prefix))
            .ok_or_else(||err(p,"unknown nested field"))?;
        let result=if op==K::Equal{rhs}else{
            let binary=match op{K::PlusEq=>K::Plus,K::MinusEq=>K::Minus,K::StarEq=>K::Star,
                K::SlashEq=>K::Slash,K::PercentEq=>K::Percent,
                _=>return Err(err(p,"unsupported compound assignment"))};
            Self::compute(old.clone(),binary,rhs,p)?
        };
        if !self.value_matches(&result,&hint){return Err(err(p,"assignment type mismatch"));}
        *old=result;
        slot.move_paths.mark_path_initialized(&prefix);
        drop(slot);
        self.record_checked_access(token,&owner,place,PlaceAccessKind::Write);
        Ok(())
    }
    fn borrow_nested(&mut self,name:&str,names:&[String],exclusive:bool,p:Position)
        ->Result<ConstValue,Diagnostic>{
        let source=self.cell(name)?;
        let parent={let slot=source.borrow();match slot.val.as_ref(){
            Some(ConstValue::Ref(r))=>Some(r.clone()),_=>None
        }};
        if let Some(parent)=parent {
            if exclusive && !parent.0.mutable {
                return Err(err(p,"cannot mutably reborrow a shared reference"));
            }
            if parent.0.active_exclusive_child.get() ||
                (exclusive && parent.0.active_children.get()!=0){
                return Err(err(p,"reference is already reborrowed"));
            }
            let mut fields=parent.0.place.indices().to_vec();
            let owner=parent.0.owner.borrow();
            if !owner.alive{return Err(err(p,"dangling reference"));}
            let root=owner.val.as_ref().ok_or_else(||err(p,"reference to moved owner"))?;
            let base=Self::nested_value(root,&fields)
                .ok_or_else(||err(p,"reference points to moved place"))?;
            let (suffix,ty)=self.nested_ids(base,names,p)?;
            fields.extend(suffix);
            if !owner.move_paths.path_initialized(&fields){return Err(err(p,"borrow of moved field"));}
            let place=Place::from_fields(&fields)
                .ok_or_else(||err(p,"field path depth exceeded"))?;
            drop(owner);
            if parent.0.mutable {
                parent.0.active_children.set(parent.0.active_children.get()+1);
                if exclusive{parent.0.active_exclusive_child.set(true);}
            }
            self.record_checked_access(self.cur.i.saturating_sub(1),&parent.0.owner,place,
                if exclusive{PlaceAccessKind::BorrowExclusive}else{PlaceAccessKind::BorrowShared});
            return Ok(ConstValue::Ref(RefValue(Rc::new(RefLease{
                owner:Rc::clone(&parent.0.owner),place,mutable:exclusive,
                item_type:ty,key:parent.0.key,parent:Some(Rc::clone(&parent.0)),registered:false,
                active_children:std::cell::Cell::new(0),
                active_exclusive_child:std::cell::Cell::new(false),return_origin_guards:RefCell::new(Vec::new()),
            }))));
        }
        let mut slot=source.borrow_mut();
        if !slot.alive{return Err(err(p,"borrow of expired owner"));}
        if exclusive && !slot.mutable{return Err(err(p,"cannot mutably borrow immutable owner"));}
        let root=slot.val.as_ref().ok_or_else(||err(p,"borrow of moved owner"))?;
        let (ids,ty)=self.nested_ids(root,names,p)?;
        if !slot.move_paths.path_initialized(&ids){return Err(err(p,"borrow of moved field"));}
        let place=Place::from_fields(&ids).ok_or_else(||err(p,"field path depth exceeded"))?;
        if slot.loans.iter().any(|(_,mutability,loan)|loan.overlaps(place) && (exclusive||*mutability)) {
            return Err(err(p,"conflicting shared/mutable borrow"));
        }
        let key=slot.next_loan;
        slot.next_loan=slot.next_loan.checked_add(1).ok_or_else(||err(p,"borrow ID overflow"))?;
        slot.loans.push((key,exclusive,place));
        drop(slot);
        self.record_checked_access(self.cur.i.saturating_sub(1),&source,place,
            if exclusive{PlaceAccessKind::BorrowExclusive}else{PlaceAccessKind::BorrowShared});
        Ok(ConstValue::Ref(RefValue(Rc::new(RefLease{owner:source,place,mutable:exclusive,
            item_type:ty,key,parent:None,registered:true,
            active_children:std::cell::Cell::new(0),active_exclusive_child:std::cell::Cell::new(false),return_origin_guards:RefCell::new(Vec::new())}))))
    }

    fn copy_field(&mut self,owner:&str,field:&str,p:Position)->Result<ConstValue,Diagnostic>{
        let cell=self.cell(owner)?;
        let referent={let slot=cell.borrow();match slot.val.as_ref(){
            Some(ConstValue::Ref(reference))=>Some(reference.clone()),_=>None
        }};
        if let Some(reference)=referent {
            if reference.0.active_children.get()!=0 {
                return Err(err(p,"reference suspended by reborrow"));
            }
            let source=reference.0.owner.borrow();
            if !source.alive{return Err(err(p,"dangling reference"));}
            let root=source.val.as_ref().ok_or_else(||err(p,"reference to moved owner"))?;
            let mut path=reference.0.place.indices().to_vec();
            if !source.move_paths.path_initialized(&path) {
                return Err(err(p,"use of moved field"));
            }
            let parent=Self::nested_value(root,&path)
                .ok_or_else(||err(p,"reference points to uninitialized payload"))?;
            let ConstValue::Struct(id,values)=parent else {
                return Err(err(p,"field access requires struct"));
            };
            let index=self.field_id(*id,field).ok_or_else(||err(p,"unknown struct field"))?;
            path.push(index);
            if !source.move_paths.path_initialized(&path) {
                return Err(err(p,"use of moved field"));
            }
            let selected=values.get(index.0 as usize)
                .ok_or_else(||err(p,"unknown struct field"))?;
            if !selected.is_copy() {
                return Err(err(p,"cannot move non-Copy field out of a reference"));
            }
            let result=selected.clone();
            let place=Place::from_fields(&path)
                .ok_or_else(||err(p,"field path depth exceeded"))?;
            drop(source);
            self.record_checked_access(self.cur.i.saturating_sub(1),&reference.0.owner,
                place,PlaceAccessKind::Read);
            return Ok(result);
        }
        let mut source=cell.borrow_mut();
        let Some(ConstValue::Struct(id,_))=source.val.as_ref() else {
            return if source.val.is_none(){Err(err(p,format!("use of moved value '{owner}'")))}
                else{Err(err(p,"field access requires struct"))};
        };
        let index=self.field_id(*id,field).ok_or_else(||err(p,"unknown struct field"))?;
        if !source.move_paths.field_initialized(index){return Err(err(p,"use of moved field"));}
        let (is_copy,ty)={
            let ConstValue::Struct(_,fields)=source.val.as_ref().unwrap()else{unreachable!()};
            let selected=&fields[index.0 as usize];
            (selected.is_copy(),selected.ty())
        };
        let place=Place::Field(index);
        if source.loans.iter().any(|(_,is_mut,f)|f.overlaps(place)&&(!is_copy||*is_mut)) {
            return Err(err(p,if is_copy{"cannot read field during mutable borrow"}
                else{"cannot move field while borrowed"}));
        }
        let output=if is_copy {
            let ConstValue::Struct(_,fields)=source.val.as_ref().unwrap()else{unreachable!()};
            fields[index.0 as usize].clone()
        } else {
            if ty==ConstType::Unit {return Err(err(p,"cannot move uninitialized field"));}
            let ConstValue::Struct(_,fields)=source.val.as_mut().unwrap()else{unreachable!()};
            let moved=std::mem::replace(&mut fields[index.0 as usize],ConstValue::Unit);
            let changed=source.move_paths.mark_moved(index);
            debug_assert!(changed);
            moved
        };
        drop(source);
        self.record_checked_access(self.cur.i.saturating_sub(1),&cell,place,
            if is_copy{PlaceAccessKind::Read}else{PlaceAccessKind::Move});
        Ok(output)
    }
    fn take(&mut self,name:&str)->Result<ConstValue,Diagnostic>{
        let p=self.cur.pos();let cell=self.cell(name)?;
        let mut slot=cell.borrow_mut();
        if !slot.alive{return Err(err(p,"use of expired binding"));}
        let val=slot.val.as_ref().ok_or_else(||err(p,format!("use of moved value '{name}'")))?;
        if !slot.move_paths.whole_initialized(){return Err(err(p,"use of partially moved value"));}
        if val.is_copy(){
            if slot.loans.iter().any(|(_,is_mut,_)|*is_mut){return Err(err(p,"read during mutable borrow"));}
            let copied=val.clone();
            drop(slot);
            self.record_checked_access(self.cur.i.saturating_sub(1),&cell,
                Place::Root,PlaceAccessKind::Read);
            return Ok(copied);
        }
        if !slot.loans.is_empty() {
            let _cfg_conflict=self.verified_edge_conflict(name,self.cur.i.saturating_sub(1),
                Place::Root,PlaceAccessKind::Move,&slot);
            return Err(err(p,"cannot move value while borrowed"));
        }
        let moved=slot.val.take().ok_or_else(||err(p,"value already moved"))?;
        drop(slot);
        self.record_checked_access(self.cur.i.saturating_sub(1),&cell,
            Place::Root,PlaceAccessKind::Move);
        Ok(moved)
    }
    fn declare_symbol(&mut self,name:String,val:ConstValue,mutable:bool,symbol:SymbolId)->Result<(),Diagnostic>{
        let p=self.cur.pos();
        if self.quantum_names.contains(&name){return Err(err(p,"typed name conflicts with a quantum name"));}
        let typed_loan=if !self.flow_stack.is_empty(){
            match &val {ConstValue::Ref(r)=>self.typed_place_of(&r.0.owner,r.0.place),_=>None}
        }else{None};
        let parent_loan=match &val {
            ConstValue::Ref(r)=>r.0.parent.as_ref().and_then(|parent|self.scopes.iter()
                .rev().flat_map(|scope|scope.values()).find_map(|slot|{
                    let current=slot.cell.borrow();
                    match current.val.as_ref(){
                        Some(ConstValue::Ref(stored)) if Rc::ptr_eq(&stored.0,parent)=>Some(slot.symbol),
                        _=>None,
                    }
                })),
            _=>None,
        };
        let nested_loan=match &val {
            ConstValue::Ref(r)=>self.typed_path_of(&r.0.owner,r.0.place)
                .map(|path|(path,r.0.mutable)),
            _=>None,
        };
        let scope=self.scopes.last_mut().unwrap();
        if scope.contains_key(&name){return Err(err(p,format!("duplicate binding '{name}'")));}
        let cell=Rc::new(RefCell::new(RefSlot{val:Some(val),mutable,alive:true,loans:Vec::new(),next_loan:0,move_paths:crate::ir::MovePathState::default()}));
        scope.insert(name,Slot{cell,symbol,pattern_loan:false});
        if let Some(flow)=self.flow_stack.last_mut(){
            if let Some(place)=typed_loan{flow.register_typed_loan(symbol,place);}
            if let Some((place,exclusive))=nested_loan {
                flow.record_verified_loan(symbol,self.cur.i.saturating_sub(1),place,exclusive,parent_loan);
            }
        }
        Ok(())
    }
    fn assign_place(&mut self,name:&str,field:Option<&str>,deref:bool,operator:K<'a>,rhs:ConstValue,p:Position,token:usize)->Result<(),Diagnostic>{
        let source=self.cell(name)?;
        let reference=if deref||field.is_some(){
            let slot=source.borrow();match slot.val.as_ref(){Some(ConstValue::Ref(r))=>Some(r.clone()),_=>None}
        }else{None};
        let target=reference.as_ref().map_or_else(||Rc::clone(&source),|r|Rc::clone(&r.0.owner));
        //A reference into a nested place must never silently overwrite its root. The caller has already
        //type-checked the RHS against &mut T
        if deref && reference.as_ref().is_some_and(|r|r.0.place.indices().len()>1) {
            let r=reference.as_ref().unwrap();
            if !r.0.mutable{return Err(err(p,"assignment requires &mut T"));}
            if r.0.active_children.get()!=0{return Err(err(p,"reference suspended by reborrow"));}
            let path=r.0.place.indices().to_vec();
            let mut slot=target.borrow_mut();
            if !slot.alive{return Err(err(p,"assignment through dangling reference"));}
            if slot.loans.iter().any(|(key,_,loan)|
                *key!=r.0.key && !r.0.owns_return_origin_guard(&target,*key) &&
                loan.overlaps(r.0.place)) {
                return Err(err(p,"cannot assign while place is borrowed"));
            }
            if !slot.move_paths.ancestors_present(&path){return Err(err(p,"uninitialized parent"));}
            let was_moved=!slot.move_paths.path_initialized(&path);
            if was_moved && operator!=K::Equal{return Err(err(p,"compound assignment to moved field"));}
            let old=slot.val.as_mut().and_then(|v|Self::nested_value_mut(v,&path))
                .ok_or_else(||err(p,"invalid reference path"))?;
            let hint=r.0.item_type.clone();
            let result=if operator==K::Equal{rhs}else{
                let binary=match operator{K::PlusEq=>K::Plus,K::MinusEq=>K::Minus,
                    K::StarEq=>K::Star,K::SlashEq=>K::Slash,K::PercentEq=>K::Percent,
                    _=>return Err(err(p,"unsupported compound assignment"))};
                Self::compute(old.clone(),binary,rhs,p)?
            };
            if !self.value_matches(&result,&hint){return Err(err(p,"assignment type mismatch"));}
            *old=result;
            slot.move_paths.mark_path_initialized(&path);
            drop(slot);
            self.record_checked_access(token,&target,r.0.place,PlaceAccessKind::Write);
            return Ok(());
        }
        let mut slot=target.borrow_mut();
        if !slot.alive{return Err(err(p,"assignment through dangling reference"));}
        if let Some(r)=reference.as_ref(){
            if r.0.active_children.get()!=0{return Err(err(p,"reference suspended by reborrow"));}
            if !r.0.mutable{return Err(err(p,"assignment requires &mut T"));}
        }
        else if !slot.mutable{return Err(err(p,"cannot assign to immutable variable"));}
        if !deref && field.is_none() {
            if let Some(ConstValue::Ref(old))=slot.val.as_ref() {
                if old.0.active_children.get()!=0 {
                    return Err(err(p,"cannot reassign reference with live reborrow"));
                }
            }
        }
        let field_id=if let Some(name)=field {
            let Some(ConstValue::Struct(id,_))=slot.val.as_ref()else{return Err(err(p,"field assignment requires struct"));};
            Some(self.field_id(*id,name).ok_or_else(||err(p,"unknown struct field"))?)
        } else {reference.as_ref().and_then(|r|r.0.place.field())};
        if slot.loans.iter().any(|(key,_,f)|f.overlaps(Place::from_field(field_id)) &&
            reference.as_ref().map_or(true,|r|r.0.key!=*key &&
                !r.0.owns_return_origin_guard(&target,*key))) {
            if reference.is_none() {
                let _cfg_conflict=self.verified_edge_conflict(name,self.cur.i.saturating_sub(1),
                    Place::from_field(field_id),PlaceAccessKind::Write,&slot);
            }
            return Err(err(p,"cannot assign while place is borrowed"));
        }
        let Some(value)=slot.val.as_ref()else{return Err(err(p,"assignment to moved value"));};
        let was_moved=field_id.is_some_and(|f|!slot.move_paths.field_initialized(f));
        if was_moved && operator!=K::Equal {
            return Err(err(p,"compound assignment to moved field"));
        }
        if field_id.is_none() && !slot.move_paths.whole_initialized() && operator!=K::Equal {
            return Err(err(p,"compound assignment to partially moved value"));
        }
        let field_schema=match (field_id,value){
            (Some(fid),ConstValue::Struct(id,_))=>self.declared_field_type(*id,fid),
            (Some(fid),ConstValue::EnumData(id,variant,_)) if
                fid.0&0x8000_0000!=0 && ((fid.0>>4)&0x7f)==variant.0=>{
                let owner=self.type_names.get(id.0 as usize);
                owner.and_then(|owner|self.enum_payloads.get(owner)).and_then(|variants|
                    variants.get(variant.0 as usize)).and_then(|fields|
                    fields.get((fid.0&0xf) as usize)).cloned()
            },
            _=>None,
        };
        let value=slot.val.as_mut().unwrap();
        let old=if let Some(fid)=field_id {
            match value {
                ConstValue::Struct(_,values)=>values.get_mut(fid.0 as usize),
                ConstValue::EnumData(_,variant,values) if fid.0&0x8000_0000!=0 &&
                    ((fid.0>>4)&0x7f)==variant.0=>values.get_mut((fid.0&0xf) as usize),
                _=>None,
            }.ok_or_else(||err(p,"field assignment requires an initialized typed place"))?
        } else {value};
        let old_ty=if was_moved {field_schema.ok_or_else(||err(p,"unknown moved field type"))?}
            else{old.ty()};
        let result=if operator==K::Equal{rhs}else{
            let binary=match operator{K::PlusEq=>K::Plus,K::MinusEq=>K::Minus,K::StarEq=>K::Star,
                K::SlashEq=>K::Slash,K::PercentEq=>K::Percent,_=>return Err(err(p,"unsupported compound assignment"))};
            Self::compute(old.clone(),binary,rhs,p)?
        };
        if !self.value_matches(&result,&old_ty){return Err(err(p,"assignment type mismatch"));}
        *old=result;
        if let Some(field)=field_id{slot.move_paths.mark_initialized(field);}
        else{slot.move_paths.initialize_whole();}
        drop(slot);
        self.record_checked_access(token,&target,Place::from_field(field_id),PlaceAccessKind::Write);
        Ok(())
    }
    fn assignment_hint(&self,name:&str,field:Option<&str>,deref:bool)->Result<ConstType,Diagnostic>{
        let p=self.cur.pos();let cell=self.cell(name)?;
        let slot=cell.borrow();
        let val=slot.val.as_ref().ok_or_else(||err(p,"assignment to moved value"))?;
        if deref {
            let ConstValue::Ref(reference)=val else{return Err(err(p,"dereference requires reference"));};
            return Ok(reference.0.item_type.clone());
        }
        if let Some(field)=field {
            let reference=if let ConstValue::Ref(reference)=val{Some(reference.clone())}else{None};
            let target=reference.as_ref().map_or_else(||Rc::clone(&cell),|r|Rc::clone(&r.0.owner));
            drop(slot);
            let owner=target.borrow();
            let Some(ConstValue::Struct(id,fields))=owner.val.as_ref()else{return Err(err(p,"field assignment requires struct"));};
            let index=self.field_id(*id,field).ok_or_else(||err(p,"unknown struct field"))?;
            if !owner.move_paths.field_initialized(index) {
                return self.declared_field_type(*id,index).ok_or_else(||err(p,"unknown field type"));
            }
            return Ok(fields[index.0 as usize].ty());
        }
        Ok(val.ty())
    }
    fn try_assignment(&mut self)->Result<bool,Diagnostic>{
        let start=self.cur.i;let p=self.cur.pos();
        let deref=self.cur.eat(K::Star);
        let name=match self.cur.peek(){Some(K::Ident(s))=>{self.cur.i+=1;s.to_owned()},_=>{self.cur.i=start;return Ok(false)}};
        let mut fields=Vec::<String>::new();
        if !deref {while self.cur.eat(K::Dot){fields.push(self.cur.word()?);}}
        let field=fields.first().cloned();
        let op=self.cur.peek();
        if !matches!(op,Some(K::Equal|K::PlusEq|K::MinusEq|K::StarEq|K::SlashEq|K::PercentEq)){
            self.cur.i=start;return Ok(false);
        }
        if !self.scopes.iter().any(|scope|scope.contains_key(&name)){
            self.cur.i=start;return Ok(false);
        }
        let deep=fields.len()>1 || (!fields.is_empty() && self.cell(&name).ok()
            .is_some_and(|cell|matches!(cell.borrow().val.as_ref(),Some(ConstValue::Ref(_)))));
        let hint=if deep {self.nested_hint(&name,&fields,p)?}
            else{self.assignment_hint(&name,field.as_deref(),deref)?};
        self.cur.i+=1;
        let rhs=self.expr(Some(&hint),0,0)?;
        self.cur.need(K::Semi,"expected ';' after assignment")?;
        if deep {self.assign_nested(&name,&fields,op.unwrap(),rhs,p,start)?;}
        else{self.assign_place(&name,field.as_deref(),deref,op.unwrap(),rhs,p,start)?;}
        Ok(true)
    }
    fn compute(a:ConstValue,op:K<'a>,b:ConstValue,at:Position)->Result<ConstValue,Diagnostic>{
        if matches!(op,K::EqEq|K::NotEq) {
            if matches!(&a,ConstValue::Ref(_))||matches!(&b,ConstValue::Ref(_)) {
                return Err(err(at,"reference equality needs explicit comparison semantics"));
            }
            if a.ty()!=b.ty(){return Err(err(at,"equality requires same type"));}
            return Ok(ConstValue::Bool(if op==K::EqEq{a==b}else{a!=b}));
        }
        if matches!(op,K::AndAnd|K::OrOr){
            if let (ConstValue::Bool(l),ConstValue::Bool(r))=(a,b){return Ok(ConstValue::Bool(if op==K::AndAnd{l&&r}else{l||r}));}
            return Err(err(at,"logical operators require bool"));
        }
        match (a,b){
            (ConstValue::I64(l),ConstValue::I64(r))=>{
                let v=match op{K::Plus=>l.checked_add(r),K::Minus=>l.checked_sub(r),K::Star=>l.checked_mul(r),
                    K::Slash=>l.checked_div(r),K::Percent=>l.checked_rem(r),
                    K::Less=>return Ok(ConstValue::Bool(l<r)),K::LessEq=>return Ok(ConstValue::Bool(l<=r)),
                    K::Greater=>return Ok(ConstValue::Bool(l>r)),K::GreaterEq=>return Ok(ConstValue::Bool(l>=r)),
                    _=>return Err(err(at,"unsupported signed integer operation"))};
                Ok(ConstValue::I64(v.ok_or_else(||err(at,"i64 overflow or division by zero"))?))
            }
            (ConstValue::U64(l),ConstValue::U64(r))=>{
                let v=match op{K::Plus=>l.checked_add(r),K::Minus=>l.checked_sub(r),K::Star=>l.checked_mul(r),
                    K::Slash=>l.checked_div(r),K::Percent=>l.checked_rem(r),
                    K::Less=>return Ok(ConstValue::Bool(l<r)),K::LessEq=>return Ok(ConstValue::Bool(l<=r)),
                    K::Greater=>return Ok(ConstValue::Bool(l>r)),K::GreaterEq=>return Ok(ConstValue::Bool(l>=r)),
                    _=>return Err(err(at,"unsupported unsigned integer operation"))};
                Ok(ConstValue::U64(v.ok_or_else(||err(at,"u64 overflow or division by zero"))?))
            }
            _=>Err(err(at,"operator requires matching scalar types")),
        }
    }
    fn binding(op:K<'a>)->Option<u8>{Some(match op{
        K::OrOr=>1,K::AndAnd=>2,K::EqEq|K::NotEq=>3,K::Less|K::LessEq|K::Greater|K::GreaterEq=>4,
        K::Plus|K::Minus=>5,K::Star|K::Slash|K::Percent=>6,_=>return None})}
    fn digits(raw:&'a str)->Cow<'a, str>{
        if raw.contains('_'){Cow::Owned(raw.replace('_',""))}else{Cow::Borrowed(raw)}
    }
    fn postfix_value(&mut self,mut val:ConstValue,depth:usize,p:Position)->Result<ConstValue,Diagnostic>{
        loop{
            if !self.cur.eat(K::Dot){break;}
            let field=self.cur.word()?;
            if self.cur.peek()==Some(K::LParen){
                val=self.call(&field,Some(val),depth+1)?;
            }else{
                let ConstValue::Struct(id,values)=val else{return Err(err(p,"field access requires struct"));};
                let index=self.field_id(id,&field).ok_or_else(||err(p,"unknown struct field"))?;
                val=values.into_iter().nth(index.0 as usize)
                    .ok_or_else(||err(p,"unknown struct field"))?;
            }
        }
        Ok(val)
    }
    fn literal(&mut self,hint:Option<&ConstType>, depth:usize)->Result<ConstValue,Diagnostic>{
        if depth>64{return Err(err(self.cur.pos(),"typed expression recursion limit"));}
        let p=self.cur.pos();
        if self.cur.eat(K::Amp){
            let exclusive=self.cur.eat(K::Ident("mut"));
            if self.cur.eat(K::Star){
                let name=self.cur.word_borrowed()?;
                let cell=self.cell(name)?;
                let parent={let slot=cell.borrow();match slot.val.as_ref(){
                    Some(ConstValue::Ref(reference))=>reference.clone(),
                    _=>return Err(err(p,"&* requires a reference")),
                }};
                return self.reborrow_reference(parent,None,exclusive,true,p);
            }
            let name=self.cur.word_borrowed()?;
            let mut fields=Vec::new();
            while self.cur.eat(K::Dot){fields.push(self.cur.word()?);}
            if fields.len()>1{return self.borrow_nested(name,&fields,exclusive,p);}
            return self.borrow_place(name,fields.first().map(String::as_str),exclusive);
        }
        if self.cur.eat(K::Star){
            let mut levels=1usize;
            while self.cur.eat(K::Star) {
                levels+=1;
                if levels>16 {return Err(err(p,"dereference nesting limit exceeded"));}
            }
            let name=self.cur.word_borrowed()?;
            return self.deref_value(name,levels);
        }
        if self.cur.eat(K::Minus){
            if let Some(K::Number(n))=self.cur.peek(){
                let digits=Self::digits(n);let v=digits.parse::<i128>().map_err(|_|err(p,"integer literal too large"))?;
                self.cur.i+=1;
                let neg=v.checked_neg().ok_or_else(||err(p,"integer overflow"))?;
                return match hint{Some(ConstType::U64)=>Err(err(p,"cannot negate u64")),
                    _=>Ok(ConstValue::I64(i64::try_from(neg).map_err(|_|err(p,"i64 overflow"))?))};
            }
            let v=self.literal(hint,depth+1)?;
            return match v {ConstValue::I64(i)=>Ok(ConstValue::I64(i.checked_neg().ok_or_else(||err(p,"i64 overflow"))?)),
                _=>Err(err(p,"unary '-' requires i64"))};
        }
        if self.cur.eat(K::Bang){return match self.literal(hint,depth+1)?{
            ConstValue::Bool(b)=>Ok(ConstValue::Bool(!b)),_=>Err(err(p,"unary '!' requires bool"))};}
        if self.cur.eat(K::LParen){let v=self.expr(hint,0,depth+1)?;self.cur.need(K::RParen,"expected ')'")?;return Ok(v);}
        if let Some(K::Number(raw))=self.cur.peek(){
            let cleaned=Self::digits(raw);
            if cleaned.bytes().any(|b| matches!(b,b'.'|b'e'|b'E')) {return Err(err(p,"typed integer literal cannot be floating-point"));}
            self.cur.i+=1;
            return if hint==Some(&ConstType::U64){Ok(ConstValue::U64(cleaned.parse().map_err(|_|err(p,"u64 overflow"))?))}
                else{Ok(ConstValue::I64(cleaned.parse().map_err(|_|err(p,"i64 overflow"))?))};
        }
        let word=self.cur.word_borrowed()?;
        if word=="true"{return Ok(ConstValue::Bool(true));}
        if word=="false"{return Ok(ConstValue::Bool(false));}
        if self.cur.eat(K::Colon){
            self.cur.need(K::Colon,"expected '::'")?;
            let variant=self.cur.word_borrowed()?;
            if let Some(v)=self.enums.get(word){
                let index=v.iter().position(|candidate| candidate.as_str()==variant)
                    .ok_or_else(||err(p,"unknown enum variant"))?;
                let type_id=*self.type_ids.get(word).expect("registered enum");
                let fields=self.enum_payloads.get(word)
                    .and_then(|variants|variants.get(index)).cloned()
                    .ok_or_else(||err(p,"enum payload schema is missing"))?;
                if fields.is_empty(){
                    if self.cur.peek()==Some(K::LParen){
                        return Err(err(p,"unit enum variant does not accept payload"));
                    }
                    return Ok(ConstValue::Enum(type_id,VariantId(index as u32)));
                }
                self.cur.need(K::LParen,"tuple enum variant requires '(...)' payload")?;
                let mut values=Vec::with_capacity(fields.len());
                for (i,field_ty) in fields.iter().enumerate(){
                    if i!=0{self.cur.need(K::Comma,"expected ',' between enum payloads")?;}
                    let value=self.expr(Some(field_ty),0,depth+1)?;
                    if !self.value_matches(&value,field_ty){
                        return Err(err(p,"enum payload type mismatch"));
                    }
                    values.push(value);
                }
                self.cur.eat(K::Comma);
                self.cur.need(K::RParen,"enum payload arity mismatch")?;
                return Ok(ConstValue::EnumData(type_id,VariantId(index as u32),values));
            }
            return Err(err(p,"unknown enum type"));
        }
        if self.cur.eat(K::LBrace){
            let field_count=self.types.get(word).ok_or_else(||err(p,"unknown struct type"))?.len();
            let id=*self.type_ids.get(word).expect("registered struct");
            let mut values=vec![ConstValue::Bool(false);field_count];
            let mut seen=0u128;
            while !self.cur.eat(K::RBrace){
                let key=self.cur.word_borrowed()?;
                self.cur.need(K::Colon,"expected ':' in struct initializer")?;
                let (field_id,ty)=self.types.get(word).and_then(|fields|fields.iter()
                    .enumerate().find(|(_, (name,_))|name.as_str()==key)
                    .map(|(i,(_,ty))|(FieldId(i as u32),ty.clone())))
                    .ok_or_else(||err(p,"unknown struct field"))?;
                let mask=1u128 << field_id.0;
                if seen & mask != 0{return Err(err(p,"duplicate struct initializer field"));}
                let val=self.expr(Some(&ty),0,depth+1)?;
                if !self.value_matches(&val,&ty){return Err(err(p,"struct field type mismatch"));}
                values[field_id.0 as usize]=val;
                seen |= mask;
                if !self.cur.eat(K::RBrace){self.cur.need(K::Comma,"expected ','")?;}else{break;}
            }
            if seen.count_ones() as usize != field_count{return Err(err(p,"missing struct initializer field"));}
            //A temporary struct is an expression, so `.field` and subsequent postfix operations must be parsed
            //before returning to the caller
            return self.postfix_value(ConstValue::Struct(id,values),depth,p);
        }
        let borrowed_receiver=if self.cur.peek()==Some(K::Dot)&&
            matches!(self.cur.ahead(1),Some(K::Ident(_))) && self.cur.ahead(2)==Some(K::LParen){
            let cell=self.cell(word)?;
            let owner_type={let slot=cell.borrow();match slot.val.as_ref(){
                Some(ConstValue::Struct(id,_))=>Some(*id),
                Some(ConstValue::Ref(r))=>match &r.0.item_type{ConstType::Resolved(id)=>Some(*id),_=>None},
                _=>None,
            }};
            if let (Some(owner),Some(K::Ident(method)))=(owner_type,self.cur.ahead(1)){
                self.methods.get(&owner).and_then(|m|m.get(method)).and_then(|id|self.fn_defs.get(id.0 as usize))
                    .and_then(|f|f.params.first()).map(|(_,ty)|match ty{
                        ConstType::Ref(_)=>Some(false),ConstType::RefMut(_)=>Some(true),_=>None,
                    }).flatten()
            }else{None}
        }else{None};
        let val=if let Some(exclusive)=borrowed_receiver {
            let existing={let cell=self.cell(word)?;let slot=cell.borrow();
                match slot.val.as_ref(){Some(ConstValue::Ref(r))=>Some(r.clone()),_=>None}};
            if let Some(reference)=existing {
                if reference.0.active_children.get()!=0{return Err(err(p,"reference suspended by reborrow"));}
                if exclusive && !reference.0.mutable {return Err(err(p,"method requires &mut self"));}
                if exclusive {ConstValue::Ref(reference)}
                else if reference.0.mutable {self.reborrow_reference(reference,None,false,true,p)?}
                else {ConstValue::Ref(reference)}
            }else{self.borrow_place(word,None,exclusive)?}
        } else if self.cur.peek()==Some(K::LParen){
            self.call(word,None,depth+1)?
        } else if self.cur.peek()==Some(K::Dot) &&
            !matches!(self.cur.ahead(2),Some(K::LParen)) {
            self.cur.i+=1;
            let first=self.cur.word()?;
            let mut fields=vec![first];
            while self.cur.peek()==Some(K::Dot) && self.cur.ahead(2)!=Some(K::LParen){
                self.cur.i+=1;fields.push(self.cur.word()?);
            }
            if fields.len()==1 {
                let borrowed=self.cell(word).ok().is_some_and(|cell|{
                    matches!(cell.borrow().val.as_ref(),Some(ConstValue::Ref(_)))
                });
                if borrowed {self.access_nested_path(word,&fields,p)?}
                else {self.copy_field(word,&fields[0],p)?}
            }else{self.access_nested_path(word,&fields,p)?}
        } else {self.take(word)?};
        self.postfix_value(val,depth,p)
    }
    fn expr(&mut self,hint:Option<&ConstType>,min_bp:u8,depth:usize)->Result<ConstValue,Diagnostic>{
        let mut left=self.literal(hint,depth+1)?;
        while let Some(op)=self.cur.peek(){
            let Some(bp)=Self::binding(op)else{break;};if bp<min_bp{break;}
            let p=self.cur.pos();self.cur.i+=1;
            if matches!(op,K::AndAnd|K::OrOr) {
                return Err(err(p,"logical &&/|| in typed functions needs lazy typed evaluation; not yet supported"));
            }
            let right=self.expr(Some(&left.ty()),bp+1,depth+1)?;
            left=Self::compute(left,op,right,p)?;
        }
        Ok(left)
    }
    fn call_argument(&mut self,expected:&ConstType,depth:usize)->Result<ConstValue,Diagnostic>{
        if let Some(K::Ident(name))=self.cur.peek() {
            if matches!(self.cur.ahead(1),Some(K::Comma|K::RParen)) {
                let existing=self.cell(name).ok().and_then(|cell|{
                    let slot=cell.borrow();
                    match slot.val.as_ref(){Some(ConstValue::Ref(r))=>Some(r.clone()),_=>None}
                });
                if let Some(reference)=existing {
                    let target=self.resolved_type(expected);
                    let exclusive=match target {
                        ConstType::RefMut(inner) if (*inner==reference.0.item_type ||
                            matches!(inner.as_ref(),ConstType::Generic(_))) && reference.0.mutable => Some(true),
                        ConstType::Ref(inner) if *inner==reference.0.item_type ||
                            matches!(inner.as_ref(),ConstType::Generic(_))=>Some(false),
                        _=>None,
                    };
                    if let Some(exclusive)=exclusive {
                        let p=self.cur.pos();
                        let value=self.reborrow_reference(reference,None,exclusive,true,p)?;
                        self.cur.i+=1;
                        return Ok(value);
                    }
                }
            }
        }
        self.expr(Some(expected),0,depth)
    }
    fn check_return_region(signature:&RegionSignature, inputs:&[Option<crate::ir::RefValue>],
        result:&crate::ir::RefValue, at:Position)->Result<(),Diagnostic>{
        let Some(required)=signature.result else{return Ok(());};
        //Fast path for the overwhelmingly common one-reference identity call: same parent-chain proof, with no
        //temporary vectors or allocations
        if inputs.len()==1 {
            let region=signature.param.first().and_then(|r|*r);
            let source=inputs[0].as_ref();
            if let (Some(region),Some(source))=(region,source) {
                let mut lease=Some(Rc::clone(&result.0));
                while let Some(node)=lease {
                    if Rc::ptr_eq(&node,&source.0) {
                        return if signature.permits(region,required){Ok(())}else{
                            Err(err(at,"returned reference lifetime does not outlive declared return region"))
                        };
                    }
                    lease=node.parent.clone();
                }
            }
            return Err(err(at,"returned reference does not originate from a declared input lifetime"));
        }
        if inputs.len()>64 {return Err(err(at,"too many reference provenance sources"));}
        let mut origins=[0u64;64];
        let mut summary=0u64;
        for (index,source) in inputs.iter().enumerate() {
            let Some(source)=source else{continue;};
            origins[index]=1u64<<index;
            let mut lease=Some(Rc::clone(&result.0));
            while let Some(node)=lease {
                if Rc::ptr_eq(&node,&source.0) {
                    summary|=1u64<<index;
                    break;
                }
                lease=node.parent.clone();
            }
        }
        if summary==0 {
            return Err(err(at,"returned reference does not originate from a declared input lifetime"));
        }
        let mut solver=RegionConstraintSolver::new(signature);
        let returned=solver.instantiate_call_sources(summary,&origins[..inputs.len()])
            .map_err(|e|err(at,e))?;
        solver.solve_and_verify_return(returned).map_err(|e|err(at,e))
    }
    //A reference returned by a compile-time-selected branch must nevertheless protect *all* universally
    //proved field origins
    fn protect_fresh_return_sources(inputs:&[Option<RefValue>],
        fresh_borrowed:&[bool],returned:&RefValue,
        candidates:Option<&[ReferencePathOrigin]>,at:Position)
        ->Result<(),Diagnostic>{
        let exclusive=returned.0.mutable;
        let mut pending=Vec::<(Rc<RefCell<RefSlot>>,Place)>::new();
        let mut retired=Vec::<(Rc<RefCell<RefSlot>>,u64)>::new();
        for (index,(source,fresh)) in inputs.iter().zip(fresh_borrowed).enumerate() {
            if !fresh {continue;}
            let Some(source)=source else {continue;};
            if !source.0.registered || source.0.parent.is_some() {
                continue;
            }
            //A mutable result cannot be derived from a shared input. This also protects unsupported/incomplete
            //provenance certificates
            if exclusive && !source.0.mutable {continue;}
            let owner=Rc::clone(&source.0.owner);
            let borrowed=owner.borrow();
            if !borrowed.alive || borrowed.val.is_none() ||
                !borrowed.loans.iter().any(|(key,loan_mut,place)|
                    *key==source.0.key && *loan_mut==source.0.mutable &&
                    *place==source.0.place){
                return Err(err(at,"unverifiable returned-reference argument loan"));
            }
            let mut new_places=Vec::<Place>::new();
            if let Some(origins)=candidates {
                for origin in origins.iter().filter(|o|o.parameter==index) {
                    let mut fields=source.0.place.indices().to_vec();
                    let mut value=Self::nested_value(borrowed.val.as_ref().unwrap(),&fields)
                        .ok_or_else(||err(at,"invalid returned-reference root projection"))?;
                    for key in &origin.path {
                        let ConstValue::Struct(actual,values)=value else{
                            return Err(err(at,"returned reference projects non-struct data"));
                        };
                        if *actual!=key.aggregate {
                            return Err(err(at,"returned reference field belongs to another type"));
                        }
                        value=values.get(key.field.0 as usize)
                            .ok_or_else(||err(at,"returned reference has invalid field index"))?;
                        fields.push(key.field);
                    }
                    if !borrowed.move_paths.path_initialized(&fields){
                        return Err(err(at,"returned reference may target moved field"));
                    }
                    let path=Place::from_fields(&fields)
                        .ok_or_else(||err(at,"returned reference path depth exceeded"))?;
                    if !new_places.contains(&path){new_places.push(path);}
                }
            }else{
                new_places.push(source.0.place);
            }
            let selected_from_source={
                let mut node=Some(Rc::clone(&returned.0));
                let mut found=false;
                while let Some(lease)=node {
                    if Rc::ptr_eq(&lease,&source.0) {found=true;break;}
                    node=lease.parent.clone();
                }
                found
            };
            if selected_from_source && !new_places.iter().any(|place|
                place.overlaps(returned.0.place)) {
                return Err(err(at,"returned reference contradicts its proven origin set"));
            }
            if new_places.is_empty() {continue;}
            //A proof may name several fresh parameters, including an arm not executed on this invocation
            for place in new_places {pending.push((Rc::clone(&owner),place));}
            retired.push((Rc::clone(&owner),source.0.key));
        }
        let mut result_guards=returned.0.return_origin_guards.borrow_mut();
        for (owner,place) in pending {
            let mut slot=owner.borrow_mut();
            let key=slot.next_loan;
            slot.next_loan=slot.next_loan.checked_add(1)
                .ok_or_else(||err(at,"returned reference guard ID overflow"))?;
            slot.loans.push((key,exclusive,place));
            result_guards.push(ReturnOriginGuard{owner:Rc::clone(&owner),key});
        }
        for (owner,key) in retired {
            owner.borrow_mut().loans.retain(|(active,_,_)|*active!=key);
        }
        Ok(())
    }
    fn call(&mut self,name:&str,self_value:Option<ConstValue>,depth:usize)->Result<ConstValue,Diagnostic>{
        let p=self.cur.pos();self.cur.need(K::LParen,"expected '(' in function call")?;
        let id=match self_value.as_ref() {
            Some(ConstValue::Struct(owner,_)) => self.methods.get(owner)
                .and_then(|defs|defs.get(name)).copied(),
            Some(ConstValue::Ref(reference))=>match &reference.0.item_type {
                ConstType::Resolved(owner)=>self.methods.get(owner).and_then(|defs|defs.get(name)).copied(),
                _=>None,
            },
            Some(_) => None,
            None => self.functions.get(name).copied(),
        }
            .ok_or_else(||err(p,format!("unknown typed function '{name}'")))?;
        let fun=Rc::clone(&self.fn_defs[id.0 as usize]);
        let is_method=self_value.is_some();
        let mut args=Vec::with_capacity(fun.params.len());
        if let Some(v)=self_value{args.push(v);}
        let track_fresh_borrowed=fun.regions.is_some() &&
            matches!(fun.ret.as_ref(),Some(ConstType::Ref(_)|ConstType::RefMut(_)));
        let mut fresh_borrowed=Vec::new();
        if track_fresh_borrowed {fresh_borrowed.resize(args.len(),false);}
        let mut bindings=HashMap::<String,ConstType>::with_capacity(fun.generics.len());
        while !self.cur.eat(K::RParen){
            let i=args.len();if i>=fun.params.len(){return Err(err(p,"function arity mismatch"));}
            let ty=&fun.params[i].1;
            let instantiated=if fun.generics.is_empty(){None}
                else{Some(Self::instantiate(ty,&bindings))};
            let expected_ty=instantiated.as_ref().unwrap_or(ty);
            let hint=if Self::has_unbound(expected_ty){
                if matches!(expected_ty,ConstType::Ref(_)|ConstType::RefMut(_)){
                    Some(expected_ty)
                }else{None}
            }else{Some(expected_ty)};
            let argument_start=self.cur.i;
            let val=if let Some(expected)=hint {
                self.call_argument(expected,depth+1)?
            }else{self.expr(None,0,depth+1)?};
            if track_fresh_borrowed {
                fresh_borrowed.push(self.cur.tokens.get(argument_start)
                    .is_some_and(|token|token.kind==K::Amp) &&
                    matches!(&val,ConstValue::Ref(reference) if
                        reference.0.registered && reference.0.parent.is_none()));
            }
            if !fun.generics.is_empty(){
                Self::bind_type(ty,&val.ty(),&mut bindings).map_err(|e|err(p,e))?;
            }
            args.push(val);
            if !self.cur.eat(K::RParen){self.cur.need(K::Comma,"expected ','")?;}else{break;}
        }
        if args.len()!=fun.params.len(){return Err(err(p,"function arity mismatch"));}
        if let Some(signature)=fun.regions.as_ref(){
            if signature.static_return(){return Err(err(p,"'static reference return requires static storage, not yet supported"));}
            for (i,_) in args.iter().enumerate() {
                if signature.static_parameter(i){return Err(err(p,"'static argument requires static storage, not yet supported"));}
            }
        }
        for generic in &fun.generics {
            let Some(ty)=bindings.get(&generic.name)else{
                return Err(err(p,format!("cannot infer generic type {}",generic.name)));
            };
            for bound in &generic.bounds {
                if !Self::satisfies_builtin_trait(ty,bound){
                    return Err(err(p,format!("trait bound {}: {} is not satisfied",generic.name,bound)));
                }
            }
        }
        let region_inputs=if fun.regions.is_some(){Some(args.iter().map(|v|
            if let ConstValue::Ref(r)=v{Some(r.clone())}else{None}).collect::<Vec<_>>())}else{None};
        for (i,((_,ty),val)) in fun.params.iter().zip(args.iter()).enumerate(){
            let instantiated=if fun.generics.is_empty(){None}
                else{Some(Self::instantiate(ty,&bindings))};
            if !self.value_matches(val,instantiated.as_ref().unwrap_or(ty)){
                return Err(err(p,format!("parameter {} type mismatch",i+1)));
            }
        }
        let unit=ConstType::Unit;
        let ret=fun.ret.as_ref().unwrap_or(&unit);
        let expected=if fun.generics.is_empty(){ret.clone()}
            else{Self::instantiate(ret,&bindings)};
        if Self::has_unbound(&expected){return Err(err(p,"unresolved generic return"));}
        if self.calls>=48{return Err(err(p,"compile-time recursion limit reached"));}
        self.calls+=1;
        //Function calls have independent control-flow domains; a callee must not inherit the
        //caller's loop or return context
        let saved_loop_depth=std::mem::replace(&mut self.loop_depth,0);
        let saved_host_flow=self.host_flow.take();
        self.return_stack.push(expected.clone());
        let new_cursor=Cursor::view(Rc::clone(&self.cur.tokens),fun.body.clone());
        let old=std::mem::replace(&mut self.cur,new_cursor);
        self.push_scope();
        let parameter_base=self.cur.tokens.len();
        for (index,((param,_),val)) in fun.params.iter().zip(args).enumerate() {
            let symbol=SymbolId(u32::try_from(parameter_base+index+1)
                .map_err(|_|err(p,"parameter symbol index overflow"))?);
            self.declare_symbol(param.clone(),val,false,symbol)?;
        }
        self.start_flow(fun.body.clone(),true);
        let result=self.eval_body(if fun.ret.is_some(){Some(&expected)}else{None});
        self.flow_stack.pop();
        //Returning a borrow of a callee-local owner is invalid even if the returned reference is never
        //dereferenced by the caller
        let escaping=result.as_ref().ok().and_then(|value|value.as_ref()).and_then(|value|{
            if let ConstValue::Ref(reference)=value {Some(Rc::clone(&reference.0.owner))}else{None}
        });
        let local_escape=escaping.as_ref().is_some_and(|owner|self.scopes.last().unwrap().values()
            .any(|slot|Rc::ptr_eq(&slot.cell,owner)));
        let scope_result=self.pop_scope();self.cur=old;self.calls-=1;
        self.return_stack.pop();
        self.loop_depth=saved_loop_depth;
        self.host_flow=saved_host_flow;
        scope_result?;
        if local_escape{return Err(err(p,"reference escapes the lifetime of a local value"));}
        let value=result?.unwrap_or(ConstValue::Unit);
        if !self.value_matches(&value,&expected){return Err(err(p,"return type mismatch"));}
        if let (Some(signature),Some(inputs),ConstValue::Ref(reference))=
            (fun.regions.as_ref(),region_inputs.as_ref(),&value) {
            Self::check_return_region(signature,inputs,reference,p)?;
            //MIR's alternative PHI proof is universal, whereas runtime evaluation only visits the chosen branch
            let exact=if !is_method && fresh_borrowed.iter().any(|&fresh|fresh) {
                self.verified_return_paths.get(&fun.name).cloned().or_else(||{
                    let mut solver=ReferenceSummarySolver::new(&self.fn_defs,&self.cur.tokens,
                        &self.types,&self.type_ids,&self.type_names);
                    solver.projected(&fun.name).map(|paths|paths.to_vec()).or_else(||
                        effectful_return_field_origin(&mut solver,&fun).map(|origin|
                            vec![ReferencePathOrigin{parameter:origin.parameter,path:origin.fields}]))
                })
            }else{None};
            Self::protect_fresh_return_sources(inputs,&fresh_borrowed,
                reference,exact.as_deref(),p)?;
        }
        Ok(value)
    }
    fn reference_if_value(&mut self,expected:Option<&ConstType>)->Result<ConstValue,Diagnostic>{
        let p=self.cur.pos();
        let mut selected=None;
        loop {
            self.cur.need(K::Ident("if"),"expected if")?;
            let condition=self.condition_body_boundary()?;
            let value=self.boolean_condition(condition,"if")?;
            let body=self.cur.body()?;
            if value && selected.is_none(){selected=Some(body);}
            if !self.cur.eat(K::Ident("else")){return Err(err(p,"reference if expression requires else"));}
            if self.cur.peek()==Some(K::Ident("if")){continue;}
            let body=self.cur.body()?;
            if selected.is_none(){selected=Some(body);}
            break;
        }
        if self.cur.peek().is_some(){return Err(err(p,"unexpected tokens after reference if expression"));}
        let selected=selected.ok_or_else(||err(p,"reference if requires an exhaustive else"))?;
        let view=Cursor::view(Rc::clone(&self.cur.tokens),selected);
        let original=std::mem::replace(&mut self.cur,view);
        let result=(||{
            let value=self.expr(expected,0,0)?;
            if self.cur.peek().is_some(){return Err(err(p,"reference if arm must be a single expression"));}
            if !matches!(&value,ConstValue::Ref(_)) ||
                expected.is_some_and(|ty|!self.value_matches(&value,ty)) {
                return Err(err(p,"reference if arm type mismatch"));
            }
            Ok(value)
        })();
        self.cur=original;
        result
    }
    fn reference_match_value(&mut self,expected:&ConstType)->Result<ConstValue,Diagnostic>{
        let p=self.cur.pos();
        let arms=reference_match_tail_arms(&self.cur.tokens,self.cur.i..self.cur.end)
            .ok_or_else(||err(p,"unproved reference match expression"))?;
        let subject=self.cur.i+1;
        let selected=self.boolean_condition(subject..subject+1,"match")?;
        let arm=arms.iter().find(|(pattern,_)|*pattern==Some(selected))
            .or_else(||arms.iter().find(|(pattern,_)|pattern.is_none()))
            .ok_or_else(||err(p,"reference match has no selected arm"))?.1.clone();
        self.cur.i=self.cur.end;
        let view=Cursor::view(Rc::clone(&self.cur.tokens),arm);
        let original=std::mem::replace(&mut self.cur,view);
        let result=(||{
            let value=self.expr(Some(expected),0,0)?;
            if self.cur.peek().is_some(){return Err(err(p,"reference match arm must be a single expression"));}
            if !self.value_matches(&value,expected){return Err(err(p,"reference match arm type mismatch"));}
            Ok(value)
        })();
        self.cur=original;
        result
    }
    fn eval_body(&mut self,ret:Option<&ConstType>)->Result<Option<ConstValue>,Diagnostic>{
        while self.cur.peek().is_some(){
            if self.cur.eat(K::Ident("return")){
                let v=if self.cur.eat(K::Semi){None}else {
                    let value=self.expr(ret,0,0)?;
                    self.cur.need(K::Semi,"expected ';' after return")?;
                    Some(value)
                };
                if self.cur.peek().is_some(){return Err(err(self.cur.pos(),"unreachable code after return"));}
                return Ok(v);
            }
            if self.cur.peek()==Some(K::Ident("if")) {
                if let Some(expected)=ret {
                    if matches!(expected,ConstType::Ref(_)|ConstType::RefMut(_)) &&
                        reference_if_tail_arms(&self.cur.tokens,self.cur.i..self.cur.end).is_some() {
                        let value=self.reference_if_value(Some(expected))?;
                        return Ok(Some(value));
                    }
                }
                self.static_if()?;
            }
            else if self.cur.peek()==Some(K::Ident("match")) {
                if let Some(expected)=ret {
                    if matches!(expected,ConstType::Ref(_)|ConstType::RefMut(_)) &&
                        reference_match_tail_arms(&self.cur.tokens,self.cur.i..self.cur.end).is_some() {
                        let value=self.reference_match_value(expected)?;
                        return Ok(Some(value));
                    }
                }
                self.static_enum_match()?;
            }
            else if self.cur.peek()==Some(K::Ident("while")) {self.static_while()?;}
            else if self.cur.peek()==Some(K::Ident("for")) {self.static_for()?;}
            else if self.cur.peek()==Some(K::Ident("loop")) {self.static_loop()?;}
            else if matches!(self.cur.peek(),Some(K::Ident("break"|"continue"))) {
                self.parse_loop_exit()?;
            }
            else if self.cur.peek()==Some(K::Ident("let")) || self.cur.peek()==Some(K::Ident("const")) {
                self.typed_let()?;self.end_dead_local_borrows();continue;
            }
            else if self.try_assignment()? {  }
            else {
                let v=self.expr(ret,0,0)?;
                if !self.cur.eat(K::Semi){
                    if self.cur.peek().is_some(){return Err(err(self.cur.pos(),"expected end of function after tail expression"));}
                    return Ok(Some(v));
                }
            }
            match self.host_flow.take() {
                Some(HostFlow::Return(v))=>return Ok(v),
                Some(signal @ (HostFlow::Break|HostFlow::Continue))=>{
                    self.host_flow=Some(signal);return Ok(None);
                }
                None=>self.end_dead_local_borrows(),
            }
        }
        Ok(None)
    }
    fn disjunctive_shared_reference_if_initializer(&mut self,hint:Option<&ConstType>)
        ->Result<ConstValue,Diagnostic>{
        let start=self.cur.i;
        let p=self.cur.pos();
        let mut end=start;
        let mut braces=0usize;
        while end<self.cur.end {
            match self.cur.tokens[end].kind {
                K::LBrace=>braces+=1,
                K::RBrace=>{
                    if braces==0 {return Err(err(p,"invalid reference if initializer"));}
                    braces-=1;
                }
                K::Semi if braces==0=>break,
                _=>(),
            }
            end+=1;
        }
        if braces!=0 || end==self.cur.end {
            return Err(err(p,"reference if initializer requires a terminating ';'"));
        }
        let arms=reference_if_tail_arms(&self.cur.tokens,start..end)
            .ok_or_else(||err(p,"reference if initializer requires exhaustive, expression-only arms"))?;
        //Every arm must be a side-effect-free explicit shared borrow `&owner(.field)*`
        let mut places=Vec::new();
        for (_,arm) in &arms {
            let candidate=&self.cur.tokens[arm.clone()];
            if candidate.len()<2 || candidate[0].kind!=K::Amp ||
                (candidate.len()-2)%2!=0 ||
                !candidate[2..].chunks_exact(2).all(|pair|
                    pair[0].kind==K::Dot && matches!(pair[1].kind,K::Ident(_))) {
                return Err(err(p,"reference if initializer requires simple shared-borrow origins"));
            }
            let K::Ident(name)=candidate[1].kind else {
                return Err(err(p,"reference if initializer requires simple shared-borrow origins"));
            };
            if name=="mut" {
                return Err(err(p,"reference if initializer requires simple shared-borrow origins"));
            }
            let names=candidate.iter().skip(3).step_by(2).filter_map(|token|
                match token.kind {K::Ident(field)=>Some(field.to_owned()),_=>None}
            ).collect::<Vec<_>>();
            let source=self.cell(name)?;
            let owner=source.borrow();
            if !owner.alive || owner.val.is_none() ||
                matches!(owner.val.as_ref(),Some(ConstValue::Ref(_))) {
                return Err(err(p,"reference if origin is not a live owned value"));
            }
            let (fields,ty)=self.nested_ids(owner.val.as_ref().unwrap(),&names,p)?;
            if !owner.move_paths.path_initialized(&fields) {
                return Err(err(p,"reference if origin is moved or uninitialized"));
            }
            let place=Place::from_fields(&fields)
                .ok_or_else(||err(p,"reference if origin path too deep"))?;
            places.push((Rc::clone(&source),place,ty));
        }
        if places.len()>32 {return Err(err(p,"too many reference PHI alternatives"));}
        let view=Cursor::view(Rc::clone(&self.cur.tokens),start..end);
        let old=std::mem::replace(&mut self.cur,view);
        let result=self.reference_if_value(hint);
        self.cur=old;
        self.cur.i=end; //leave semicolon to typed_let
        let result=result?;
        let ConstValue::Ref(selected)=&result else {
            return Err(err(p,"reference if initializer requires a shared reference"));
        };
        if selected.0.mutable || places.iter().any(|(_,_,ty)|ty!=&selected.0.item_type) ||
            !places.iter().any(|(owner,place,_)|
                Rc::ptr_eq(owner,&selected.0.owner) && *place==selected.0.place) {
            return Err(err(p,"reference if initializer has inconsistent PHI provenance or type"));
        }
        //Validate all candidates before creating any guard. An exclusive independent borrow of ANY inactive
        //source must reject the join
        let mut guards=Vec::new();
        for (owner,place,_) in places {
            if Rc::ptr_eq(&owner,&selected.0.owner) && place==selected.0.place {
                continue;
            }
            if guards.iter().any(|(seen,p):&(Rc<RefCell<RefSlot>>,Place)|
                Rc::ptr_eq(seen,&owner) && *p==place) {continue;}
            let slot=owner.borrow();
            if slot.loans.iter().any(|(_,exclusive,locked)|
                *exclusive && locked.overlaps(place)) {
                return Err(err(p,"reference PHI alternative conflicts with mutable borrow"));
            }
            guards.push((Rc::clone(&owner),place));
        }
        let mut acquired=Vec::new();
        for (owner,place) in guards {
            let key={
                let mut slot=owner.borrow_mut();
                let key=slot.next_loan;
                slot.next_loan=slot.next_loan.checked_add(1)
                    .ok_or_else(||err(p,"reference PHI guard ID overflow"))?;
                slot.loans.push((key,false,place));
                key
            }; //Release the RefMut before moving its owning Rc into the guard
            acquired.push(ReturnOriginGuard{owner,key});
        }
        selected.0.return_origin_guards.borrow_mut().extend(acquired);
        Ok(result)
    }
    fn typed_let(&mut self)->Result<(),Diagnostic>{
        let is_const=self.cur.eat(K::Ident("const"));if !is_const{self.cur.need(K::Ident("let"),"expected let")?;}
        let mutable=self.cur.eat(K::Ident("mut"));
        if mutable&&is_const{return Err(err(self.cur.pos(),"const cannot be mutable"));}
        let name_index=self.cur.i;
        let name=self.cur.word()?;
        let ty=if self.cur.eat(K::Colon){let raw=self.cur.ty(None)?;Some(self.resolved_type(&raw))}else{None};
        self.cur.need(K::Equal,"expected '='")?;
        let value=if self.cur.peek()==Some(K::Ident("if")) {
            self.disjunctive_shared_reference_if_initializer(ty.as_ref())?
        }else{self.expr(ty.as_ref(),0,0)?};
        if let Some(ref ty)=ty{if !self.value_matches(&value,ty){return Err(err(self.cur.pos(),"initializer type mismatch"));}}
        self.cur.need(K::Semi,"expected ';'")?;
        let symbol=SymbolId(u32::try_from(name_index+1).map_err(|_|err(self.cur.pos(),"symbol index overflow"))?);
        self.declare_symbol(name,value,mutable,symbol)
    }
    fn quantum_statement(&mut self)->Result<(),Diagnostic>{
        let start=self.cur.i;let p=self.cur.pos();
        //Delegate original borrowed tokens to the proven parser; never rewrite the source Calls with typed
        //scalar arguments are reconstructed explicitly from typed values
        if let Some(K::Ident(name))=self.cur.peek(){
            if self.cur.ahead(1)==Some(K::LParen){
                let gate=syntax::Name::from(name);self.cur.i+=1;self.cur.need(K::LParen,"expected '('")?;
                if gate=="static_assert_eq" || gate=="static_assert_ne" {
                    let a=self.expr(None,0,0)?;
                    self.cur.need(K::Comma,"expected ',' in static assertion")?;
                    let b=self.expr(Some(&a.ty()),0,0)?;
                    self.cur.need(K::RParen,"expected ')'")?;
                    self.cur.need(K::Semi,"expected ';'")?;
                    if a.ty()!=b.ty(){return Err(err(p,"static assertion types differ"));}
                    if matches!(&a,ConstValue::Ref(_))||matches!(&b,ConstValue::Ref(_)){
                        return Err(err(p,"reference equality needs explicit comparison semantics"));
                    }
                    if matches!(a,ConstValue::Struct(_, _)){
                        return Err(err(p,"struct equality requires PartialEq (not yet supported)"));
                    }
                    let ok=if gate=="static_assert_eq"{a==b}else{a!=b};
                    if !ok{return Err(err(p,"exact typed static assertion failed"));}
                    return Ok(());
                }
                let mut args=Vec::new();
                while !self.cur.eat(K::RParen){
                    let value=if let Some(K::Ident(n))=self.cur.peek(){
                        if self.quantum_names.contains(n){let name=syntax::Name::from(n);self.cur.i+=1;Expr::Var(name)}
                        else{let v=self.expr(None,0,0)?;Self::quantum_scalar(v,p)?}
                    }else{
                        let v=self.expr(None,0,0)?;Self::quantum_scalar(v,p)?
                    };
                    args.push(value);
                    if !self.cur.eat(K::RParen){self.cur.need(K::Comma,"expected ','")?;}else{break;}
                }
                self.cur.need(K::Semi,"expected ';' after gate")?;
                self.quantum.push(Stmt::Call{name:gate,args,at:p});return Ok(());
            }
        }
        while self.cur.peek().is_some() && self.cur.peek()!=Some(K::Semi){self.cur.i+=1;}
        self.cur.need(K::Semi,"expected ';'")?;
        let parsed=syntax::Parser::from_slice(&self.cur.tokens[start..self.cur.i]).parse()?;
        if parsed.statements.len()!=1{return Err(err(p,"expected one quantum statement"));}
        if let Stmt::Let{name,value:Expr::Call{name:ctor,..},..}=&parsed.statements[0]{
            if ctor=="qubit"{self.quantum_names.insert(name.as_str().to_owned());}
        }
        self.quantum.extend(parsed.statements);
        Ok(())
    }
    //Side-effecting expressions and references do not receive an implicit CFG certificate
    fn pure_match_guard(&mut self)->Result<Option<bool>,Diagnostic>{
        if !self.cur.eat(K::Ident("if")){return Ok(None);}
        let first=self.cur.i;
        if !matches!(self.cur.peek(),Some(K::Ident(_))){
            return Err(err(self.cur.pos(),"match guard requires a pure bool variable or literal"));
        }
        self.cur.i+=1;
        let result=self.boolean_condition(first..self.cur.i,"match guard")?;
        if self.cur.peek()!=Some(K::FatArrow){
            return Err(err(self.cur.pos(),"match guard requires a single bool expression"));
        }
        Ok(Some(result))
    }
    fn match_has_ref_bindings(&self,open:usize)->bool {
        let mut at=open+1;
        while at<self.cur.end && self.cur.tokens.get(at).is_some_and(|t|t.kind!=K::RBrace){
            let Some((pattern,next))=crate::typed_patterns::parse(
                &self.cur.tokens,at,self.cur.end)else{return false;};
            let mut bindings=Vec::new();
            crate::typed_patterns::collect_bindings(&pattern,&mut bindings);
            if bindings.iter().any(|(_,_,is_ref,_)|*is_ref){return true;}
            at=next;
            if self.cur.tokens.get(at).is_some_and(|t|t.kind==K::Ident("if")) {
                at+=1;
                if at>=self.cur.end{return false;}
                at+=1; //Pure single-token guard; checked later by frontend
            }
            if self.cur.tokens.get(at).is_none_or(|t|t.kind!=K::FatArrow){return false;}
            at+=1;
            if self.cur.tokens.get(at).is_none_or(|t|t.kind!=K::LBrace){return false;}
            let mut depth=0usize;
            loop {
                if at>=self.cur.end{return false;}
                match self.cur.tokens[at].kind {
                    K::LBrace=>depth+=1,
                    K::RBrace=>{depth-=1;if depth==0 {at+=1;break;}},
                    _=>(),
                }
                at+=1;
            }
            if self.cur.tokens.get(at).is_some_and(|t|t.kind==K::Comma){at+=1;}
        }
        false
    }
    fn static_enum_match(&mut self)->Result<(),Diagnostic>{
        let p=self.cur.pos();
        self.cur.need(K::Ident("match"),"expected match")?;
        //`match variable {` must not be misread as `Struct { ... }`
        let mut borrowed_subject=None::<(String,bool)>;
        let mut partial_owner=None::<String>;
        let value=if self.cur.eat(K::Amp){
            let exclusive=self.cur.eat(K::Ident("mut"));
            let subject=self.cur.word()?;
            if self.cur.peek()!=Some(K::LBrace){
                return Err(err(p,"borrowed match requires a named enum owner"));
            }
            let owner=self.cell(&subject)?;
            let slot=owner.borrow();
            if !slot.alive || !slot.move_paths.whole_initialized(){
                return Err(err(p,"borrowed match of moved or partially moved enum"));
            }
            if exclusive && !slot.mutable{
                return Err(err(p,"mutable enum match requires a mutable owner"));
            }
            if slot.loans.iter().any(|(_,is_mut,_)|exclusive || *is_mut){
                return Err(err(p,"enum match conflicts with an active borrow"));
            }
            let value=match slot.val.as_ref(){
                Some(value@ConstValue::Enum(..))|Some(value@ConstValue::EnumData(..))=>value.clone(),
                _=>return Err(err(p,"borrowed match requires an enum")),
            };
            drop(slot);
            borrowed_subject=Some((subject,exclusive));
            value
        }else if matches!(self.cur.peek(),Some(K::Ident(name)) if
            name!="true" && name!="false") &&
            self.cur.ahead(1)==Some(K::LBrace) {
            let subject=self.cur.word()?;
            let cell=self.cell(&subject)?;
            let candidate={
                let slot=cell.borrow();
                if !slot.alive{return Err(err(p,"use of expired enum owner"));}
                let supports_partial=match slot.val.as_ref(){
                    Some(ConstValue::Enum(id,_))|Some(ConstValue::EnumData(id,_,_))=>{
                        self.type_names.get(id.0 as usize)
                            .and_then(|name|self.enum_payloads.get(name))
                            .is_some_and(|variants|variants.iter().any(|fields|
                                fields.len()>=2 && fields.iter().any(|ty|
                                    !matches!(self.resolved_type(ty),
                                        ConstType::I64|ConstType::U64|ConstType::Bool)))) ||
                        self.match_has_ref_bindings(self.cur.i)
                    },
                    _=>false,
                };
                supports_partial.then_some(())
            };
            if candidate.is_some(){
                let slot=cell.borrow();
                if !slot.loans.is_empty(){return Err(err(p,"cannot match owned enum while borrowed"));}
                //This is a read-only discriminant snapshot. Bound non-Copy values MUST be taken from the real owner,
                //never the clone
                let value=slot.val.as_ref().ok_or_else(||err(p,"use of moved enum"))?.clone();
                drop(slot);
                partial_owner=Some(subject);
                value
            }else{self.take(&subject)?}
        } else {self.expr(None,0,0)?};
        if let ConstValue::Bool(selected_bool)=&value {
            self.cur.need(K::LBrace,"expected '{' after bool match value")?;
            let mut seen=0u8;
            let mut wildcard=false;
            let mut selected=None::<Range<usize>>;
            while !self.cur.eat(K::RBrace) {
                if self.cur.peek().is_none(){return Err(err(p,"unclosed bool match"));}
                let arm_at=self.cur.pos();
                let pattern=self.cur.word_borrowed()?;
                if wildcard{return Err(err(arm_at,"unreachable arm after wildcard"));}
                let (matches_value,coverage)=match pattern {
                    "true" => (*selected_bool,1u8),
                    "false" => (!*selected_bool,2u8),
                    "_" => (true,0u8),
                    _ => return Err(err(arm_at,"expected true, false or '_' in bool match")),
                };
                let guard=self.pure_match_guard()?;
                if guard.is_none(){
                    if coverage==0 {wildcard=true;}
                    else {
                        if seen&coverage!=0{return Err(err(arm_at,"duplicate bool match arm"));}
                        seen|=coverage;
                    }
                }
                self.cur.need(K::FatArrow,"expected '=>' after bool match pattern")?;
                let body=self.cur.body()?;
                if matches_value && guard.unwrap_or(true) && selected.is_none(){selected=Some(body);}
                self.cur.eat(K::Comma);
            }
            if !wildcard && seen!=3 {
                return Err(err(p,"nonexhaustive bool match: add true, false or '_'"));
            }
            let selected=selected.ok_or_else(||err(p,"bool match has no matching arm"))?;
            let start=self.quantum.len();
            self.main(selected)?;
            let statements=self.quantum.split_off(start);
            self.quantum.push(Stmt::Block{statements,at:p});
            return Ok(());
        }
        let (enum_id,variant_id,payload)=match value {
            ConstValue::Enum(id,variant)=>(id,variant,Vec::new()),
            ConstValue::EnumData(id,variant,fields)=>(id,variant,fields),
            _=>return Err(err(p,"typed static match currently requires bool or enum")),
        };
        //Own the bounded variant schema before creating RefLease entries; borrow_enum_field must mutably access
        //the runtime loan registry
        let enum_name=self.type_names.get(enum_id.0 as usize)
            .ok_or_else(||err(p,"unknown enum type in match"))?.clone();
        let variants=self.enums.get(&enum_name)
            .ok_or_else(||err(p,"unknown enum type in match"))?.clone();
        debug_assert!(variants.len()<=128);
        self.cur.need(K::LBrace,"expected '{' after match value")?;
        let mut seen=0u128;
        let mut wildcard=false;
        let mut selected=None::<Range<usize>>;
        let mut selected_bindings=Vec::new();
        let matched_value=if payload.is_empty(){ConstValue::Enum(enum_id,variant_id)}
            else{ConstValue::EnumData(enum_id,variant_id,payload)};
        while !self.cur.eat(K::RBrace){
            if self.cur.peek().is_none(){return Err(err(p,"unclosed enum match"));}
            let arm_at=self.cur.pos();
            if wildcard{return Err(err(arm_at,"unreachable arm after wildcard"));}
            let Some((pattern,after))=crate::typed_patterns::parse(
                &self.cur.tokens,self.cur.i,self.cur.end)else{
                return Err(err(arm_at,"unsupported nested enum pattern"));
            };
            let (checked,is_selected)={
                let schema=crate::typed_patterns::Schema{
                    enums:&self.enums,payloads:&self.enum_payloads,
                    structs:&self.types,type_ids:&self.type_ids,
                };
                let checked=crate::typed_patterns::check(&pattern,
                    &ConstType::Resolved(enum_id),borrowed_subject.as_ref().map(|(_,m)|*m),
                    &schema).map_err(|reason|err(arm_at,reason))?;
                let is_selected=crate::typed_patterns::matches_value(&pattern,&matched_value,&schema);
                (checked,is_selected)
            };
            self.cur.i=after;
            //A nested discriminant filters only a *subset* of the outer variant. It must be followed by a covering
            //pattern or wildcard
            let coverage=checked.variant.filter(|_|checked.covers_variant)
                .map_or(0u128,|index|1u128<<index);
            let is_wildcard=matches!(pattern,crate::typed_patterns::Pattern::Wildcard);
            let has_payload_binding=!checked.bindings.is_empty();
            let guard=self.pure_match_guard()?;
            if guard.is_some() && has_payload_binding {
                return Err(err(arm_at,"guard cannot inspect payload bindings yet"));
            }
            if guard.is_none(){
                if is_wildcard{wildcard=true;}
                else if coverage!=0 {
                    if seen & coverage != 0{return Err(err(arm_at,"duplicate enum match variant"));}
                    seen |= coverage;
                }
            }
            self.cur.need(K::FatArrow,"expected '=>' after enum pattern")?;
            let body=self.cur.body()?;
            if is_selected && guard.unwrap_or(true) && selected.is_none() {
                let mut bindings=Vec::<(String,ConstValue,SymbolId)>::new();
                for binding in checked.bindings {
                    let fields=binding.path.iter().map(|key|key.field).collect::<Vec<_>>();
                    let bound=if let Some((owner,_))=&borrowed_subject {
                        self.borrow_enum_path(owner,&fields,binding.by_ref==Some(true),binding.token)?
                    }else if let Some(owner)=&partial_owner {
                        if let Some(exclusive)=binding.by_ref {
                            self.borrow_enum_path(owner,&fields,exclusive,binding.token)?
                        }else{
                            let leaf=Self::nested_value(&matched_value,&fields)
                                .ok_or_else(||err(arm_at,"nested enum pattern has no matching payload"))?;
                            if leaf.is_copy(){
                                let cell=self.cell(owner)?;
                                let slot=cell.borrow();
                                if !slot.move_paths.path_initialized(&fields){
                                    return Err(err(arm_at,"use of moved enum payload"));
                                }
                                let place=Place::from_fields(&fields)
                                    .ok_or_else(||err(arm_at,"enum copy path too deep"))?;
                                if slot.loans.iter().any(|(_,mutable,loan)|
                                    *mutable && loan.overlaps(place)){
                                    return Err(err(arm_at,"cannot read enum field through mutable borrow"));
                                }
                                leaf.clone()
                            }else{self.take_enum_pattern_field(owner,&fields,binding.token)?}
                        }
                    }else{
                        if binding.by_ref.is_some(){
                            return Err(err(arm_at,"ref pattern needs a named, live enum owner"));
                        }
                        Self::nested_value(&matched_value,&fields)
                            .ok_or_else(||err(arm_at,"nested enum pattern has no matching payload"))?.clone()
                    };
                    bindings.push((binding.name.to_owned(),bound,
                        SymbolId(u32::try_from(binding.token+1)
                            .map_err(|_|err(arm_at,"symbol index overflow"))?)));
                }
                selected=Some(body);selected_bindings=bindings;
            }
            self.cur.eat(K::Comma);
        }
        if !wildcard && seen.count_ones() as usize != variants.len(){
            return Err(err(p,"nonexhaustive enum match: add missing variants or '_'"));
        }
        let selected=selected.ok_or_else(||err(p,"enum match has no matching arm"))?;
        let start=self.quantum.len();
        self.pending_variant_bindings=selected_bindings;
        self.main(selected)?;
        let statements=self.quantum.split_off(start);
        self.quantum.push(Stmt::Block{statements,at:p});
        Ok(())
    }
    fn condition_body_boundary(&mut self)->Result<Range<usize>,Diagnostic>{
        let start=self.cur.i;
        let mut parens=0usize;
        let mut brackets=0usize;
        let mut literal_braces=0usize;
        while let Some(kind)=self.cur.peek(){
            match kind {
                K::LParen=>parens+=1,
                K::RParen=>parens=parens.saturating_sub(1),
                K::LBracket=>brackets+=1,
                K::RBracket=>brackets=brackets.saturating_sub(1),
                K::LBrace if literal_braces!=0=>literal_braces+=1,
                K::LBrace => {
                    let struct_literal=self.cur.i>start && matches!(
                        self.cur.tokens[self.cur.i-1].kind,
                        K::Ident(name) if self.types.contains_key(name) &&
                            !self.scopes.iter().any(|scope|scope.contains_key(name)));
                    if struct_literal || parens!=0 || brackets!=0 {
                        literal_braces+=1;
                    } else {break;}
                }
                K::RBrace if literal_braces!=0=>literal_braces-=1,
                _=>(),
            }
            self.cur.i+=1;
        }
        if self.cur.peek()!=Some(K::LBrace){
            return Err(err(self.cur.pos(),"expected '{' after compile-time condition"));
        }
        Ok(start..self.cur.i)
    }
    fn static_if(&mut self)->Result<(),Diagnostic>{
        let p=self.cur.pos();
        let mut selected=None::<Range<usize>>;
        loop {
            self.cur.need(K::Ident("if"),"expected if")?;
            let condition=self.condition_body_boundary()?;
            let value=self.boolean_condition(condition,"if")?;
            let body=self.cur.body()?;
            if value && selected.is_none(){selected=Some(body);}
            if !self.cur.eat(K::Ident("else")){break;}
            if self.cur.peek()==Some(K::Ident("if")){continue;}
            let body=self.cur.body()?;
            if selected.is_none(){selected=Some(body);}
            break;
        }
        if let Some(body)=selected {
            let start=self.quantum.len();
            self.main(body)?;
            let statements=self.quantum.split_off(start);
            self.quantum.push(Stmt::Block{statements,at:p});
        }
        Ok(())
    }
    fn parse_loop_exit(&mut self)->Result<(),Diagnostic>{
        let p=self.cur.pos();
        let is_break=self.cur.eat(K::Ident("break"));
        if !is_break {self.cur.need(K::Ident("continue"),"expected loop control")?;}
        if self.loop_depth==0{return Err(err(p,"break/continue outside typed loop"));}
        self.cur.need(K::Semi,"expected ';' after loop control")?;
        self.host_flow=Some(if is_break{HostFlow::Break}else{HostFlow::Continue});
        Ok(())
    }
    fn parse_host_return(&mut self)->Result<(),Diagnostic>{
        let p=self.cur.pos();self.cur.need(K::Ident("return"),"expected return")?;
        let expected=self.return_stack.last().cloned().unwrap_or(ConstType::Unit);
        let value=if self.cur.eat(K::Semi){None}else{
            let v=self.expr(Some(&expected),0,0)?;
            self.cur.need(K::Semi,"expected ';' after return")?;
            Some(v)
        };
        if let Some(ref v)=value {
            if !self.value_matches(v,&expected){return Err(err(p,"return type mismatch"));}
        }else if expected!=ConstType::Unit{return Err(err(p,"missing return value"));}
        self.host_flow=Some(HostFlow::Return(value));
        Ok(())
    }
    fn boolean_condition(&mut self,range:Range<usize>,context:&str)->Result<bool,Diagnostic>{
        let p=at(&self.cur.tokens,range.start);
        let view=Cursor::view(Rc::clone(&self.cur.tokens),range);
        let saved=std::mem::replace(&mut self.cur,view);
        let result=(||{
            let value=self.expr(Some(&ConstType::Bool),0,0)?;
            if self.cur.peek().is_some(){return Err(err(self.cur.pos(),format!("unexpected tokens in {context} condition")));}
            match value {ConstValue::Bool(v)=>Ok(v),_=>Err(err(p,format!("typed {context} requires compile-time bool")))}
        })();
        self.cur=saved;result
    }
    fn loop_condition(&mut self,range:Range<usize>)->Result<bool,Diagnostic>{
        self.boolean_condition(range,"while")
    }
    fn run_loop_iteration(&mut self,body:Range<usize>,at:Position)->Result<bool,Diagnostic>{
        let start=self.quantum.len();
        self.main(body)?;
        let statements=self.quantum.split_off(start);
        self.quantum.push(Stmt::Block{statements,at});
        match self.host_flow.take() {
            Some(HostFlow::Break)=>Ok(false),
            Some(HostFlow::Continue)|None=>Ok(true),
            Some(signal @ HostFlow::Return(_))=>{self.host_flow=Some(signal);Ok(false)},
        }
    }
    fn static_while(&mut self)->Result<(),Diagnostic>{
        let p=self.cur.pos();self.cur.need(K::Ident("while"),"expected while")?;
        let start=self.cur.i;
        //Scan only at the top level, never mistake grouped expressions for a body. The typed expression
        //evaluator validates the condition
        let mut parens=0usize;
        while let Some(token)=self.cur.peek() {
            match token {
                K::LParen=>parens+=1,
                K::RParen=>parens=parens.saturating_sub(1),
                K::LBrace if parens==0=>break,
                _=>(),
            }
            self.cur.i+=1;
        }
        let condition=start..self.cur.i;
        let body=self.cur.body()?;
        self.loop_depth+=1;
        let result=(||{
            for _ in 0..100_000usize {
                if !self.loop_condition(condition.clone())? {return Ok(());}
                if !self.run_loop_iteration(body.clone(),p)? {return Ok(());}
            }
            Err(err(p,"typed static while iteration limit reached"))
        })();
        self.loop_depth-=1;result
    }
    fn static_loop(&mut self)->Result<(),Diagnostic>{
        let p=self.cur.pos();self.cur.need(K::Ident("loop"),"expected loop")?;
        let body=self.cur.body()?;
        self.loop_depth+=1;
        let result=(||{
            for _ in 0..100_000usize {
                if !self.run_loop_iteration(body.clone(),p)?{return Ok(());}
            }
            Err(err(p,"typed static loop requires reachable break (100000 iteration limit)"))
        })();
        self.loop_depth-=1;result
    }
    fn static_for(&mut self)->Result<(),Diagnostic>{
        let p=self.cur.pos();self.cur.need(K::Ident("for"),"expected for")?;
        let variable_index=self.cur.i;
        let variable=self.cur.word()?;
        self.cur.need(K::Ident("in"),"expected 'in' in for loop")?;
        let lo=self.expr(None,0,0)?;
        let inclusive=if self.cur.eat(K::DotDotEq){true}else{
            self.cur.need(K::DotDot,"expected '..' or '..=' in for range")?;false
        };
        let hi=self.expr(Some(&lo.ty()),0,0)?;
        let body=self.cur.body()?;
        let signed=matches!(lo,ConstValue::I64(_));
        let start=match lo {ConstValue::I64(n)=>i128::from(n),ConstValue::U64(n)=>i128::from(n),_=>return Err(err(p,"for range requires i64 or u64"))};
        let stop=match hi {ConstValue::I64(n) if signed=>i128::from(n),ConstValue::U64(n) if !signed=>i128::from(n),_=>return Err(err(p,"for range endpoint type mismatch"))};
        let exclusive=stop+if inclusive{1}else{0};
        let iterations=(exclusive-start).max(0);
        if iterations>100_000{return Err(err(p,"typed static for iteration limit reached"));}
        self.loop_depth+=1;
        let result=(||{
            for value in start..exclusive {
                self.push_scope();
                let index=if signed{ConstValue::I64(i64::try_from(value).map_err(|_|err(p,"for range overflow"))?)}
                    else{ConstValue::U64(u64::try_from(value).map_err(|_|err(p,"for range overflow"))?)};
                let symbol=SymbolId(u32::try_from(variable_index+1).map_err(|_|err(p,"symbol index overflow"))?);
                self.declare_symbol(variable.clone(),index,false,symbol)?;
                let next=self.run_loop_iteration(body.clone(),p);
                let pop=self.pop_scope();pop?;
                if !next?{break;}
            }
            Ok(())
        })();
        self.loop_depth-=1;result
    }
    fn quantum_scalar(v:ConstValue,at:Position)->Result<Expr,Diagnostic>{
        match v{
            ConstValue::I64(n)=>{if n.unsigned_abs()>9_007_199_254_740_992u64{return Err(err(at,"i64 cannot be represented exactly by f64 QPU boundary"));}
                Ok(Expr::Number(n as f64))},
            ConstValue::U64(n)=>{if n>9_007_199_254_740_992{return Err(err(at,"u64 cannot be represented exactly by f64 QPU boundary"));}
                Ok(Expr::Number(n as f64))},
            ConstValue::Bool(b)=>Ok(Expr::Bool(b)),
            _=>Err(err(at,"aggregate cannot be used as a quantum gate operand")),
        }
    }
    fn main(&mut self,body:Range<usize>)->Result<(),Diagnostic>{
        if self.block_depth>=64{return Err(err(self.cur.pos(),"typed static branch nesting limit reached"));}
        let owns_flow=!self.flow_stack.last().is_some_and(|flow|flow.contains(&body));
        if owns_flow {self.start_flow(body.clone(),false);}
        self.block_depth+=1;
        let view=Cursor::view(Rc::clone(&self.cur.tokens),body);
        let old=std::mem::replace(&mut self.cur,view);
        self.push_scope();
        let pattern_bindings=std::mem::take(&mut self.pending_variant_bindings);
        for (name,value,symbol) in pattern_bindings {
            let is_reference=matches!(&value,ConstValue::Ref(_));
            self.declare_symbol(name.clone(),value,false,symbol)?;
            if is_reference {
                if let Some(slot)=self.scopes.last_mut().and_then(|scope|scope.get_mut(&name)) {
                    slot.pattern_loan=true;
                }
            }
        }
        self.end_dead_local_borrows();
        while self.cur.peek().is_some(){
            if self.cur.peek()==Some(K::Ident("while")) {
                self.static_while()?;
            } else if self.cur.peek()==Some(K::Ident("for")) {
                self.static_for()?;
            } else if self.cur.peek()==Some(K::Ident("loop")) {
                self.static_loop()?;
            } else if matches!(self.cur.peek(),Some(K::Ident("break"|"continue"))) {
                self.parse_loop_exit()?;
            } else if self.cur.peek()==Some(K::Ident("return")) {
                self.parse_host_return()?;
            } else if self.cur.peek()==Some(K::Ident("match")) {
                self.static_enum_match()?;
            } else if self.cur.peek()==Some(K::Ident("if")) {
                self.static_if()?;
            } else if self.cur.peek()==Some(K::LBrace) {
                //A standalone `{ ... }` introduces a true lexical scope: nested RefLease children must be dropped
                //before resuming the parent's mutable reference
                let p=self.cur.pos();
                let body=self.cur.body()?;
                let first=self.quantum.len();
                self.main(body)?;
                let statements=self.quantum.split_off(first);
                self.quantum.push(Stmt::Block{statements,at:p});
            } else if matches!(self.cur.peek(),Some(K::Ident("let"|"const"))){
                let mut i=self.cur.i+1;
                if self.cur.tokens.get(i).map(|t|t.kind)==Some(K::Ident("mut")){i+=1;}
                let mut typed=false;
                if self.cur.tokens.get(i+1).map(|t|t.kind)==Some(K::Colon){
                    if let Some(K::Ident(n))=self.cur.tokens.get(i+2).map(|t|t.kind){
                        typed=matches!(n,"i64"|"u64"|"bool")||self.types.contains_key(n)||self.enums.contains_key(n);
                    }
                    if matches!(self.cur.tokens.get(i+2).map(|t|t.kind),Some(K::Amp|K::AndAnd)){typed=true;}
                } else if self.cur.tokens.get(i+1).map(|t|t.kind)==Some(K::Equal){
                    let rhs=self.cur.tokens.get(i+2).map(|t|t.kind);
                    typed=matches!(rhs,Some(K::Number(_))|Some(K::Minus)|Some(K::Amp)|Some(K::Star)|
                        Some(K::Ident("true"|"false"|"if")))
                        ||matches!(rhs,Some(K::Ident(n)) if self.scopes.iter().any(|scope|scope.contains_key(n))
                            //A call to a declared typed function may infer a scalar, aggregate or reference type. Do NOT route its
                            //`let` through the quantum Parser (which owns qubit()/bit())
                            || (self.functions.contains_key(n) &&
                                self.cur.tokens.get(i+3).is_some_and(|t|t.kind==K::LParen)));
                }
                if typed {self.typed_let()?;} else {self.quantum_statement()?;}
            }else if self.try_assignment()? {
            }else if let Some(K::Ident(n))=self.cur.peek(){
                if (self.functions.contains_key(n) && self.cur.ahead(1)==Some(K::LParen)) ||
                    (self.scopes.iter().any(|scope|scope.contains_key(n)) &&
                    self.cur.ahead(1)==Some(K::Dot) && self.cur.ahead(3)==Some(K::LParen)) {
                    let _value=self.expr(None,0,0)?;
                    self.cur.need(K::Semi,"expected ';' after method call")?;
                }else{self.quantum_statement()?;}
            }else{return Err(err(self.cur.pos(),"unsupported typed main statement"));}
            if self.host_flow.is_some(){break;}
            self.end_dead_local_borrows();
        }
        let scope_result=self.pop_scope();self.cur=old;self.block_depth-=1;
        if owns_flow {self.flow_stack.pop();}
        scope_result
    }
    fn parse_definitions(&mut self)->Result<Range<usize>,Diagnostic>{
        while self.cur.peek().is_some(){
            if matches!(self.cur.peek(),Some(K::Ident("struct"|"enum"|"impl"|"fn"))){
                self.definition()?;
            } else {break;}
        }
        let top_level_start=self.cur.i;
        for fun in &self.fn_defs {
            for ty in fun.params.iter().map(|(_,ty)|ty).chain(fun.ret.iter()) {
                let mut inner=ty;
                while let ConstType::Ref(nested)|ConstType::RefMut(nested)=inner {inner=nested;}
                if let ConstType::Named(n)=inner {
                    if !self.types.contains_key(n)&&!self.enums.contains_key(n){return Err(err(self.cur.pos(),format!("unknown type '{n}'")));}
                }
            }
        }
        if let Some(id)=self.functions.get("main") {
            if self.cur.peek().is_some(){return Err(err(self.cur.pos(),"unexpected tokens after function declarations"));}
            let main=&self.fn_defs[id.0 as usize];
            if !main.params.is_empty()||main.ret.is_some()||!main.generics.is_empty(){return Err(err(self.cur.pos(),"main must be fn main()"));}
            Ok(main.body.clone())
        } else if self.fn_defs.is_empty() {
            Ok(top_level_start..self.cur.end)
        } else {
            Err(err(self.cur.pos(),"missing fn main()"))
        }
    }
    fn validate_function_bodies(&self)->Result<HashMap<String,Vec<ReferencePathOrigin>>,Diagnostic>{
        let tokens=&self.cur.tokens;
        let mut mir_methods=HashMap::new();
        for (&owner,entries) in &self.methods {
            for (name,id) in entries {
                let def=&self.fn_defs[id.0 as usize];
                let borrowed=def.params.first().and_then(|(_,ty)|match ty {
                    ConstType::RefMut(_)=>Some(true),ConstType::Ref(_)=>Some(false),_=>None,
                });
                if let Some(exclusive)=borrowed {
                    mir_methods.insert((owner,name.clone()),
                        (exclusive,def.params.len(),def.ret.clone().unwrap_or(ConstType::Unit)));
                }
            }
        }
        //No raw quantum op receives a guessed effects summary. A future semantic lowering pass must provide
        //each complete verified effect
        let verified_effects=HashMap::new();
        let mir_schema=crate::typed_mir::Schema{enum_payloads:&self.enum_payloads,enums:&self.enums,types:&self.types,
            type_ids:&self.type_ids,type_names:&self.type_names,methods:&mir_methods,
            verified_effects:&verified_effects};
        let projected_returns={
            let mut solver=ReferenceSummarySolver::new(&self.fn_defs,tokens,
                &self.types,&self.type_ids,&self.type_names);
            let mut proven=HashMap::<String,Vec<crate::typed_mir::VerifiedReturnedReference>>::new();
            for (name,id) in &self.functions {
                let function=&self.fn_defs[id.0 as usize];
                let Some(result_type)=function.ret.as_ref()else{continue;};
                if !function.generics.is_empty() ||
                    !matches!(result_type,ConstType::Ref(_)|ConstType::RefMut(_)){
                    continue;
                }
                if let Some(paths)=solver.projected(name) {
                    if !paths.is_empty() && paths.len()<=32 &&
                        paths.iter().all(|origin|origin.parameter<function.params.len()) {
                        proven.insert(name.clone(),paths.iter().map(|origin|
                            crate::typed_mir::VerifiedReturnedReference{
                                parameter:origin.parameter,fields:origin.path.clone(),
                                ty:result_type.clone(),
                            }).collect());
                    }
                }else if let Some(origin)=effectful_return_field_origin(&mut solver,function){
                    proven.insert(name.clone(),vec![origin]);
                }
            }
            for _ in 0..self.functions.len() {
                let mut changed=false;
                for (name,id) in &self.functions {
                    if proven.contains_key(name){continue;}
                    let function=&self.fn_defs[id.0 as usize];
                    for (callee_name,callee_id) in &self.functions {
                        let Some(origins)=proven.get(callee_name)else{continue;};
                        let callee=&self.fn_defs[callee_id.0 as usize];
                        let composed=origins.iter().map(|origin|
                            forwarded_return_field_origin(tokens,function,callee_name,callee,origin))
                            .collect::<Option<Vec<_>>>();
                        if let Some(composed)=composed {
                            if !composed.is_empty() && composed.len()<=32 {
                                proven.insert(name.clone(),composed);
                                changed=true;break;
                            }
                        }
                    }
                }
                if !changed{break;}
            }
            proven
        };

        let mut verified_calls=HashMap::<String,crate::typed_mir::VerifiedCallSummary>::new();
        for _ in 0..self.functions.len() {
            let mut progressed=false;
            for (name,id) in &self.functions {
                if verified_calls.contains_key(name) || name.as_str()=="main" {continue;}
                let def=&self.fn_defs[id.0 as usize];
                if !def.generics.is_empty() ||
                    (def.ret.as_ref().is_some_and(|ty|*ty!=ConstType::Unit) &&
                        !projected_returns.contains_key(name)) {continue;}
                let mir=crate::typed_mir::lower_with_verified_calls(
                    tokens,def.body.clone(),&def.params,&mir_schema,&[],&verified_calls);
                let Ok(Some(mir))=mir else{continue;};
                if !matches!(mir.verify(),Ok(conflicts) if conflicts.is_empty()) {continue;}
                //The callee must not consume that storage by value; a shared reference also cannot mutate it
                let mut valid=true;
                let mut field_writes=HashSet::new();
                let mut parameter_effects=HashSet::new();
                for block in &mir.blocks {
                    for statement in &block.statements {
                        if let crate::typed_mir::Statement::Call{name,token,..}=statement {
                            //Method calls are a different dispatch/effect namespace; an identically named free function must never
                            //certify the method by coincidence
                            let method_call=tokens.get(*token+1)
                                .is_some_and(|t|t.kind==K::Dot);
                            if method_call || !verified_calls.contains_key(name) {valid=false;}
                        }
                        if matches!(statement,crate::typed_mir::Statement::QuantumOperation{..}) {
                            valid=false;
                        }
                        for event in statement.events() {
                            let formal=event.path.owner.0 as usize;
                            let lower=tokens.len()+1;
                            if formal<lower || formal>=lower+def.params.len(){continue;}
                            let formal_ty=&def.params[formal-lower].1;
                            let op=event.op;
                            let kind=match op {
                                crate::cfg_borrow::Access::Move=>Some(crate::typed_mir::VerifiedEffectKind::Move),
                                crate::cfg_borrow::Access::Drop=>Some(crate::typed_mir::VerifiedEffectKind::Drop),
                                crate::cfg_borrow::Access::Write|
                                    crate::cfg_borrow::Access::Initialize=>Some(crate::typed_mir::VerifiedEffectKind::Write),
                                _=>None,
                            };
                            if let Some(kind)=kind {
                                parameter_effects.insert(crate::typed_mir::VerifiedParameterEffect{
                                    parameter:formal-lower,fields:event.path.fields.clone(),kind,
                                });
                            }
                            if matches!(formal_ty,ConstType::Ref(_)|ConstType::RefMut(_)) {
                                //A reference formal is a caller-owned abstract place. Its storage must never be moved, dropped or
                                //deallocated in a callee
                                if matches!(op,crate::cfg_borrow::Access::Move|
                                    crate::cfg_borrow::Access::Drop|
                                    crate::cfg_borrow::Access::StorageDead) {valid=false;}
                                if matches!(formal_ty,ConstType::Ref(_)) &&
                                    matches!(op,crate::cfg_borrow::Access::Write|
                                        crate::cfg_borrow::Access::Initialize|
                                        crate::cfg_borrow::Access::BorrowMut|
                                        crate::cfg_borrow::Access::ReserveMut) {
                                    valid=false;
                                }
                                if matches!(op,crate::cfg_borrow::Access::Write|
                                    crate::cfg_borrow::Access::Initialize) {
                                    if !matches!(formal_ty,ConstType::RefMut(_)) ||
                                        event.path.fields.is_empty() {
                                        valid=false;
                                    }else{
                                        field_writes.insert(crate::typed_mir::VerifiedFieldWrite{
                                            parameter:formal-lower,
                                            fields:event.path.fields.clone(),
                                        });
                                    }
                                }
                            }
                        }
                        //Nested verified calls carry only their certified transitive effects. Their actual events were already
                        //checked by MIR, so do not replay moves or drops
                        for effect in statement.verified_effects() {
                            let paths=if effect.alternatives.is_empty(){
                                std::slice::from_ref(&effect.path)
                            }else{effect.alternatives.as_slice()};
                            for path in paths {
                                let formal=path.owner.0 as usize;
                                let lower=tokens.len()+1;
                                if formal<lower || formal>=lower+def.params.len(){continue;}
                                let formal_ty=&def.params[formal-lower].1;
                                if matches!(formal_ty,ConstType::Ref(_)|ConstType::RefMut(_)) &&
                                    (effect.kind!=crate::typed_mir::VerifiedEffectKind::Write ||
                                     !matches!(formal_ty,ConstType::RefMut(_)) ||
                                     path.fields.is_empty()) {valid=false;}
                                parameter_effects.insert(crate::typed_mir::VerifiedParameterEffect{
                                    parameter:formal-lower,fields:path.fields.clone(),
                                    kind:effect.kind,
                                });
                                if matches!(formal_ty,ConstType::RefMut(_)) &&
                                    effect.kind==crate::typed_mir::VerifiedEffectKind::Write &&
                                    !path.fields.is_empty() {
                                    field_writes.insert(crate::typed_mir::VerifiedFieldWrite{
                                        parameter:formal-lower,fields:path.fields.clone(),
                                    });
                                }
                            }
                        }
                    }
                }
                if !valid || parameter_effects.len()>256 {continue;}
                let mut parameter_effects=parameter_effects.into_iter().collect::<Vec<_>>();
                parameter_effects.sort_by(|a,b|a.parameter.cmp(&b.parameter)
                    .then_with(||(a.kind as u8).cmp(&(b.kind as u8)))
                    .then_with(||a.fields.iter().map(|key|(key.aggregate.0,key.field.0))
                        .cmp(b.fields.iter().map(|key|(key.aggregate.0,key.field.0)))));
                let mut field_writes=field_writes.into_iter().collect::<Vec<_>>();
                field_writes.sort_by(|a,b|a.parameter.cmp(&b.parameter)
                    .then_with(||a.fields.iter().map(|key|(key.aggregate.0,key.field.0))
                        .cmp(b.fields.iter().map(|key|(key.aggregate.0,key.field.0)))));
                let declared_origins=projected_returns.get(name)
                    .map(Vec::as_slice).unwrap_or(&[]);
                let path_cases=mir.solve_path_cases(tokens.len(),&def.params,declared_origins)
                    .filter(|cases| {
                        let actual=cases.iter().flat_map(|c|c.effects.iter().cloned())
                            .collect::<HashSet<_>>();
                        //An effect missing from any enumerated path means the CFG proof is incomplete; fall back to MAY
                        actual==parameter_effects.iter().cloned().collect::<HashSet<_>>()
                    }).unwrap_or_default();
                verified_calls.insert(name.clone(),crate::typed_mir::VerifiedCallSummary{
                    parameters:def.params.iter().map(|(_,ty)|ty.clone()).collect(),
                    field_writes,
                    parameter_effects,
                    returned:projected_returns.get(name).and_then(|origins|
                        (origins.len()==1).then(||origins[0].clone())),
                    returned_alternatives:projected_returns.get(name).filter(|origins|
                        origins.len()>1).cloned().unwrap_or_default(),
                    path_cases,
                });
                progressed=true;
            }
            if !progressed {break;}
        }
        for fun in &self.fn_defs {
            let affine_aggregate=fun.params.iter().any(|(_,ty)|match ty {
                ConstType::Named(name)=>self.types.contains_key(name)||self.enums.contains_key(name),
                ConstType::Resolved(_)=>true,
                _=>false,
            });
            let interesting=!fun.generics.is_empty() || affine_aggregate || tokens[fun.body.clone()].iter().any(|t|
                matches!(t.kind,K::Amp|K::Star|K::Dot|K::Ident("if"|"match"|"while"|"for")) ||
                matches!(t.kind,K::Ident(name) if verified_calls.contains_key(name)));
            if !interesting {continue;}
            let copy_bounds=fun.generics.iter().filter(|g|g.bounds.iter().any(|b|b=="Copy"))
                .map(|g|g.name.clone()).collect::<Vec<_>>();
            let affine_generic=fun.generics.iter().any(|g|
                !g.bounds.iter().any(|b|b=="Copy") && fun.params.iter().any(|(_,ty)|
                    matches!(ty,ConstType::Generic(name) if name==&g.name)));
            let requires_complete_mir=affine_generic || affine_aggregate;
            let lowered=crate::typed_mir::lower_with_verified_calls(
                tokens,fun.body.clone(),&fun.params,&mir_schema,&copy_bounds,&verified_calls);
            match lowered {
                Ok(Some(mir))=>match mir.verify(){
                    Ok(errors)=>if let Some(first)=errors.first(){
                        return Err(err(at(tokens,first.token),format!("typed MIR borrow check: {}",first.message)));
                    },
                    Err(reason)=>{
                        //A fully lowered MIR is subject to mandatory checking Resource exhaustion/invariant errors fail closed;
                        //they cannot downgrade a complete MIR to a success
                        return Err(err(at(tokens,fun.body.start),
                            format!("typed MIR analysis failed: {reason}")));
                    }
                },
                Ok(None) if requires_complete_mir=>return Err(err(at(tokens,fun.body.start),
                    format!("incomplete typed MIR ownership coverage in affine function '{}'",fun.name))),
                Err(reason)=>return Err(err(at(tokens,fun.body.start),
                    format!("typed MIR lowering failed in function '{}': {reason}",fun.name))),
                Ok(None)=>(), //not certified; legacy RefLease checker applies
            }
        }
        let entry_main=self.functions.get("main").map(|id|id.0 as usize);
        let mut summaries=ReferenceSummarySolver::new(&self.fn_defs,tokens,
            &self.types,&self.type_ids,&self.type_names);
        for (function_index,fun) in self.fn_defs.iter().enumerate() {
            let mut block_loops=Vec::<bool>::new();
            let mut next_loop=false;
            for i in fun.body.clone() {
                match tokens[i].kind {
                    K::Ident("while"|"for"|"loop")=>next_loop=true,
                    K::LBrace=>{block_loops.push(next_loop);next_loop=false;},
                    K::RBrace=>{block_loops.pop();},
                    K::Ident("break"|"continue")
                        if Some(function_index)!=entry_main && !block_loops.iter().any(|&is_loop|is_loop)=>{
                        return Err(err(at(tokens,i),"break or continue outside a static loop"));
                    }
                    _=>(),
                }
            }
            for i in fun.body.clone() {
                if !matches!(tokens[i].kind,K::Ident("let"|"const")){continue;}
                let mut j=i+1;
                if tokens.get(j).is_some_and(|t|t.kind==K::Ident("mut")){j+=1;}
                if !matches!(tokens.get(j).map(|t|t.kind),Some(K::Ident(_))) {continue;}
                if !tokens.get(j+1).is_some_and(|t|t.kind==K::Colon){continue;}
                let ty=tokens.get(j+2).map(|t|t.kind);
                if !tokens.get(j+3).is_some_and(|t|t.kind==K::Equal){continue;}
                let literal=tokens.get(j+4).map(|t|t.kind);
                if !tokens.get(j+5).is_some_and(|t|t.kind==K::Semi){continue;}
                let mismatch=matches!(ty,Some(K::Ident("bool"))) && matches!(literal,Some(K::Number(_))) ||
                    matches!(ty,Some(K::Ident("i64"|"u64"))) &&
                    matches!(literal,Some(K::Ident("true"|"false")));
                if mismatch {return Err(err(at(tokens,j+4),"initializer type mismatch in function body"));}
            }
            let ref_return=matches!(fun.ret.as_ref(),Some(ConstType::Ref(_)|ConstType::RefMut(_)));
            if !ref_return {continue;}
            let certified_return=verified_calls.get(&fun.name).is_some_and(|summary|
                summary.returned.as_ref().is_some_and(|origin|
                    fun.ret.as_ref()==Some(&origin.ty)) ||
                (!summary.returned_alternatives.is_empty() &&
                    summary.returned_alternatives.iter().all(|origin|
                        fun.ret.as_ref()==Some(&origin.ty))));
            if certified_return {continue;}
            let parameters=fun.params.iter().enumerate().map(|(i,(name,_))|
                (name.clone(),SymbolId(u32::try_from(tokens.len()+i+1)
                    .expect("token index is within u32")))).collect::<Vec<_>>();
            let flow=FlowPlan::new(tokens,fun.body.clone(),true,0,&parameters);
            if has_mutable_alias_prefix(tokens,fun) {
                if summaries.prove(&fun.name).is_some() {
                    continue;
                }
                return Err(err(at(tokens,fun.body.start),
                    "cannot prove lifetime or linear ownership of mutable alias"));
            }
            let shared_aliases=reference_aliases(tokens,fun)
                .filter(|(aliases,tail)| !aliases.bindings.is_empty() &&
                    reference_expression_origins(&mut summaries,fun,
                        aliases,tail.clone()).is_some())
                .map(|(aliases,_)|aliases.bindings).unwrap_or_default();
            let mut param_region=HashMap::<SymbolId,usize>::new();
            for (i,(_,ty)) in fun.params.iter().enumerate() {
                if matches!(ty,ConstType::Ref(_)|ConstType::RefMut(_)) {
                    param_region.insert(parameters[i].1,i);
                }
            }
            let mut check_source = |expression:usize| -> Result<(),Diagnostic> {
                if expression>=fun.body.end || tokens[expression].kind==K::Semi {
                    return Err(err(at(tokens,expression),
                        "reference-returning function requires a return value"));
                }
                let mut pos=expression;
                let by_borrow=tokens[pos].kind==K::Amp;
                if by_borrow {pos+=1;}
                let exclusive_borrow=by_borrow && pos<fun.body.end &&
                    tokens[pos].kind==K::Ident("mut");
                if exclusive_borrow {pos+=1;}
                let mut dereferences=0usize;
                if by_borrow {
                    while pos<fun.body.end && tokens[pos].kind==K::Star {
                        dereferences+=1;
                        pos+=1;
                        if dereferences>16{return Err(err(at(tokens,expression),
                            "returned reborrow nesting limit exceeded"));}
                    }
                }
                let reborrow=dereferences!=0;
                //Runtime nested reference borrows need their own place and owner proof
                if dereferences>1 {
                    return Err(err(at(tokens,expression),
                        "cannot prove nested returned reborrow provenance"));
                }
                if pos>=fun.body.end {
                    return Err(err(at(tokens,expression),"unresolved return reference origin"));
                }
                //Interprocedural return proof for a *pure* multi-argument reference helper (including if/match
                //alternatives)
                if !by_borrow {
                    if let Some(K::Ident(callee_name))=tokens.get(pos).map(|t|t.kind) {
                        if tokens.get(pos+1).is_some_and(|t|t.kind==K::LParen) {
                            if let Some(source_mask)=summaries.prove(callee_name) {
                                let callee=self.fn_defs.iter().find(|f|f.name==callee_name)
                                    .expect("proven call has a definition");
                                if callee.ret==fun.ret {
                                    let mut call_end=pos+2;
                                    let mut actuals=Vec::with_capacity(callee.params.len());
                                    while call_end<fun.body.end &&
                                        tokens[call_end].kind!=K::RParen {
                                        let K::Ident(name)=tokens[call_end].kind else {break;};
                                        let Some(caller_index)=fun.params.iter().position(
                                            |(parameter,_)|parameter==name) else {break;};
                                        if callee.params.get(actuals.len()).map(|p|&p.1)!=
                                            Some(&fun.params[caller_index].1) ||
                                            flow.binding_at_token(call_end)!=
                                            Some(parameters[caller_index].1) {break;}
                                        actuals.push(caller_index);
                                        call_end+=1;
                                        if tokens.get(call_end).is_some_and(|t|t.kind==K::Comma){
                                            call_end+=1;
                                        }else{break;}
                                    }
                                    if actuals.len()==callee.params.len() &&
                                        tokens.get(call_end).is_some_and(|t|t.kind==K::RParen) &&
                                        tokens.get(call_end+1).is_none_or(|t|
                                            matches!(t.kind,K::Semi|K::RBrace)) {
                                        let mut exclusive_actuals=HashSet::new();
                                        for (&actual,(_,ty)) in actuals.iter().zip(&callee.params) {
                                            if matches!(ty,ConstType::RefMut(_)) &&
                                                !exclusive_actuals.insert(parameters[actual].1) {
                                                return Err(err(at(tokens,expression),
                                                    "one mutable reference cannot bind two call parameters"));
                                            }
                                        }
                                        let signature=fun.regions.as_ref().expect(
                                            "reference return has a region signature");
                                        let mut actual_masks=[0u64;64];
                                        for (slot,&index) in actual_masks.iter_mut().zip(&actuals){
                                            *slot=1u64<<index;
                                        }
                                        let mut solver=RegionConstraintSolver::new(signature);
                                        let returned=solver.instantiate_call_sources(source_mask,
                                            &actual_masks[..actuals.len()])
                                            .map_err(|msg|err(at(tokens,expression),msg))?;
                                        solver.solve_and_verify_return(returned).map_err(|msg|
                                            err(at(tokens,expression),msg))?;
                                        return Ok(());
                                    }
                                }
                            }
                        }
                    }
                }
                let mut transparent_call_end=None;
                if !by_borrow {
                    if let (Some(K::Ident(callee_name)),Some(K::LParen),
                            Some(K::Ident(_)),Some(K::RParen))=(
                        tokens.get(pos).map(|t|t.kind),tokens.get(pos+1).map(|t|t.kind),
                        tokens.get(pos+2).map(|t|t.kind),tokens.get(pos+3).map(|t|t.kind)) {
                        let arg_type=match tokens.get(pos+2).map(|t|t.kind) {
                            Some(K::Ident(name))=>fun.params.iter()
                                .find(|(parameter,_)|parameter==name).map(|(_,ty)|ty),
                            _=>None,
                        };
                        let compatible=self.fn_defs.iter().any(|candidate|
                            candidate.name==callee_name && candidate.ret==fun.ret &&
                            candidate.params.len()==1 &&
                            arg_type==Some(&candidate.params[0].1));
                        if compatible && transparent_reference_chain(&self.fn_defs,tokens,callee_name,16) {
                            transparent_call_end=Some(pos+4);
                            pos+=2; //use the reference argument's real binding
                        }
                    }
                }
                let Some(source)=flow.binding_at_token(pos) else {
                    return Err(err(at(tokens,expression),
                        "cannot prove lifetime of returned reference expression"));
                };
                //A source identifier alone is NOT proof that the whole expression is a reference to that source
                let mut after=pos+1;
                let mut projection=false;
                while after<fun.body.end && tokens[after].kind==K::Dot {
                    projection=true;
                    after+=1;
                    if !matches!(tokens.get(after).map(|t|t.kind),Some(K::Ident(_))) {
                        return Err(err(at(tokens,expression),
                            "invalid returned reference place projection"));
                    }
                    after+=1;
                }
                if let Some(end_of_call)=transparent_call_end {after=end_of_call;}
                if after<fun.body.end && !matches!(tokens[after].kind,K::Semi|K::RBrace) {
                    return Err(err(at(tokens,expression),
                        "cannot prove lifetime of composite returned reference expression"));
                }
                let verified_alias_source=match tokens[pos].kind {
                    K::Ident(name)=>shared_aliases.iter()
                        .find(|alias|alias.name==name)
                        .map(|alias|parameters[alias.origin].1),
                    _=>None,
                };
                let root=if let Some(source)=verified_alias_source {source} else {
                    flow.root_owner(source).ok_or_else(||
                        err(at(tokens,expression),"cyclic reference origin in function body"))?
                };
                let candidate=if verified_alias_source.is_some() || by_borrow ||
                    flow.origin(source).is_some(){root}else{source};
                if by_borrow && !reborrow && param_region.contains_key(&candidate) &&
                    !matches!(tokens.get(pos+1).map(|t|t.kind),Some(K::Dot)) {
                    return Err(err(at(tokens,expression),
                        "reference to parameter binding cannot escape its local lifetime"));
                }
                if exclusive_borrow && reborrow {
                    if let Some(&index)=param_region.get(&candidate) {
                        if !matches!(&fun.params[index].1,ConstType::RefMut(_)) {
                            return Err(err(at(tokens,expression),
                                "cannot mutably reborrow a shared reference parameter"));
                        }
                    }
                }
                //Returning &r.field borrows the REFERENT of r, never the local reference slot
                if projection {
                    if !by_borrow || reborrow {
                        return Err(err(at(tokens,expression),
                            "projected return must explicitly borrow a referenced field"));
                    }
                    let Some(&index)=param_region.get(&candidate)else{
                        return Err(err(at(tokens,expression),
                            "projected return has no proven reference parameter"));
                    };
                    let mut fields=Vec::new();
                    let mut field_at=pos+1;
                    while field_at<after {
                        if tokens[field_at].kind!=K::Dot{return Err(err(at(tokens,field_at),
                            "invalid projected return field"));}
                        let K::Ident(field)=tokens.get(field_at+1).map(|t|t.kind)
                            .ok_or_else(||err(at(tokens,field_at),"missing projected field"))?
                        else{return Err(err(at(tokens,field_at),"invalid projected field name"));};
                        fields.push(field);field_at+=2;
                    }
                    let (_path,pointee,source_mut)=checked_reference_projection(
                        &fun.params[index].1,&fields,&self.types,&self.type_ids,&self.type_names)
                        .ok_or_else(||err(at(tokens,expression),
                            "cannot resolve returned reference field path"))?;
                    if exclusive_borrow && !source_mut {
                        return Err(err(at(tokens,expression),
                            "cannot mutably borrow field through shared reference"));
                    }
                    let expected=match fun.ret.as_ref() {
                        Some(ConstType::Ref(ty)) if !exclusive_borrow=>ty.as_ref(),
                        Some(ConstType::RefMut(ty)) if exclusive_borrow=>ty.as_ref(),
                        _=>return Err(err(at(tokens,expression),
                            "projected reference mutability does not match return type")),
                    };
                    if !same_projected_type(&pointee,expected,&self.type_ids) {
                        return Err(err(at(tokens,expression),
                            "returned projected reference pointee type mismatch"));
                    }
                }
                //A direct returned parameter (or its `&*` reborrow) must also have the same pointee type as the
                //declared return
                if !projection {
                    if let Some(&index)=param_region.get(&candidate) {
                        let input=&fun.params[index].1;
                        let output=fun.ret.as_ref();
                        if !by_borrow && matches!(input,ConstType::RefMut(_)) &&
                            matches!(output,Some(ConstType::Ref(_))) {
                            return Err(err(at(tokens,expression),
                                "shared return from mutable reference requires explicit reborrow"));
                        }
                        let mut inner=input;
                        for n in 0..dereferences {
                            let mutable=matches!(inner,ConstType::RefMut(_));
                            inner=match inner {
                                ConstType::Ref(ty)|ConstType::RefMut(ty)=>ty,
                                _=>return Err(err(at(tokens,expression),
                                    "returned reborrow dereferences a non-reference")),
                            };
                            if exclusive_borrow && n+1==dereferences && !mutable {
                                return Err(err(at(tokens,expression),
                                    "cannot mutably reborrow a shared reference"));
                            }
                        }
                        let pointee=if reborrow{Some(inner)}else{match input {
                            ConstType::Ref(ty)|ConstType::RefMut(ty)=>Some(ty.as_ref()),
                            _=>None,
                        }};
                        let expected=match output {
                            Some(ConstType::Ref(ty)|ConstType::RefMut(ty))=>Some(ty.as_ref()),
                            _=>None,
                        };
                        if pointee.is_some() && expected.is_some() && pointee!=expected {
                            return Err(err(at(tokens,expression),
                                "returned reference pointee type mismatch"));
                        }
                    }
                }
                if matches!(fun.ret.as_ref(),Some(ConstType::RefMut(_))) {
                    //`&*x` always creates a shared reborrow, even when x itself is &mut. A shared child must never be
                    //promoted to &mut in an uncalled function
                    if by_borrow && !exclusive_borrow {
                        return Err(err(at(tokens,expression),
                            "cannot return a shared reborrow as a mutable reference"));
                    }
                    if !by_borrow {
                        if let Some(&index)=param_region.get(&candidate) {
                            if !matches!(&fun.params[index].1,ConstType::RefMut(_)) {
                                return Err(err(at(tokens,expression),
                                    "cannot return a shared reference as a mutable reference"));
                            }
                        }
                    }
                }
                if flow.is_local(candidate) && (by_borrow || flow.origin(source).is_some()) {
                    return Err(err(at(tokens,expression),
                        "reference escapes the lifetime of a local owner"));
                }
                if let (Some(signature),Some(&param_index))=
                    (fun.regions.as_ref(),param_region.get(&candidate)) {
                    if let (Some(source_region),Some(target))=
                        (signature.param[param_index],signature.result) {
                        if !signature.permits(source_region,target) {
                            return Err(err(at(tokens,expression),
                                "return lifetime does not outlive declared result region"));
                        }
                    }
                } else {
                    //A reference from any source other than a proven lifetime-bearing parameter is not a valid return A
                    //bare, unrelated local must not bypass this check
                    return Err(err(at(tokens,expression),
                        "returned reference is not derived from a reference parameter"));
                }
                Ok(())
            };
            for i in fun.body.clone() {
                if tokens[i].kind==K::Ident("return") {
                    check_source(i+1)?;
                }
            }
            let tail_start=(fun.body.start..fun.body.end).rev()
                .find(|&i|tokens[i].kind==K::Semi).map_or(fun.body.start,|i|i+1);
            if tail_start<fun.body.end {
                if tokens[tail_start].kind==K::Ident("if") {
                    let arms=reference_if_tail_arms(tokens,tail_start..fun.body.end)
                        .ok_or_else(||err(at(tokens,tail_start),
                            "cannot prove lifetime of non-exhaustive or composite reference if expression"))?;
                    for (condition,arm) in arms {
                        if let Some(condition)=condition {
                            if !pure_reference_condition(tokens,fun,condition) {
                                return Err(err(at(tokens,condition),
                                    "cannot prove pure boolean reference if condition"));
                            }
                        }
                        check_source(arm.start)?;
                    }
                }else if tokens[tail_start].kind==K::Ident("match") {
                    let arms=reference_match_tail_arms(tokens,tail_start..fun.body.end)
                        .ok_or_else(||err(at(tokens,tail_start),
                            "cannot prove lifetime of non-exhaustive or composite reference match expression"))?;
                    for (_,arm) in arms {check_source(arm.start)?;}
                }else{
                    check_source(tail_start)?;
                }
            } else if !(fun.body.clone()).any(|i|tokens[i].kind==K::Ident("return")) {
                return Err(err(at(tokens,fun.body.start),
                    "reference-returning function requires a return expression"));
            }
        }
        let mut verified_return_paths=HashMap::new();
        for (name,summary) in &verified_calls {
            let origins=summary.returned.iter()
                .chain(summary.returned_alternatives.iter())
                .map(|origin|ReferencePathOrigin{
                    parameter:origin.parameter,path:origin.fields.clone(),
                }).collect::<Vec<_>>();
            if !origins.is_empty() {verified_return_paths.insert(name.clone(),origins);}
        }
        Ok(verified_return_paths)
    }
    fn lower_main(mut self, main:Range<usize>)->Result<Vec<Stmt>,Diagnostic>{
        self.main(main)?;
        Ok(self.quantum)
    }
    fn finish(mut self)->Result<Vec<Stmt>,Diagnostic>{
        let main=self.parse_definitions()?;
        self.verified_return_paths=self.validate_function_bodies()?;
        self.lower_main(main)
    }
}

pub fn enabled(source:&str)->bool{
    source.lines().any(|line| {
        let code=line.split_once("//").map_or(line,|(before,_)|before);
        let generic_signature=code.find("fn ").is_some_and(|offset|{
            let signature=code[offset+3..].split('(').next().unwrap_or("");
            signature.contains('<') && signature.contains('>')
        });
        generic_signature || code.contains("impl ") || code.contains("->") || code.contains("<T>") ||
        (code.contains("fn ") && code.contains('\'')) ||
        code.contains("i64") || code.contains("u64") ||
        code.contains("struct ") || code.contains("enum ") ||
        code.contains("&self") || code.contains("&mut self") ||
        code.contains("&bool") || code.contains("&mut bool")
    })
}
fn finish_quantum_scopes(quantum:Vec<Stmt>)->Result<Vec<Stmt>,Diagnostic>{
    if quantum.iter().any(|stmt|matches!(stmt,Stmt::Block{..})) {
        crate::language::lower(&quantum)
    } else {Ok(quantum)}
}

pub fn compile(source:&str)->Result<crate::ir::Program,Diagnostic>{
    let tokens=syntax::lex(source)?;
    let quantum=finish_quantum_scopes(Front::new(tokens).finish()?)?;
    crate::sema::check(&quantum)
}

pub fn compile_timed(source:&str)->Result<(crate::ir::Program,std::time::Duration,std::time::Duration,std::time::Duration,std::time::Duration),Diagnostic>{
    let started=std::time::Instant::now();
    #[cfg(feature = "alloc-profile")]
    let alloc_stage=crate::alloc_profile::StageScope::enter(crate::alloc_profile::Stage::Lexer);
    let tokens=syntax::lex(source)?;
    #[cfg(feature = "alloc-profile")]
    drop(alloc_stage);
    let lex=started.elapsed();
    let started=std::time::Instant::now();
    #[cfg(feature = "alloc-profile")]
    let alloc_stage=crate::alloc_profile::StageScope::enter(crate::alloc_profile::Stage::Parser);
    let mut front=Front::new(tokens);
    let main=front.parse_definitions()?;
    #[cfg(feature = "alloc-profile")]
    drop(alloc_stage);
    let parse=started.elapsed();
    let started=std::time::Instant::now();
    #[cfg(feature = "alloc-profile")]
    let alloc_stage=crate::alloc_profile::StageScope::enter(crate::alloc_profile::Stage::Lowering);
    let quantum=finish_quantum_scopes(front.lower_main(main)?)?;
    #[cfg(feature = "alloc-profile")]
    drop(alloc_stage);
    let lower=started.elapsed();
    let started=std::time::Instant::now();
    #[cfg(feature = "alloc-profile")]
    let alloc_stage=crate::alloc_profile::StageScope::enter(crate::alloc_profile::Stage::Semantic);
    let program=crate::sema::check(&quantum)?;
    #[cfg(feature = "alloc-profile")]
    drop(alloc_stage);
    Ok((program,lex,parse,lower,started.elapsed()))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn compact_struct_positional_fields_preserve_source_order_independence() {
        let source="struct S{a:i64,b:i64,active:bool} fn main(){let s:S=S{active:true,b:7,a:5};let q=qubit();if s.active{rz(s.a+s.b,q);}else{x(q);}}";
        let expected=crate::compile("fn main(){let q=qubit();rz(12,q);}").unwrap();
        let program=good(source);
        assert_eq!(crate::sema::emit_qasm(&program),crate::sema::emit_qasm(&expected));
        assert_eq!(crate::qcu::encode(&program).unwrap(),crate::qcu::encode(&expected).unwrap());
    }
    #[test] fn compact_struct_ids_distinguish_types_and_track_moves() {
        let a="struct A{x:i64} struct B{x:i64} fn main(){let a:A=A{x:2};let b:B=B{x:2};static_assert_eq(a,b);}";
        assert!(bad(a).contains("types differ"));
        let moved="struct A{x:i64} fn main(){let a:A=A{x:2};let b:A=a;let q=qubit();rz(a.x,q);}";
        assert!(bad(moved).contains("moved"));
        let duplicate="struct A{x:i64,y:i64} fn main(){let a:A=A{x:1,x:2};}";
        assert!(bad(duplicate).contains("duplicate"));
    }
    #[test] fn compact_enum_ids_keep_variant_identity_and_ownership() {
        let a="enum A{X,Y} enum B{X,Y} fn main(){let a:A=A::X;let b:B=B::X;static_assert_eq(a,b);}";
        assert!(bad(a).contains("types differ"));
        let program=good("enum A{X,Y} fn main(){let a:A=A::Y;let q=qubit();match a{A::X=>{x(q);},A::Y=>{h(q);}}}");
        let expected=crate::compile("fn main(){let q=qubit();h(q);}").unwrap();
        assert_eq!(crate::qcu::encode(&program).unwrap(),crate::qcu::encode(&expected).unwrap());
    }
    #[test] fn unified_static_example_uses_checked_quantum_ir() {
        let source="struct Pulse{angle:i64,enabled:bool} enum Axis{X,Y,Z} fn main(){let mut step:u64=3;step+=1;let p:Pulse=Pulse{angle:4,enabled:true};let axis:Axis=Axis::Y;let q=qubit();rz(p.angle,q);match axis{Axis::Y=>{h(q);},_=>{x(q);}}static_assert_eq(step,4);}";
        let reference="fn main(){let q=qubit();rz(4,q);h(q);}";
        let actual=good(source);
        let expected=crate::compile(reference).unwrap();
        assert_eq!(crate::sema::emit_qasm(&actual),crate::sema::emit_qasm(&expected));
        assert_eq!(crate::qcu::encode(&actual).unwrap(),crate::qcu::encode(&expected).unwrap());
    }
    #[test] fn unified_match_requires_exhaustive_patterns() {
        let source="enum Axis{X,Y} fn main(){let a:Axis=Axis::Y;match a{Axis::X=>{}}}";
        assert!(bad(source).contains("nonexhaustive"));
        assert!(bad("enum Axis{X,Y} fn main(){let a:Axis=Axis::Y;match a{Axis::X=>{},Axis::X=>{},_=>{}}}")
            .contains("duplicate"));
        assert!(bad("enum A{X} enum B{X} fn main(){let a:A=A::X;match a{B::X=>{}}}")
            .contains("another enum"));
    }
    #[test] fn unified_match_moves_noncopy_enum() {
        let source="enum Axis{X,Y} fn main(){let a:Axis=Axis::Y;match a{Axis::X=>{},Axis::Y=>{}}static_assert_eq(a,Axis::Y);}";
        assert!(bad(source).contains("moved"));
    }
    #[test] fn unified_compound_overflow_and_immutable_rejected() {
        assert!(bad("fn main(){let mut x:i64=9223372036854775807;x+=1;}").contains("overflow"));
        assert!(bad("fn main(){let x:u64=3;x+=1;}").contains("immutable"));
        assert!(bad("fn main(){let mut x:u64=0;x-=1;}").contains("overflow"));
    }
    #[test] fn unified_standalone_statements_and_exact_64bit_values() {
        let program=good("let x:u64=18446744073709551615;static_assert_eq(x,18446744073709551615);let q=qubit();h(q);");
        assert_eq!(program.qubits,1);
        assert_eq!(program.instructions.len(),1);
    }
    #[test] fn unified_static_if_keeps_branch_selection_and_ownership() {
        let actual=good("fn main(){let a:i64=3;let yes:bool=a>2;let q=qubit();if yes{h(q);}else{x(q);}}");
        let expected=crate::compile("fn main(){let q=qubit();h(q);}").unwrap();
        assert_eq!(crate::sema::emit_qasm(&actual),crate::sema::emit_qasm(&expected));
        let nested=good("fn main(){let q=qubit();if false{x(q);}else if true{z(q);}else{h(q);}}");
        let ref_program=crate::compile("fn main(){let q=qubit();z(q);}").unwrap();
        assert_eq!(crate::qcu::encode(&nested).unwrap(),crate::qcu::encode(&ref_program).unwrap());
    }
    #[test] fn literal_bool_conditions_are_not_variable_lookups() {
        let source="fn main(){let q=qubit();if false{x(q);}else if true{z(q);}else{h(q);}}";
        let expected=crate::compile("fn main(){let q=qubit();z(q);}").unwrap();
        let actual=good(source);
        assert_eq!(crate::sema::emit_qasm(&actual),crate::sema::emit_qasm(&expected));
        assert_eq!(crate::qcu::encode(&actual).unwrap(),crate::qcu::encode(&expected).unwrap());
    }
    #[test] fn repeated_scopes_preserve_move_and_shadow_checks() {
        let src="struct S{x:i64} fn twice(a:i64)->i64{let x:i64=a*2;return x;} fn main(){let q=qubit();rz(twice(2)+twice(3)+twice(4),q);}";
        let program=good(src);
        assert_eq!(program.angles,&[18.0]);
        assert!(bad("struct S{x:i64} fn take(s:S)->i64{s.x} fn main(){let s:S=S{x:2};let q=qubit();rz(take(s),q);rz(take(s),q);}").contains("moved"));
    }
    #[test] fn field_copy_does_not_move_or_clone_aggregate() {
        let src="struct Big{x:i64,y:i64,z:i64,flag:bool} fn main(){let p:Big=Big{x:2,y:4,z:8,flag:true};let q=qubit();rx(p.x+p.y+p.z,q);if p.flag{h(q);}rz(p.x,q);}";
        let actual=good(src);
        let reference=crate::compile("fn main(){let q=qubit();rx(14,q);h(q);rz(2,q);}").unwrap();
        assert_eq!(crate::sema::emit_qasm(&actual),crate::sema::emit_qasm(&reference));
        assert_eq!(crate::qcu::encode(&actual).unwrap(),crate::qcu::encode(&reference).unwrap());
    }
    #[test] fn match_128_variants_and_reject_duplicate_and_nonexhaustive() {
        let variants=(0..128).map(|i|format!("V{i}")).collect::<Vec<_>>().join(",");
        let arms=(0..128).map(|i|format!("E::V{i}=>{{}}" )).collect::<Vec<_>>().join(",");
        let src=format!("enum E{{{variants}}} fn main(){{let e:E=E::V127;let q=qubit();match e{{{arms}}}h(q);}}");
        assert_eq!(good(&src).instructions.len(),1);
        let broken=format!("enum E{{{variants}}} fn main(){{let e:E=E::V0;match e{{E::V0=>{{}}}}}}");
        assert!(bad(&broken).contains("nonexhaustive"));
    }
    #[test] fn struct_initializer_checks_complete_and_duplicate_fields_without_copying_schema() {
        assert!(bad("struct S{a:i64,b:u64} fn main(){let s:S=S{a:3};}").contains("missing"));
        assert!(bad("struct S{a:i64,b:u64} fn main(){let s:S=S{a:3,a:4,b:2};}").contains("duplicate"));
        assert_eq!(good("struct S{a:i64,b:u64} fn main(){let s:S=S{a:3,b:2};let q=qubit();rz(s.a,q);}").angles,&[3.0]);
    }
    #[test] fn unified_match_preserves_qubit_alias_checks() {
        let source="enum Axis{X,Y} fn main(){let a:Axis=Axis::Y;let q=qubit();match a{Axis::X=>{h(q);},Axis::Y=>{cx(q,q);}}}";
        assert!(bad(source).contains("qubit")||bad(source).contains("distinct")||bad(source).contains("same"));
    }
    fn good(source:&str)->crate::ir::Program {compile(source).unwrap()}
    fn bad(source:&str)->String {compile(source).unwrap_err().message}
    #[test] fn same_scope_borrows_drop_before_lexical_escape_check() {
        let p=good("fn main(){let n:i64=4;let a:&i64=&n;let b:&i64=&n;let q=qubit();rx(*a+*b,q);}");
        assert_eq!(p.angles.as_slice(), &[8.0]);
        let p=good("fn main(){let mut n:i64=1;let r:&mut i64=&mut n;*r=8;let q=qubit();rz(*r,q);}");
        assert_eq!(p.angles.as_slice(), &[8.0]);
    }
    #[test] fn reference_to_callee_local_must_still_be_rejected() {
        let source="fn escape<'a>()->&'a i64{let n:i64=1;return &n;} fn main(){let r:&i64=escape();}";
        assert!(bad(source).contains("reference escapes"));
    }
    #[test] fn reference_types_and_shared_read() {
        let p=good("fn twice(x:&i64)->i64{*x*2} fn main(){let n:i64=9;let r:&i64=&n;let s:&i64=&n;let q=qubit();rx(twice(r),q);ry(*s,q);}");
        assert_eq!(p.angles.as_slice(), &[18.0,9.0]);
    }
    #[test] fn shared_method_may_return_a_borrowed_field() {
        let p=good("struct P{x:i64} impl P{fn view(&self)->&i64{&self.x}} fn main(){let p:P=P{x:12};let v:&i64=p.view();let q=qubit();rx(*v,q);}");
        assert_eq!(p.angles.as_slice(), &[12.0]);
    }
    #[test] fn mutable_reborrows_suspend_parent_until_scope_exit() {
        let p=good("fn main(){let mut n:i64=1;let r:&mut i64=&mut n;if true {let t:&mut i64=&mut *r;*t=8;}*r=9;let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles.as_slice(), &[9.0]);
        assert!(bad("fn main(){let mut n:i64=1;let r=&mut n;let t=&mut *r;*r=3;*t=4;}").contains("suspended"));
    }
    #[test] fn reference_mutations_update_owner() {
        let p=good("fn change(x:&mut i64,v:i64){*x=v;} fn main(){let mut n:i64=1;change(&mut n,7);let q=qubit();rx(n,q);}");
        assert_eq!(p.angles.as_slice(), &[7.0]);
        let p=good("fn change(x:&mut i64){*x+=3;} fn main(){let mut n:i64=2;change(&mut n);let q=qubit();rz(n,q);}");
        assert_eq!(p.angles.as_slice(), &[5.0]);
    }
    #[test] fn ref_receiver_preserves_aggregate_and_mut_receiver_changes_it() {
        let source="struct Pulse{angle:i64} impl Pulse{fn get(&self)->i64{self.angle} fn set(&mut self,v:i64){self.angle=v;}} fn main(){let mut p:Pulse=Pulse{angle:2};p.set(9);let q=qubit();rx(p.get(),q);ry(p.get(),q);}";
        let p=good(source);
        assert_eq!(p.angles.as_slice(), &[9.0,9.0]);
    }
    #[test] fn explicit_reference_field_and_disjoint_mut_borrows() {
        let p=good("struct Pair{x:i64,y:i64} fn main(){let mut p:Pair=Pair{x:3,y:4};if true {let a:&mut i64=&mut p.x;let b:&mut i64=&mut p.y;*a=10;*b=20;}let q=qubit();rx(p.x,q);ry(p.y,q);}");
        assert_eq!(p.angles.as_slice(), &[10.0,20.0]);
    }
    #[test] fn conflicting_borrows_rejected() {
        assert!(bad("fn main(){let mut n:i64=1;let a=&mut n;let b=&mut n;*a=3;}").contains("conflicting"));
        assert!(bad("fn main(){let mut n:i64=1;let a=&n;let b=&mut n;let q=qubit();rx(*a,q);}").contains("conflicting"));
        assert!(bad("fn main(){let mut n:i64=1;let a=&mut n;let b=&n;*a=3;}").contains("conflicting"));
        assert!(bad("fn main(){let n:i64=1;let a=&mut n;}").contains("immutable"));
        assert!(bad("fn main(){let mut n:i64=1;let a=&n;n=2;let q=qubit();rx(*a,q);}").contains("borrowed"));
        assert!(bad("fn main(){let mut n:i64=1;let a=&mut n;let q=qubit();rx(n,q);ry(*a,q);}").contains("borrow"));
    }
    #[test] fn borrowing_move_only_struct_does_not_move_and_blocks_move() {
        let p=good("struct P{x:i64} fn read(x:&P)->i64{x.x} fn main(){let p:P=P{x:9};let q=qubit();rx(read(&p),q);ry(p.x,q);}");
        assert_eq!(p.angles.as_slice(), &[9.0,9.0]);
        assert!(bad("struct P{x:i64} fn main(){let p:P=P{x:9};let a=&p;let b:P=p;let q=qubit();rx(a.x,q);}").contains("borrowed"));
    }
    #[test] fn reference_return_from_param_and_reject_local_escape() {
        let p=good("fn keep(x:&i64)->&i64{x} fn main(){let n:i64=4;let r:&i64=keep(&n);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles.as_slice(), &[4.0]);
        assert!(bad("fn escape<'a>()->&'a i64{let n:i64=1;return &n;} fn main(){let r:&i64=escape();let q=qubit();rx(*r,q);}").contains("reference escapes"));
    }
    #[test] fn reference_type_and_deref_errors() {
        assert!(bad("fn read(x:&i64)->i64{*x} fn main(){let n:i64=1;let q=qubit();rx(read(n),q);}").contains("type mismatch"));
        assert!(bad("fn main(){let n:i64=2;let r:i64=&n;}").contains("type mismatch"));
        assert!(bad("fn main(){let n:i64=2;let r:i64=*n;}").contains("dereference"));
    }
    #[test] fn reference_edition_preserves_quantum_output() {
        let old=good("fn main(){let q=qubit();rx(9,q);ry(4,q);}");
        let new=good("fn read(x:&i64)->i64{*x} fn main(){let n:i64=9;let r=&n;let q=qubit();rx(read(r),q);ry(4,q);}");
        assert_eq!(crate::sema::emit_qasm(&old),crate::sema::emit_qasm(&new));
    }
    #[test] fn nested_shared_references_deref_without_moving() {
        let src="fn main(){let n:i64=7;let r:&i64=&n;let rr:&&i64=&r;let rrr:&&&i64=&rr;let q=qubit();rx(**rr,q);ry(***rrr,q);rz(*r,q);}";
        let p=good(src);
        assert_eq!(p.angles.as_slice(), &[7.0,7.0,7.0]);
        let keep=good("fn read(x:&&i64)->i64{**x} fn main(){let n:i64=5;let r:&i64=&n;let q=qubit();rx(read(&r),q);}");
        assert_eq!(keep.angles.as_slice(), &[5.0]);
    }
    #[test] fn nested_reference_lifetime_and_type_guards() {
        assert!(bad("fn escape<'a>()->&'a &i64{let n:i64=1;let r:&i64=&n;return &r;} fn main(){let r:&&i64=escape();}").contains("reference escapes"));
        assert!(bad("fn read(x:&&Unknown)->i64{1} fn main(){let q=qubit();h(q);}").contains("unknown type"));
        assert!(bad("fn main(){let n:i64=1;let r:&i64=&n;let rr:&&i64=&r;let q=qubit();rx(***rr,q);}").contains("dereference"));
        let overly_nested=format!("fn read(x:{}i64)->i64{{1}} fn main(){{}}", "&".repeat(17));
        assert!(bad(&overly_nested).contains("nesting limit"));
    }
    #[test] fn call_mutable_reference_temporarily_reborrows() {
        let p=good("fn inc(x:&mut i64){*x+=1;} fn main(){let mut n:i64=3;let r:&mut i64=&mut n;inc(r);inc(r);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles.as_slice(), &[5.0]);
        let p=good("fn change(x:&mut i64){*x=8;} fn main(){let mut n:i64=1;let r:&mut i64=&mut n;change(r);let q=qubit();ry(*r,q);}");
        assert_eq!(p.angles.as_slice(), &[8.0]);
    }
    #[test] fn mutable_reference_can_be_shared_temporarily() {
        let p=good("fn read(x:&i64)->i64{*x} fn bump(x:&mut i64){*x+=2;} fn main(){let mut n:i64=2;let r:&mut i64=&mut n;let q=qubit();rx(read(r),q);bump(r);ry(read(r),q);}");
        assert_eq!(p.angles.as_slice(), &[2.0,4.0]);
        assert!(bad("fn both(a:&mut i64,b:&i64){} fn main(){let mut n:i64=1;let r:&mut i64=&mut n;both(r,r);}").contains("reborrow"));
        assert!(bad("fn read(x:&mut i64){} fn main(){let n:i64=1;let r=&n;read(r);}").contains("type mismatch"));
    }
    #[test] fn nll_releases_unused_and_last_used_shared_reference() {
        let p=good("fn main(){let mut x:i64=3;let a=&x;let b=&mut x;*b=8;let q=qubit();rx(x,q);}");
        assert_eq!(p.angles.as_slice(),&[8.0]);
        let p=good("fn main(){let mut x:i64=4;let a=&x;let q=qubit();rx(*a,q);x=7;ry(x,q);}");
        assert_eq!(p.angles.as_slice(),&[4.0,7.0]);
    }
    #[test] fn nll_releases_mutable_reference_after_last_read() {
        let p=good("fn main(){let mut n:i64=1;let r=&mut n;*r=8;let q=qubit();rx(*r,q);n=9;ry(n,q);}");
        assert_eq!(p.angles.as_slice(),&[8.0,9.0]);
        assert!(bad("fn main(){let mut n:i64=1;let r=&mut n;n=9;let q=qubit();rx(*r,q);}").contains("borrow"));
    }
    #[test] fn nll_does_not_drop_reference_used_from_nested_borrow() {
        let p=good("fn main(){let mut n:i64=3;let r=&n;let rr= &r;let q=qubit();rx(**rr,q);n=8;ry(n,q);}");
        assert_eq!(p.angles.as_slice(),&[3.0,8.0]);
    }
    #[test] fn reborrow_chains_allow_multiple_shared_siblings() {
        let p=good("fn main(){let mut n:i64=3;let r=&mut n;let a=&*r;let b=&*r;let q=qubit();rx(*a+*b,q);*r=7;ry(*r,q);}");
        assert_eq!(p.angles.as_slice(),&[6.0,7.0]);
        assert!(bad("fn main(){let mut n:i64=1;let r=&mut n;let a=&*r;let b=&mut *r;let q=qubit();rx(*a,q);}").contains("reborrow"));
    }
    #[test] fn reborrow_chains_suspend_two_mutable_levels() {
        let p=good("fn main(){let mut n:i64=1;let a=&mut n;let b=&mut *a;let c=&mut *b;*c=11;let q=qubit();rx(*c,q);*b=12;ry(*b,q);*a=13;rz(*a,q);}");
        assert_eq!(p.angles.as_slice(),&[11.0,12.0,13.0]);
    }
    #[test] fn inferred_function_results_are_typed_not_quantum_declarations() {
        let scalar=good("fn id(x:i64)->i64{x} fn main(){let answer=id(9);let q=qubit();rx(answer,q);}");
        assert_eq!(scalar.angles.as_slice(),&[9.0]);
        let returned=good("fn forward(x:&mut i64)->&mut i64{x} fn main(){let mut n:i64=3;let r=&mut n;let s=forward(r);*s=10;let q=qubit();rx(*s,q);}");
        assert_eq!(returned.angles.as_slice(),&[10.0]);
    }
    #[test] fn lifetime_propagation_returns_original_place() {
        let p=good("fn forward(x:&mut i64)->&mut i64{x} fn main(){let mut n:i64=3;let r=&mut n;let s=forward(r);*s=10;let q=qubit();rx(*s,q);}");
        assert_eq!(p.angles.as_slice(),&[10.0]);
        assert!(bad("fn escape<'a>()->&'a i64{let x:i64=1;let a=&x;return a;} fn main(){let a=escape();}").contains("reference escapes"));
    }
    #[test] fn region_060_named_shared_reference_survives_call() {
        let p=good("fn identity<'a>(x:&'a i64)->&'a i64{x} fn main(){let n:i64=7;let r=identity(&n);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles,&[7.0]);
    }
    #[test] fn region_060_mutable_ref_preserves_origin_and_ownership() {
        let p=good("fn identity<'a>(x:&'a mut i64)->&'a mut i64{x} fn main(){let mut n:i64=3;let r=identity(&mut n);*r=11;let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles,&[11.0]);
        assert!(bad("fn identity<'a>(x:&'a mut i64)->&'a mut i64{x} fn main(){let mut n:i64=3;let r=identity(&mut n);n=5;let q=qubit();rx(*r,q);}").contains("borrow"));
    }
    #[test] fn region_060_illegal_return_from_independent_lifetime() {
        let source="fn wrong<'a,'b>(x:&'a i64,y:&'b i64)->&'a i64{y} fn main(){let a:i64=1;let b:i64=2;let r=wrong(&a,&b);let q=qubit();rx(*r,q);}";
        assert!(bad(source).contains("lifetime does not outlive"));
    }
    #[test] fn region_060_explicit_where_bound_enables_safe_shorten() {
        let p=good("fn shorten<'a,'b>(x:&'b i64)->&'a i64 where 'b:'a {x} fn main(){let n:i64=9;let r=shorten(&n);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles,&[9.0]);
        assert!(bad("fn wrong<'a,'b>(x:&'b i64)->&'a i64 where 'a:'b {x} fn main(){let n:i64=9;let r=wrong(&n);}").contains("lifetime does not outlive"));
    }
    #[test] fn region_060_transitive_where_constraints() {
        let p=good("fn trans<'a,'b,'c>(x:&'a i64)->&'c i64 where 'a:'b,'b:'c {x} fn main(){let n:i64=17;let r=trans(&n);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles,&[17.0]);
    }
    #[test] fn region_060_undeclared_duplicate_and_elision_rules() {
        assert!(bad("fn f<'a>(x:&'b i64)->&'a i64{x} fn main(){}").contains("undeclared lifetime"));
        assert!(bad("fn f<'a,'a>(x:&'a i64)->&'a i64{x} fn main(){}").contains("duplicate lifetime"));
        assert!(bad("fn f<'a,'b>(x:&'a i64,y:&'b i64)->&i64{x} fn main(){}").contains("missing lifetime specifier"));
        assert!(bad("fn f<'static>(x:&'static i64)->&'static i64{x} fn main(){}").contains("cannot be lifetime parameters"));
    }
    #[test] fn region_060_single_input_elided_output() {
        let p=good("fn f<'a>(x:&'a i64)->&i64{x} fn main(){let n:i64=6;let r=f(&n);let q=qubit();ry(*r,q);}");
        assert_eq!(p.angles,&[6.0]);
    }
    #[test] fn region_060_declared_lifetime_can_mix_with_type_parameter() {
        let p=good("fn identity<'a,T>(x:&'a T)->&'a T{x} fn main(){let n:i64=5;let r=identity(&n);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles,&[5.0]);
    }
    #[test] fn region_060_method_borrowed_receiver() {
        let p=good("struct P{n:i64} impl P{fn get<'a>(&'a self)->&'a i64{&self.n}} fn main(){let p:P=P{n:13};let r=p.get();let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles,&[13.0]);
    }
    #[test] fn region_060_bool_only_signature_uses_typed_frontend() {
        let src="fn read<'a>(x:&'a bool){let v:bool=*x;} fn main(){let v:bool=true;read(&v);let q=qubit();h(q);}";
        assert!(enabled(src));
        assert_eq!(good(src).qubits,1);
    }
    #[test] fn region_060_static_references_need_real_static_storage() {
        assert!(bad("fn f(x:&'static i64)->&'static i64{x} fn main(){let n:i64=1;let r=f(&n);}").contains("static storage"));
    }
    #[test] fn region_060_reborrow_parent_is_valid_provenance() {
        let p=good("fn f<'a>(x:&'a i64)->&'a i64{&*x} fn main(){let n:i64=19;let r=f(&n);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles,&[19.0]);
    }
    #[test] fn region_060_named_lifetime_preserves_qasm_and_qcu() {
        let named=good(include_str!("../benchmark_fixtures/region_named_060.qr"));
        let flat=crate::compile(include_str!("../benchmark_fixtures/region_named_060_flat.qr")).unwrap();
        assert_eq!(crate::sema::emit_qasm(&named),crate::sema::emit_qasm(&flat));
        assert_eq!(crate::qcu::encode(&named).unwrap(),crate::qcu::encode(&flat).unwrap());
    }
    #[test] fn cfg_while_fixed_point_preserves_repeated_reference_reads() {
        let code="fn main(){let mut i:i64=0;let mut n:i64=3;let r=&n;let q=qubit();while i<3{rx(*r,q);i+=1;}n=8;ry(n,q);}";
        let flat="fn main(){let q=qubit();rx(3,q);rx(3,q);rx(3,q);ry(8,q);}";
        let compiled=good(code);let baseline=crate::compile(flat).unwrap();
        assert_eq!(compiled.angles,baseline.angles);
        assert_eq!(crate::sema::emit_qasm(&compiled),crate::sema::emit_qasm(&baseline));
        assert_eq!(crate::qcu::encode(&compiled).unwrap(),crate::qcu::encode(&baseline).unwrap());
    }
    #[test] fn cfg_while_mutable_reborrow_each_iteration() {
        let p=good("fn main(){let mut n:i64=0;let mut i:i64=0;let q=qubit();while i<3{let r=&mut n;*r+=1;i+=1;}rx(n,q);}");
        assert_eq!(p.angles,&[3.0]);
    }
    #[test] fn cfg_for_range_compiles_and_releases_borrows() {
        let p=good("fn main(){let mut n:i64=2;let q=qubit();for i in 0..3{let r=&mut n;*r+=i;}rx(n,q);}");
        assert_eq!(p.angles,&[5.0]);
        let p=good("fn main(){let q=qubit();for i in 1..=3{rx(i,q);}}");
        assert_eq!(p.angles,&[1.0,2.0,3.0]);
    }
    #[test] fn cfg_break_and_continue_propagate_from_nested_if() {
        let p=good("fn main(){let q=qubit();let mut i:i64=0;let mut total:i64=0;while i<6{i+=1;if i==2{continue;}if i==4{break;}total+=i;}rx(total,q);}");
        assert_eq!(p.angles,&[4.0]);
    }
    #[test] fn cfg_break_from_match_and_nested_loops() {
        let p=good("enum Mode{Stop,Run} fn main(){let mode:Mode=Mode::Stop;let mut n:i64=0;let q=qubit();for i in 0..5{match mode{Mode::Stop=>{break;},Mode::Run=>{}}n+=i;}rx(n,q);}");
        assert_eq!(p.angles,&[0.0]);
        let p=good("fn main(){let mut n:i64=0;let q=qubit();for i in 0..3{for j in 0..3{if j==1{break;}n+=1;}}rx(n,q);}");
        assert_eq!(p.angles,&[3.0]);
    }
    #[test] fn cfg_if_identifier_rhs_is_not_a_struct_literal() {
        let p=good("fn find(x:i64)->i64{for i in 0..5{if i==x{return i;}}return 7;} fn main(){let q=qubit();rx(find(3),q);}");
        assert_eq!(p.angles,&[3.0]);
        let p=good("fn main(){let a:i64=2;let b:i64=4;let q=qubit();if a<b{h(q);}else{x(q);}}");
        let expected=crate::compile("fn main(){let q=qubit();h(q);}").unwrap();
        assert_eq!(crate::sema::emit_qasm(&p),crate::sema::emit_qasm(&expected));
    }
    #[test] fn cfg_if_grouped_struct_condition_retains_initializer_braces() {
        let p=good("struct Flag{n:i64} fn main(){let q=qubit();if (Flag{n:2}.n==2){h(q);}else{x(q);}}");
        let expected=crate::compile("fn main(){let q=qubit();h(q);}").unwrap();
        assert_eq!(crate::qcu::encode(&p).unwrap(),crate::qcu::encode(&expected).unwrap());
    }
    #[test] fn typed_temporary_struct_field_projection_is_an_expression() {
        let p=good("struct Flag{n:i64} fn main(){let n:i64=Flag{n:3}.n;let q=qubit();rx(n,q);}");
        assert_eq!(p.angles,&[3.0]);
        let p=good("struct Flag{n:i64} fn main(){let q=qubit();if Flag{n:2}.n==2{h(q);}else{x(q);}}");
        let expected=crate::compile("fn main(){let q=qubit();h(q);}").unwrap();
        assert_eq!(crate::sema::emit_qasm(&p),crate::sema::emit_qasm(&expected));
        assert!(bad("struct Flag{n:i64} fn main(){let q=qubit();if (Flag{n:2}.missing==2){h(q);}}").contains("unknown struct field"));
    }
    #[test] fn cfg_return_from_loop_preserves_function_call_isolation() {
        let p=good("fn count()->i64{let mut n:i64=0;loop{n+=1;if n==3{return n;}}} fn main(){let q=qubit();rx(count(),q);}");
        assert_eq!(p.angles,&[3.0]);
        let p=good("fn find(x:i64)->i64{for i in 0..5{if i==x{return i;}}return 7;} fn main(){let q=qubit();rx(find(3),q);}");
        assert_eq!(p.angles,&[3.0]);
    }
    #[test] fn cfg_loop_rejects_outside_control_and_iteration_overflow() {
        assert!(bad("fn main(){break;}").contains("outside typed loop"));
        assert!(bad("fn main(){continue;}").contains("outside typed loop"));
        assert!(bad("fn main(){for i in 0..100001{}}").contains("iteration limit"));
        assert!(bad("fn main(){while 3{break;}}").contains("compile-time bool"));
    }
    #[test] fn cfg_loop_lifetime_cannot_escape_iteration_owner() {
        let source="fn bad_ref<'a>()->&'a i64{for i in 0..1{let local:i64=i;return &local;}let end:i64=2;return &end;} fn main(){let r=bad_ref();}";
        assert!(bad(source).contains("reference escapes"));
    }
    #[test] fn cfg_loop_output_is_byte_identical_to_flat() {
        let actual=good(include_str!("../benchmark_fixtures/reference_cfg_loops_0523.qr"));
        let control=crate::compile(include_str!("../benchmark_fixtures/reference_cfg_loops_0523_flat.qr")).unwrap();
        assert_eq!(crate::sema::emit_qasm(&actual),crate::sema::emit_qasm(&control));
        assert_eq!(crate::qcu::encode(&actual).unwrap(),crate::qcu::encode(&control).unwrap());
    }
    #[test] fn cfg_loop_liveness_rejects_mutation_before_future_read() {
        let source="fn main(){let mut x:i64=1;let r=&x;let q=qubit();let mut i:i64=0;while i<2{x=9;rx(*r,q);i+=1;}}";
        assert!(bad(source).contains("borrow"));
    }
    #[test] fn cfg_if_join_releases_outer_reference_after_last_branch_use() {
        let source="fn main(){let mut n:i64=3;let r=&n;if true{let q=qubit();rx(*r,q);}else{let q=qubit();h(q);}n=8;let q=qubit();ry(n,q);}";
        let p=good(source);
        assert_eq!(p.angles.as_slice(),&[3.0,8.0]);
    }
    #[test] fn cfg_match_join_releases_outer_reference_after_last_arm_use() {
        let source="enum Mode{A,B} fn main(){let mut n:i64=4;let r=&n;let m:Mode=Mode::A;match m{Mode::A=>{let q=qubit();rx(*r,q);},Mode::B=>{}}n=9;let q=qubit();ry(n,q);}";
        let p=good(source);
        assert_eq!(p.angles.as_slice(),&[4.0,9.0]);
    }
    #[test] fn cfg_nested_if_and_match_keep_outer_continuation() {
        let source="enum Mode{A,B} fn main(){let mut n:i64=3;let r=&n;let m:Mode=Mode::B;if true{match m{Mode::A=>{},Mode::B=>{let q=qubit();rx(*r,q);}}}else{}n=10;let q=qubit();ry(n,q);}";
        let p=good(source);
        assert_eq!(p.angles.as_slice(),&[3.0,10.0]);
    }
    #[test] fn cfg_if_different_paths_have_different_live_loans() {
        let source="fn main(){let mut n:i64=1;let r=&n;if false{let q=qubit();rx(*r,q);}else{n=7;let q=qubit();ry(n,q);}}";
        let p=good(source);
        assert_eq!(p.angles.as_slice(),&[7.0]);
    }
    #[test] fn cfg_match_disjoint_paths_allow_inactive_loan_to_end() {
        let source="enum Axis{X,Y} fn main(){let mut n:i64=1;let r=&n;let a:Axis=Axis::Y;match a{Axis::X=>{let q=qubit();rx(*r,q);},Axis::Y=>{n=9;let q=qubit();ry(n,q);}}}";
        let p=good(source);
        assert_eq!(p.angles.as_slice(),&[9.0]);
    }
    #[test] fn cfg_branch_lowering_preserves_qasm_and_qcu() {
        let branch=good("enum Mode{A,B} fn main(){let mut n:i64=3;let r=&n;let m:Mode=Mode::B;if true{match m{Mode::A=>{},Mode::B=>{let q=qubit();rx(*r,q);}}}n=9;let q=qubit();ry(n,q);}");
        let flat=crate::compile("fn main(){let q=qubit();rx(3,q);let q2=qubit();ry(9,q2);}").unwrap();
        assert_eq!(crate::sema::emit_qasm(&branch),crate::sema::emit_qasm(&flat));
        assert_eq!(crate::qcu::encode(&branch).unwrap(),crate::qcu::encode(&flat).unwrap());
    }
    #[test] fn cfg_does_not_drop_borrow_that_is_used_after_branch() {
        let source="fn main(){let mut n:i64=3;let r=&n;if true{let q=qubit();h(q);}else{}n=8;let q=qubit();rx(*r,q);}";
        assert!(bad(source).contains("borrow"));
    }
    #[test] fn cfg_preserves_reborrow_exclusivity_across_if() {
        let source="fn main(){let mut n:i64=1;let r=&mut n;if true{let c=&mut *r;*r=2;*c=5;}let q=qubit();rx(*r,q);}";
        assert!(bad(source).contains("suspended"));
    }
    #[test] fn cfg_keeps_borrow_until_last_use_in_second_branch() {
        let source="fn main(){let n:i64=3;let r=&n;if true{let q=qubit();rx(*r,q);}else{}let q=qubit();ry(*r,q);}";
        let p=good(source);
        assert_eq!(p.angles.as_slice(),&[3.0,3.0]);
    }
    #[test] fn place_tracking_disjoint_fields_and_deref_aliases() {
        let p=good("struct Pair{x:i64,y:i64} fn main(){let mut p:Pair=Pair{x:1,y:2};let a=&mut p.x;let b=&mut p.y;*a=7;*b=8;let q=qubit();rx(p.x,q);ry(p.y,q);}");
        assert_eq!(p.angles.as_slice(),&[7.0,8.0]);
        assert!(bad("struct P{x:i64} fn main(){let mut p:P=P{x:1};let a=&mut p.x;let b=&mut p.x;*a=3;}").contains("conflicting"));
    }
    #[test] fn direct_typed_return_to_checked_ir() {
        let p=good("fn twice(x:i64)->i64{return x*2;} fn main(){let q=qubit();rz(twice(3),q);}");
        assert_eq!(p.qubits,1);assert_eq!(p.angles.as_slice(),&[6.0]);
    }
    #[test] fn monomorphized_exact_generic_values() {
        let p=good("fn plus<T>(x:T,y:T)->T{x+y} fn main(){let x:u64=4;let q=qubit();rx(plus(x,3),q);}");
        assert_eq!(p.angles.as_slice(),&[7.0]);
        assert!(bad("fn plus<T>(x:T,y:T)->T{x+y} fn main(){let x:u64=4;let y:i64=3;let q=qubit();rx(plus(x,y),q);}")
            .contains("type mismatch"));
    }
    #[test] fn impl_method_moves_aggregate_receiver() {
        let p=good("struct Pulse{angle:i64} impl Pulse{fn angle(self)->i64{self.angle}} fn main(){let p:Pulse=Pulse{angle:5};let q=qubit();rz(p.angle(),q);}");
        assert_eq!(p.angles.as_slice(),&[5.0]);
        assert!(bad("struct Pulse{angle:i64} impl Pulse{fn angle(self)->i64{self.angle}} fn main(){let p:Pulse=Pulse{angle:5};let q=qubit();rz(p.angle(),q);rz(p.angle(),q);}")
            .contains("moved value"));
    }
    #[test] fn moving_a_struct_invalidates_source() {
        assert!(bad("struct Boxed{value:i64} fn main(){let p:Boxed=Boxed{value:5};let q:Boxed=p;let x=qubit();rx(p.value,x);}")
            .contains("moved value"));
        let p=good("struct Boxed{value:i64} fn main(){let p:Boxed=Boxed{value:5};let q:Boxed=p;let x=qubit();rx(q.value,x);}");
        assert_eq!(p.angles.as_slice(),&[5.0]);
    }
    #[test] fn exact_unsigned_and_enum_can_return_without_f64() {
        let p=good("enum Axis{X,Y} fn id<T>(x:T)->T{return x;} fn main(){let max:u64=18446744073709551615;let m:u64=id(max);static_assert_eq(m,18446744073709551615);let a:Axis=Axis::Y;let b:Axis=id(a);static_assert_eq(b,Axis::Y);let q=qubit();h(q);}");
        assert_eq!(p.qubits,1);
        assert!(bad("fn id(x:u64)->u64{x} fn main(){let max:u64=18446744073709551615;let q=qubit();rz(id(max),q);}")
            .contains("f64 QPU boundary"));
    }
    #[test] fn overflow_and_borrow_checks_preserved() {
        assert!(bad("fn inc(x:i64)->i64{x+1} fn main(){let q=qubit();rz(inc(9223372036854775807),q);}")
            .contains("overflow"));
        assert!(bad("fn id(x:i64)->i64{x} fn main(){let q=qubit();cx(q,q);}")
            .contains("distinct"));
    }
    #[test] fn no_source_text_rewrite_or_second_lexing() {
        let src="fn id(x:i64)->i64{return x;} fn main(){let q=qubit();rz(id(7),q);}";
        let direct=compile(src).unwrap();
        let (timed, lex, parse, lower, check)=compile_timed(src).unwrap();
        assert_eq!(timed.angles,direct.angles);
        assert!(lex.as_nanos()>0);assert!(parse.as_nanos()>0);assert!(lower.as_nanos()>0);assert!(check.as_nanos()>0);
    }
    #[test] fn repeated_function_calls_keep_token_ranges_and_exact_values() {
        let src="fn id<T>(x:T)->T{x} fn twice(x:i64)->i64{x*2} fn main(){let q=qubit();rx(twice(id(4)),q);ry(twice(id(5)),q);}";
        let program=good(src);
        assert_eq!(program.angles.as_slice(), &[8.0,10.0]);
        let tokens=syntax::lex(src).unwrap();
        let mut front=Front::new(tokens);
        let main=front.parse_definitions().unwrap();
        assert!(main.start < main.end);
        assert_eq!(Rc::strong_count(&front.cur.tokens),1);
        let bodies:Vec<_>=front.fn_defs.iter().map(|f|f.body.clone()).collect();
        assert_eq!(bodies.len(),3);
        assert!(bodies.iter().all(|b|b.start<b.end));
    }
    #[test] fn direct_borrowed_quantum_statement_parser_matches_owned() {
        let src="let q=qubit();h(q);";
        let tokens=syntax::lex(src).unwrap();
        let borrowed=syntax::Parser::from_slice(&tokens).parse().unwrap();
        let owned=syntax::Parser::new(tokens.clone()).parse().unwrap();
        let left=crate::sema::check(&borrowed.statements).unwrap();
        let right=crate::sema::check(&owned.statements).unwrap();
        assert_eq!(crate::sema::emit_qasm(&left),crate::sema::emit_qasm(&right));
    }
    #[test] fn parser_and_typed_lowering_report_distinct_nonzero_stages() {
        let src="fn twice(x:i64)->i64{x*2} fn main(){let q=qubit();rx(twice(7),q);}";
        let (program,lex,parse,lower,sema)=compile_timed(src).unwrap();
        assert_eq!(program.angles.as_slice(), &[14.0]);
        assert!(lex.as_nanos()>0 && parse.as_nanos()>0 && lower.as_nanos()>0 && sema.as_nanos()>0);
    }

}

#[cfg(test)]
mod cfg_061_symbol_region_tests {
    use super::*;
    #[test]fn shadowed_reference_uses_outer_borrow_after_inner_scope(){
        let source="fn main(){let mut x:i64=1;let r=&x;if true {let x:i64=2;let r=&x;let y:i64=*r;}let y:i64=*r;}";
        assert!(compile(source).is_ok());
    }
    #[test]fn uncalled_function_cannot_return_reference_to_local(){
        let src="fn invalid<'a>(x:&'a i64)->&'a i64 {let tmp:i64=2;return &tmp;} fn main(){}";
        assert!(compile(src).unwrap_err().message.contains("reference escapes"));
    }
    #[test]fn uncalled_tail_reference_to_local_is_rejected(){
        let src="fn invalid<'a>(x:&'a i64)->&'a i64 {let tmp:i64=2;&tmp} fn main(){}";
        assert!(compile(src).unwrap_err().message.contains("reference escapes"));
    }
    #[test]fn uncalled_function_lifetime_constraint_is_checked(){
        let src="fn invalid<'a,'b>(x:&'b i64)->&'a i64{return x;} fn main(){}";
        assert!(compile(src).unwrap_err().message.contains("lifetime"));
    }
    #[test]fn unused_function_break_outside_loop_is_rejected(){
        let src="fn broken(){break;} fn main(){}";
        assert!(compile(src).unwrap_err().message.contains("outside a static loop"));
    }
    #[test]fn unused_function_simple_type_error_is_checked(){
        let src="fn broken()->i64 {let n:bool=42;return 1;} fn main(){}";
        assert!(compile(src).unwrap_err().message.contains("initializer type mismatch"));
    }
    #[test]fn uncalled_valid_function_does_not_emit_quantum_instructions(){
        let a=compile("fn id<'a>(x:&'a i64)->&'a i64{return x;} fn main(){let q=qubit();h(q);}").unwrap();
        let b=compile("fn main(){let q=qubit();h(q);}").unwrap();
        assert_eq!(crate::qcu::encode(&a).unwrap(),crate::qcu::encode(&b).unwrap());
    }
}

#[cfg(test)]
mod region_bridge_tests_062 {
    fn good(src:&str)->crate::ir::Program{
        crate::compile(src).expect("0.6.2 region bridge should accept this safe program")
    }
    #[test]
    fn outer_shared_reference_remains_available_through_nested_scope() {
        let got=good("fn main(){let n:i64=4;let r:&i64=&n;if true{let t:&i64=&*r;let q=qubit();rz(*t,q);}let q2=qubit();rx(*r,q2);}");
        let expected=good("fn main(){let q=qubit();rz(4,q);let q2=qubit();rx(4,q2);}");
        assert_eq!(crate::sema::emit_qasm(&got),crate::sema::emit_qasm(&expected));
        assert_eq!(crate::qcu::encode(&got).unwrap(),crate::qcu::encode(&expected).unwrap());
    }
    #[test]
    fn independent_mutable_loans_still_reject_and_shared_loans_remain_valid() {
        let invalid="fn main(){let mut n:i64=1;let a=&mut n;let b=&mut n;let q=qubit();rx(*a+*b,q);}";
        assert!(crate::compile(invalid).is_err());
        let valid=good("fn main(){let n:i64=2;let a=&n;let b=&n;let q=qubit();rx(*a+*b,q);}");
        let expected=good("fn main(){let q=qubit();rx(4,q);}");
        assert_eq!(crate::sema::emit_qasm(&valid),crate::sema::emit_qasm(&expected));
    }
}

#[cfg(test)]
mod typed_rust_port_tests_066 {
    #[test] fn copy_scalar_does_not_move_original() {
        let compiled=crate::compile("fn main(){let x:i64=3;let y:i64=x;let q=qubit();rx(x,q);ry(y,q);}").unwrap();
        assert_eq!(compiled.angles.as_slice(),&[3.0,3.0]);
    }
    #[test] fn moving_aggregate_invalidates_original() {
        let diagnostic=crate::compile("struct S{a:i64,b:i64} fn main(){let x:S=S{a:3,b:4};let y:S=x;let q=qubit();rx(x.a,q);}").unwrap_err().message;
        assert!(diagnostic.contains("moved"),"{diagnostic}");
    }
    #[test] fn mutable_write_to_disjoint_field_preserves_shared_loan() {
        let program=crate::compile("struct S{a:i64,b:i64} fn main(){let mut x:S=S{a:3,b:4};let r=&x.a;x.b=9;let q=qubit();rx(*r,q);ry(x.b,q);}").unwrap();
        assert_eq!(program.angles.as_slice(),&[3.0,9.0]);
    }
    #[test] fn write_to_borrowed_field_is_still_rejected() {
        let diagnostic=crate::compile("struct S{a:i64,b:i64} fn main(){let mut x:S=S{a:3,b:4};let r=&x.a;x.a=9;let q=qubit();rx(*r,q);}").unwrap_err().message;
        assert!(diagnostic.contains("borrow"),"{diagnostic}");
    }
}

#[cfg(test)]
mod rust_move_path_tests_067 {
    use super::*;
    fn good(src:&str)->crate::ir::Program {compile(src).unwrap()}
    fn bad(src:&str)->String {compile(src).unwrap_err().message}
    const TYPES:&str="struct Boxed{value:i64} struct Pair{left:Boxed,right:Boxed}";

    #[test]
    fn move_left_field_and_use_right_sibling() {
        let source=format!("{TYPES} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let l:Boxed=p.left;let q=qubit();rx(p.right.value,q);ry(l.value,q);}}");
        assert_eq!(good(&source).angles.as_slice(),&[7.0,3.0]);
    }

    #[test]
    fn moving_field_blocks_whole_struct_and_repeated_field_move() {
        let root=format!("{TYPES} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let l:Boxed=p.left;let full:Pair=p;}}");
        assert!(bad(&root).contains("partially moved"));
        let twice=format!("{TYPES} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let a:Boxed=p.left;let b:Boxed=p.left;}}");
        assert!(bad(&twice).contains("moved field"));
    }

    #[test]
    fn reinitializing_moved_field_restores_entire_aggregate() {
        let source=format!("{TYPES} fn main(){{let mut p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let l:Boxed=p.left;p.left=Boxed{{value:10}};let all:Pair=p;let q=qubit();rx(all.left.value,q);ry(all.right.value,q);}}");
        assert_eq!(good(&source).angles.as_slice(),&[10.0,7.0]);
    }

    #[test]
    fn moved_field_may_not_be_borrowed_but_sibling_may() {
        let source=format!("{TYPES} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let l:Boxed=p.left;let r=&p.right;let q=qubit();rz(r.value,q);}}");
        assert_eq!(good(&source).angles.as_slice(),&[7.0]);
        let bad_source=format!("{TYPES} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let l:Boxed=p.left;let r=&p.left;}}");
        assert!(bad(&bad_source).contains("moved"));
    }

    #[test]
    fn noncopy_field_cannot_move_out_of_shared_or_mutable_reference() {
        let borrowed=format!("{TYPES} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let r=&p;let x:Boxed=r.left;}}");
        assert!(bad(&borrowed).contains("cannot move non-Copy field out of a reference"));
        let mut_borrowed=format!("{TYPES} fn main(){{let mut p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let r=&mut p;let x:Boxed=r.left;}}");
        assert!(bad(&mut_borrowed).contains("cannot move non-Copy field out of a reference"));
    }

    #[test]
    fn compound_assignment_on_moved_field_is_rejected() {
        let source=format!("{TYPES} fn main(){{let mut p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let a:Boxed=p.left;p.left+=Boxed{{value:2}};}}");
        let message=bad(&source);
        assert!(message.contains("moved")||message.contains("unsupported"),"{message}");
    }

    #[test]
    fn reassign_sibling_through_mutable_reference_after_partial_move() {
        let source=format!("{TYPES} fn main(){{let mut p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let a:Boxed=p.left;let r:&mut Boxed=&mut p.right;*r=Boxed{{value:9}};let q=qubit();rx(a.value,q);}}");
        assert_eq!(good(&source).angles.as_slice(),&[3.0]);
    }

    #[test]
    fn partial_move_rejects_whole_owner_borrow() {
        let source=format!("{TYPES} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let a:Boxed=p.left;let all=&p;}}");
        assert!(bad(&source).contains("partially moved"));
    }

    #[test]
    fn reinitialization_still_checks_declared_field_type() {
        let source=format!("{TYPES} fn main(){{let mut p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let a:Boxed=p.left;p.left=12;}}");
        assert!(bad(&source).contains("type mismatch"));
    }

    #[test]
    fn shared_reference_to_field_keeps_loan_active_until_last_call() {
        let source=format!("{TYPES} fn get(x:&Boxed)->i64{{x.value}} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let r=&p.left;let a:Boxed=p.left;let q=qubit();rx(get(r),q);}}");
        assert!(bad(&source).contains("borrow"));
    }

    #[test]
    fn borrowed_live_field_blocks_move_and_remains_usable() {
        let source=format!("{TYPES} fn main(){{let p:Pair=Pair{{left:Boxed{{value:3}},right:Boxed{{value:7}}}};let r=&p.left;let m:Boxed=p.left;let q=qubit();rz(r.value,q);}}");
        assert!(bad(&source).contains("borrow"));
    }
}

#[cfg(test)]
mod nested_move_path_tests_068 {
    const TYPES:&str="struct Leaf{value:i64} struct Mid{first:Leaf,second:Leaf} struct Outer{inner:Mid,spare:Leaf}";
    fn source(body:&str)->String {
        format!("{TYPES} fn main(){{let mut obj:Outer=Outer{{inner:Mid{{first:Leaf{{value:3}},second:Leaf{{value:7}}}},spare:Leaf{{value:9}}}};{body}}}")
    }
    #[test]fn nested_copy_leaf_preserves_aggregate(){
        let s=source("let a:i64=obj.inner.first.value;let b:i64=obj.inner.first.value;let q=qubit();rx(a,q);ry(b,q);");
        let got=crate::compile(&s).unwrap();
        assert_eq!(got.angles.as_slice(),&[3.0,3.0]);
    }
    #[test]fn nested_move_keeps_independent_sibling_and_parent_partial(){
        let good=source("let first:Leaf=obj.inner.first;let v:i64=obj.inner.second.value;let q=qubit();rx(v,q);ry(first.value,q);");
        assert_eq!(crate::compile(&good).unwrap().angles.as_slice(),&[7.0,3.0]);
        let bad=source("let first:Leaf=obj.inner.first;let whole:Outer=obj;");
        assert!(crate::compile(&bad).unwrap_err().message.contains("partially moved"));
    }
    #[test]fn nested_write_restores_full_aggregate(){
        let s=source("let first:Leaf=obj.inner.first;obj.inner.first=Leaf{value:11};let whole:Outer=obj;let q=qubit();rx(whole.inner.first.value,q);");
        assert_eq!(crate::compile(&s).unwrap().angles.as_slice(),&[11.0]);
    }
    #[test]fn nested_borrow_of_sibling_blocks_only_overlapping_moves(){
        let safe=source("let r=&obj.inner.second;let first:Leaf=obj.inner.first;let q=qubit();rx(r.value,q);ry(first.value,q);");
        assert_eq!(crate::compile(&safe).unwrap().angles.as_slice(),&[7.0,3.0]);
        let bad=source("let r=&obj.inner.second;let moved:Leaf=obj.inner.second;let q=qubit();rx(r.value,q);");
        assert!(crate::compile(&bad).unwrap_err().message.contains("borrow"));
    }
    #[test]fn nested_mut_reference_can_reinitialize_exact_leaf(){
        let s=source("let r=&mut obj.inner.second;*r=Leaf{value:13};let q=qubit();rx(obj.inner.first.value,q);");
        assert_eq!(crate::compile(&s).unwrap().angles.as_slice(),&[3.0]);
    }
    #[test]fn nested_parent_borrow_prevents_partial_move(){
        let bad=source("let r=&obj.inner;let moved:Leaf=obj.inner.first;let q=qubit();rx(r.second.value,q);");
        assert!(crate::compile(&bad).is_err());
    }
}

#[cfg(test)]
mod typed_mir_integration_tests_0611 {
    use super::*;
    #[test]fn mir_accepts_nll_end_of_borrow_before_write(){
        let source="fn main(){let mut x:i64=1;let r=&x;let y:i64=*r;x=3;}";
        assert!(compile(source).is_ok());
    }
    #[test]fn mir_rejects_write_in_untaken_branch_with_live_loan(){
        let source="fn main(){let mut x:i64=1;let r=&x;if true{let a:i64=*r;}else{x=3;}let b:i64=*r;}";
        let error=compile(source).err().expect("unselected branch must fail");
        assert!(error.message.contains("typed MIR borrow check"),"{}",error.message);
    }
}

#[cfg(test)]
mod rust_0618_generic_tests {
    use super::*;
    fn ok(src:&str)->crate::ir::Program {compile(src).unwrap()}
    fn no(src:&str)->String {compile(src).unwrap_err().message}

    #[test]
    fn independent_type_parameters_and_numeric_inference() {
        let src="fn choose<T,U>(left:T,right:U)->T{left} fn main(){let n:u64=17;let q=qubit();rx(choose(n,true),q);ry(choose(3,false),q);}";
        assert_eq!(ok(src).angles.as_slice(), &[17.0,3.0]);
    }

    #[test]
    fn repeated_generic_bindings_must_agree() {
        let bad="fn choose<T,U>(a:T,b:T,c:U)->T{a} fn main(){let x:u64=3;let y:i64=5;let q=qubit();rx(choose(x,y,true),q);}";
        assert!(no(bad).contains("generic type mismatch"));
    }

    #[test]
    fn builtin_copy_bound_is_not_implicitly_granted_to_structs() {
        let good="fn copied<T:Copy>(v:T)->T{v} fn main(){let q=qubit();rx(copied(5),q);}";
        assert_eq!(ok(good).angles.as_slice(), &[5.0]);
        let bad="struct Boxed{v:i64} fn copied<T:Copy>(v:T)->T{v} fn main(){let b:Boxed=Boxed{v:3};let c=copied(b);}";
        assert!(no(bad).contains("trait bound T: Copy is not satisfied"));
    }

    #[test]
    fn eq_and_partial_eq_bounds_accept_scalars_but_not_implicit_aggregate_impls() {
        let source="fn id<T:Eq>(value:T)->T{value} fn wrap<U:PartialEq>(value:U)->U{value} fn main(){let n:i64=3;static_assert_eq(id(n),3);let v:u64=12;static_assert_eq(wrap(v),12);let q=qubit();h(q);}";
        assert_eq!(ok(source).qubits, 1);
        let bad="struct NonEq{v:i64} fn id<T:Eq>(v:T)->T{v} fn main(){let a:NonEq=NonEq{v:1};let b=id(a);}";
        assert!(no(bad).contains("trait bound T: Eq is not satisfied"));
        let not_derived="enum Mode{A,B} fn id<T:Eq>(v:T)->T{v} fn main(){let a:Mode=Mode::B;let b=id(a);}";
        assert!(no(not_derived).contains("trait bound T: Eq is not satisfied"));
    }

    #[test]
    fn where_bounds_and_inline_bounds_can_be_combined() {
        let src="fn ident<T:Copy,U>(x:T,y:U)->T where T: PartialEq {x} fn main(){let q=qubit();ry(ident(9,true),q);}";
        assert_eq!(ok(src).angles.as_slice(), &[9.0]);
        assert!(no("fn ident<T>(x:T)->T where U: Copy {x} fn main(){}")
            .contains("where bound requires declared type parameter"));
    }

    #[test]
    fn unknown_traits_and_duplicate_type_parameters_fail_closed() {
        assert!(no("fn id<T:Clone>(v:T)->T{v} fn main(){}")
            .contains("unsupported trait bound 'Clone'"));
        assert!(no("fn id<T,T>(v:T)->T{v} fn main(){}")
            .contains("duplicate type parameter"));
        assert!(no("fn make<T>()->T{1} fn main(){let x=make();}")
            .contains("cannot infer generic type T"));
    }

    #[test]
    fn lifetime_elision_works_with_one_reference_but_rejects_ambiguity() {
        let src="fn identity(x:&i64)->&i64{x} fn main(){let n:i64=23;let r=identity(&n);let q=qubit();rx(*r,q);}";
        assert_eq!(ok(src).angles.as_slice(), &[23.0]);
        assert!(no("fn ambiguous(x:&i64,y:&i64)->&i64{x} fn main(){}")
            .contains("missing lifetime specifier"));
        assert!(no("fn without_input()->&i64{let x:i64=1;&x} fn main(){}")
            .contains("missing lifetime specifier"));
    }

    #[test]
    fn generic_references_preserve_lifetimes_and_do_not_copy_pointees() {
        let src="fn hold<'a,T,U>(x:&'a T,unused:U)->&'a T{x} fn main(){let n:i64=14;let r=hold(&n,true);let q=qubit();rz(*r,q);}";
        assert_eq!(ok(src).angles.as_slice(), &[14.0]);
        assert!(no("fn wrong<'a,'b,T>(x:&'a T,y:&'b T)->&'a T{y} fn main(){}")
            .contains("lifetime"));
    }

    #[test]
    fn unused_generic_reference_returns_check_both_syntaxes() {
        let tail="fn wrong<'a,'b,T>(x:&'a T,y:&'b T)->&'a T{y} fn main(){}";
        let explicit="fn wrong<'a,'b,T>(x:&'a T,y:&'b T)->&'a T{return y;} fn main(){}";
        let reborrow="fn wrong<'a,'b,T>(x:&'a T,y:&'b T)->&'a T{&*y} fn main(){}";
        for source in [tail,explicit,reborrow] {
            assert!(no(source).contains("lifetime"),"source accepted: {source}");
        }
    }

    #[test]
    fn bound_generic_reference_return_can_shorten_proven_lifetime() {
        let source="fn shorten<'a,'b,T>(x:&'b T)->&'a T where 'b:'a {x} fn main(){}";
        assert!(compile(source).is_ok());
        let bad="fn shorten<'a,'b,T>(x:&'b T)->&'a T where 'a:'b {x} fn main(){}";
        assert!(no(bad).contains("lifetime"));
    }

    #[test]
    fn unused_reference_return_without_input_must_have_lifetime() {
        let no_source="fn invalid()->&i64{let local:i64=7;&local} fn main(){}";
        assert!(no(no_source).contains("missing lifetime specifier"));
        let explicit_but_local="fn invalid<'a>()->&'a i64{let local:i64=7;&local} fn main(){}";
        assert!(no(explicit_but_local).contains("reference escapes"));
    }

    #[test]
    fn generic_void_function_is_routed_through_public_compiler() {
        let source="fn consume<T:Copy>(x:T){} fn main(){let flag=true;consume(flag);let q=qubit();h(q);}";
        assert!(enabled(source));
        assert_eq!(crate::compile(source).unwrap().qubits,1);
    }

    #[test]
    fn generic_host_wrapper_keeps_qasm_and_qcu_byte_identical() {
        let source="fn id<T:Copy>(v:T)->T{v} fn main(){let q=qubit();rx(id(7),q);ry(id(2),q);}";
        let baseline="fn main(){let q=qubit();rx(7,q);ry(2,q);}";
        let new=crate::compile(source).unwrap();
        let old=crate::compile(baseline).unwrap();
        assert_eq!(crate::sema::emit_qasm(&new),crate::sema::emit_qasm(&old));
        assert_eq!(crate::qcu::encode(&new).unwrap(),crate::qcu::encode(&old).unwrap());
    }
}

#[cfg(test)]
mod rust_0619_whole_body_tests {
    use super::*;
    fn reject(source:&str)->String {
        compile(source).expect_err("invalid function was accepted").message
    }
    #[test]
    fn unused_generic_double_move_fails_in_statements_and_tail() {
        for body in ["let first=value;let second=value;",
                     "let first=value;value",
                     "value;value"] {
            let source=format!("fn invalid<T>(value:T)->T{{{body}}} fn main(){{}}");
            assert!(reject(&source).contains("typed MIR borrow check"),"{source}");
        }
    }
    #[test]
    fn unused_generic_branch_move_requires_validity_on_both_paths() {
        let source="fn invalid<T>(value:T)->T{if false {let moved=value;}value} fn main(){}";
        assert!(reject(source).contains("typed MIR borrow check"));
    }
    #[test]
    fn copy_bounds_do_not_unnecessarily_forbid_reuse() {
        let source="fn valid<T:Copy>(value:T)->T{let first=value;value} fn main(){}";
        assert!(compile(source).is_ok());
    }
    #[test]
    fn reference_param_and_unrestricted_generic_return_are_checked() {
        let source="fn valid<'a,T>(value:&'a T)->&'a T{value} fn main(){}";
        assert!(compile(source).is_ok());
        let bad="fn invalid<'a,T>(value:&'a T)->&'a &T{&value} fn main(){}";
        assert!(reject(bad).contains("parameter binding"));
    }
    #[test]
    fn omitted_reference_return_and_unproved_conditional_are_rejected() {
        let missing="fn invalid<'a>(x:&'a i64)->&'a i64{} fn main(){}";
        assert!(reject(missing).contains("return expression"));
        let valid="fn valid<'a>(x:&'a i64)->&'a i64{if true{x}else{x}} fn main(){}";
        assert!(compile(valid).is_ok());
        let conditional="fn invalid<'a>(x:&'a i64)->&'a i64{if true{x}} fn main(){}";
        assert!(reject(conditional).contains("cannot prove lifetime"));
    }
    #[test]
    fn unused_reference_returns_require_exact_pointee_types() {
        let bad="fn invalid<'a,T,U>(value:&'a T)->&'a U{value} fn main(){}";
        assert!(reject(bad).contains("pointee type mismatch"));
        let good="fn valid<'a,T>(value:&'a T)->&'a T{&*value} fn main(){}";
        assert!(compile(good).is_ok());
    }
    #[test]
    fn lifetime_of_a_name_does_not_certify_composite_expression() {
        let bad="fn invalid<'a>(value:&'a i64)->&'a i64{value+1} fn main(){}";
        assert!(reject(bad).contains("composite returned reference"));
        let exclusive="fn invalid<'a>(value:&'a i64)->&'a mut i64{&mut *value} fn main(){}";
        assert!(reject(exclusive).contains("cannot mutably reborrow"));
    }
    #[test]
    fn unused_concrete_aggregate_cannot_move_twice() {
        let bad="struct Payload{n:i64} fn invalid(x:Payload){let a=x;let b=x;} fn main(){}";
        assert!(reject(bad).contains("typed MIR borrow check"));
        let good="struct Payload{n:i64} fn take(x:Payload)->i64{x.n} fn main(){}";
        assert!(compile(good).is_ok());
    }
    #[test]
    fn arbitrary_calls_with_affine_generic_effects_are_not_certified() {
        let source="fn invalid<T>(value:T){unknown_effect(value);} fn main(){}";
        assert!(reject(source).contains("incomplete typed MIR ownership coverage"));
    }
    #[test]
    fn generic_scalar_arithmetic_keeps_the_move_events() {
        let source="fn valid<T>(x:T,y:T)->T{x+y} fn main(){let q=qubit();rx(valid(2,3),q);}";
        assert!(compile(source).is_ok());
        let invalid="fn invalid<T>(x:T,y:T)->T{x+y;x} fn main(){}";
        assert!(reject(invalid).contains("typed MIR borrow check"));
    }
}

#[cfg(test)]
mod mir_0619_mutable_binding_tests {
    fn reject(src:&str)->String {
        crate::typed_frontend::compile(src).unwrap_err().message
    }
    #[test]fn unused_mutable_borrow_requires_mut_binding(){
        let src="fn invalid<T>(value:T){let reference=&mut value;} fn main(){}";
        assert!(reject(src).contains("cannot mutably borrow immutable binding"));
        let src="fn invalid(){let value:i64=4;let reference=&mut value;} fn main(){}";
        assert!(reject(src).contains("cannot mutably borrow immutable binding"));
    }
    #[test]fn borrow_of_explicitly_mut_local_is_permitted(){
        let src="fn valid<T>(value:T){let mut local=value;let reference=&mut local;} fn main(){}";
        assert!(crate::typed_frontend::compile(src).is_ok());
    }
}

#[cfg(test)]
mod mir_branch_integration_0620_tests {
    fn reject(source:&str)->String {
        crate::typed_frontend::compile(source).unwrap_err().message
    }
    #[test]
    fn uncalled_generic_move_after_else_if_is_checked_on_every_arm() {
        let invalid="fn invalid<T>(value:T){if true {let first=value;} else if false {} let second=value;} fn main(){}";
        assert!(reject(invalid).contains("typed MIR borrow check"));
    }
    #[test]
    fn uncalled_generic_copy_bound_still_allows_branches() {
        let valid="fn valid<T:Copy>(value:T){if true {let first=value;} else if false {} let second=value;} fn main(){}";
        assert!(crate::typed_frontend::compile(valid).is_ok());
    }
}

#[cfg(test)]
mod rust_0623_returned_reference_calls {
    use super::*;
    #[test]
    fn unused_identity_call_can_propagate_reference_origin(){
        let source="fn identity<'a>(v:&'a i64)->&'a i64{v} fn wrapper<'a>(x:&'a i64)->&'a i64{identity(x)} fn main(){}";
        assert!(compile(source).is_ok());
    }
    #[test]
    fn proven_multi_argument_call_can_return_a_verified_input_origin(){
        let source="fn pick<'a>(x:&'a i64,y:&'a i64)->&'a i64{x} \
            fn wrapper<'a>(v:&'a i64)->&'a i64{pick(v,v)} \
            fn main(){let a:i64=19;let r=wrapper(&a);let q=qubit();rx(*r,q);}";
        let program=compile(source).expect("proven reference origin should be accepted");
        assert_eq!(program.qubits,1);
        assert_eq!(program.angles.as_slice(),&[19.0]);
    }
    #[test]
    fn multi_argument_call_still_rejects_shorter_lived_return_origin(){
        let source="fn pick<'a,'b>(x:&'a i64,y:&'b i64)->&'a i64{x} \
            fn wrapper<'a,'b>(x:&'a i64,y:&'b i64)->&'a i64{pick(y,x)} fn main(){}";
        assert!(compile(source).is_err(),
            "outlives constraints must follow the actual returned parameter");
    }
    #[test]
    fn multi_argument_call_can_follow_verified_shared_alias(){
        let source="fn opaque<'a>(x:&'a i64,y:&'a i64)->&'a i64{let alias=x;alias} \
            fn wrapper<'a>(v:&'a i64)->&'a i64{opaque(v,v)} \
            fn main(){let n:i64=23;let r=wrapper(&n);let q=qubit();rx(*r,q);}";
        let program=compile(source).expect("a verified shared alias must preserve provenance");
        assert_eq!(program.angles.as_slice(),&[23.0]);
    }
    #[test]
    fn identity_helper_must_be_structurally_proven(){
        let source="fn identity<'a>(v:&'a i64)->&'a i64{let local:i64=5;&local} fn wrapper<'a>(v:&'a i64)->&'a i64{identity(v)} fn main(){}";
        assert!(compile(source).is_err());
    }
}

#[cfg(test)]
mod region_call_results_0627_tests {
    use super::*;
    fn ok(src:&str)->crate::ir::Program { compile(src).expect("valid region call") }
    fn bad(src:&str)->String {compile(src).expect_err("invalid lifetime accepted").message}

    #[test]
    fn alternative_reference_result_from_called_function_selects_first_owner(){
        let p=ok("fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} fn main(){let a:i64=3;let b:i64=8;let r=choose(true,&a,&b);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles.as_slice(),&[3.0]);
    }
    #[test]
    fn alternative_reference_result_selects_second_owner(){
        let p=ok("fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} fn main(){let a:i64=3;let b:i64=8;let r=choose(false,&a,&b);let q=qubit();rx(*r,q);}");
        assert_eq!(p.angles.as_slice(),&[8.0]);
    }
    #[test]
    fn alternative_reference_calls_preserve_existing_quantum_output(){
        let via=ok("fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} fn main(){let a:i64=3;let b:i64=8;let r=choose(false,&a,&b);let q=qubit();rx(*r,q);}");
        let direct=ok("fn main(){let q=qubit();rx(8,q);}");
        assert_eq!(crate::sema::emit_qasm(&via),crate::sema::emit_qasm(&direct));
    }
    #[test]
    fn uncalled_alternative_return_checks_every_lifetime(){
        let s="fn choose<'a,'b>(c:bool,x:&'a i64,y:&'b i64)->&'a i64{if c{x}else{y}} fn main(){}";
        assert!(bad(s).contains("lifetime"));
    }
    #[test]
    fn explicit_outlives_allows_two_reference_sources(){
        ok("fn choose<'a,'b>(c:bool,x:&'a i64,y:&'b i64)->&'a i64 where 'b:'a {if c{x}else{y}} fn main(){let a:i64=3;let b:i64=8;let r=choose(false,&a,&b);let q=qubit();rx(*r,q);}");
    }
    #[test]
    fn no_else_does_not_prove_return_reference(){
        assert!(bad("fn choose<'a>(c:bool,x:&'a i64)->&'a i64{if c{x}} fn main(){}")
            .contains("cannot prove lifetime"));
    }
    #[test]
    fn local_reference_in_inactive_arm_cannot_escape(){
        let s="fn invalid<'a>(c:bool,x:&'a i64)->&'a i64{let n:i64=2;if c{x}else{&n}} fn main(){}";
        assert!(bad(s).contains("local"));
    }
    #[test]
    fn mutable_alternative_results_cannot_gain_mutability_from_shared_arm(){
        let s="fn invalid<'a>(c:bool,x:&'a mut i64,y:&'a i64)->&'a mut i64{if c{x}else{y}} fn main(){}";
        assert!(bad(s).contains("mutable reference"));
    }
    #[test]
    fn mutable_parameter_requires_explicit_shared_return_reborrow(){
        let unsupported="fn invalid<'a>(x:&'a mut i64)->&'a i64{x} fn main(){}";
        assert!(bad(unsupported).contains("explicit reborrow"));
        let supported="fn valid<'a>(x:&'a mut i64)->&'a i64{&*x} fn main(){}";
        assert!(compile(supported).is_ok());
    }
    #[test]
    fn shared_reborrow_cannot_be_promoted_to_mutable_return(){
        let s="fn invalid<'a>(x:&'a mut i64)->&'a mut i64{&*x} fn main(){}";
        assert!(bad(s).contains("shared reborrow"));
    }
    #[test]
    fn returned_reference_across_multiple_mutable_reborrow_calls(){
        let s="fn id<'a>(x:&'a mut i64)->&'a mut i64{x} fn step<'a>(x:&'a mut i64)->&'a mut i64{id(x)} fn main(){let mut n:i64=4;let r=&mut n;let v=step(r);*v=6;let q=qubit();rx(*v,q);}";
        assert_eq!(ok(s).angles.as_slice(),&[6.0]);
    }
}

#[cfg(test)]
mod region_match_and_call_chain_0628_tests {
    use super::*;
    fn good(source:&str)->crate::ir::Program {
        compile(source).expect("valid region match/call chain rejected")
    }
    fn bad(source:&str)->String {
        compile(source).expect_err("unsafe reference provenance accepted").message
    }
    #[test]
    fn boolean_match_selects_both_alternative_reference_owners() {
        let prefix="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{match c{true=>{x},false=>{y}}} ";
        let left=good(&format!("{prefix} fn main(){{let a:i64=7;let b:i64=9;let r=choose(true,&a,&b);let q=qubit();rx(*r,q);}}"));
        let right=good(&format!("{prefix} fn main(){{let a:i64=7;let b:i64=9;let r=choose(false,&a,&b);let q=qubit();rx(*r,q);}}"));
        assert_eq!(left.angles,&[7.0]);
        assert_eq!(right.angles,&[9.0]);
    }
    #[test]
    fn match_can_use_exhaustive_wildcard() {
        let src="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{match c{true=>{x},_=>{y}}} fn main(){let a:i64=3;let b:i64=11;let r=choose(false,&a,&b);let q=qubit();ry(*r,q);}";
        assert_eq!(good(src).angles,&[11.0]);
    }
    #[test]
    fn match_rejects_missing_arm_even_when_not_called() {
        let src="fn choose<'a>(c:bool,x:&'a i64)->&'a i64{match c{true=>{x}}} fn main(){}";
        assert!(bad(src).contains("cannot prove lifetime"));
    }
    #[test]
    fn match_rejects_duplicate_arms() {
        let src="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{match c{true=>{x},true=>{y},false=>{y}}} fn main(){}";
        assert!(bad(src).contains("cannot prove lifetime"));
    }
    #[test]
    fn match_checks_inactive_local_reference_branch() {
        let src="fn invalid<'a>(c:bool,x:&'a i64)->&'a i64{let n:i64=5;match c{true=>{x},false=>{&n}}} fn main(){}";
        assert!(bad(src).contains("local"));
    }
    #[test]
    fn match_requires_outlives_on_every_alternative() {
        let src="fn wrong<'a,'b>(c:bool,x:&'a i64,y:&'b i64)->&'a i64{match c{true=>{x},false=>{y}}} fn main(){}";
        assert!(bad(src).contains("lifetime"));
        let valid="fn choose<'a,'b>(c:bool,x:&'a i64,y:&'b i64)->&'a i64 where 'b:'a {match c{true=>{x},false=>{y}}} fn main(){let a:i64=4;let b:i64=6;let r=choose(false,&a,&b);let q=qubit();rx(*r,q);}";
        assert_eq!(good(valid).angles,&[6.0]);
    }
    #[test]
    fn match_cannot_upgrade_shared_reference_to_mutable() {
        let src="fn wrong<'a>(c:bool,x:&'a mut i64,y:&'a i64)->&'a mut i64{match c{true=>{x},false=>{y}}} fn main(){}";
        assert!(bad(src).contains("mutable reference"));
    }
    #[test]
    fn three_hop_reference_return_uses_actual_lease() {
        let src="fn inner<'a>(x:&'a i64)->&'a i64{x} fn middle<'a>(x:&'a i64)->&'a i64{inner(x)} fn outer<'a>(x:&'a i64)->&'a i64{middle(x)} fn main(){let n:i64=14;let r=outer(&n);let q=qubit();rx(*r,q);}";
        assert_eq!(good(src).angles,&[14.0]);
    }
    #[test]
    fn three_hop_mutable_reborrow_preserves_exclusive_access() {
        let src="fn inner<'a>(x:&'a mut i64)->&'a mut i64{x} fn middle<'a>(x:&'a mut i64)->&'a mut i64{inner(x)} fn outer<'a>(x:&'a mut i64)->&'a mut i64{middle(x)} fn main(){let mut n:i64=2;let r=outer(&mut n);*r=16;let q=qubit();rx(*r,q);}";
        assert_eq!(good(src).angles,&[16.0]);
    }
    #[test]
    fn reborrow_parent_chain_survives_multiple_function_boundaries() {
        let src="fn first<'a>(x:&'a mut i64)->&'a mut i64{&mut *x} fn second<'a>(x:&'a mut i64)->&'a mut i64{first(x)} fn main(){let mut n:i64=2;let r=second(&mut n);*r=21;let q=qubit();ry(*r,q);}";
        assert_eq!(good(src).angles,&[21.0]);
    }
    #[test]
    fn shared_reborrow_can_cross_verified_reference_wrappers() {
        let src="fn first<'a>(x:&'a i64)->&'a i64{&*x} fn second<'a>(x:&'a i64)->&'a i64{first(x)} fn main(){let n:i64=19;let r=second(&n);let q=qubit();rx(*r,q);}";
        assert_eq!(good(src).angles,&[19.0]);
    }
    #[test]
    fn mutable_reborrow_can_cross_three_verified_reference_wrappers() {
        let src="fn first<'a>(x:&'a mut i64)->&'a mut i64{&mut *x} fn second<'a>(x:&'a mut i64)->&'a mut i64{first(x)} fn third<'a>(x:&'a mut i64)->&'a mut i64{second(x)} fn main(){let mut n:i64=3;let r=third(&mut n);*r=23;let q=qubit();rx(*r,q);}";
        assert_eq!(good(src).angles,&[23.0]);
    }
    #[test]
    fn shared_reborrow_cannot_claim_mutable_result_in_wrapper() {
        let src="fn first<'a>(x:&'a mut i64)->&'a mut i64{&*x} fn second<'a>(x:&'a mut i64)->&'a mut i64{first(x)} fn main(){}";
        let message=bad(src);
        assert!(message.contains("shared reborrow") || message.contains("mutable reference"),"{message}");
    }
    #[test]
    fn shared_reference_cannot_be_upgraded_by_nested_wrapper() {
        let src="fn first<'a>(x:&'a i64)->&'a mut i64{&mut *x} fn second<'a>(x:&'a i64)->&'a mut i64{first(x)} fn main(){}";
        let message=bad(src);
        assert!(message.contains("mutably reborrow") || message.contains("mutable reference"),"{message}");
    }
    #[test]
    fn mutable_parent_cannot_be_used_while_nested_child_is_live() {
        let src="fn main(){let mut n:i64=2;let r=&mut n;let child=&mut *r;*r=9;let q=qubit();rx(*child,q);}";
        let error=bad(src);
        assert!(error.contains("reborrow") || error.contains("suspended") || error.contains("borrow"),"{error}");
    }
    #[test]
    fn deep_wrapper_without_origin_is_rejected() {
        let src="fn unsafe_inner<'a>(x:&'a i64)->&'a i64{let y:i64=2;&y} fn middle<'a>(x:&'a i64)->&'a i64{unsafe_inner(x)} fn outer<'a>(x:&'a i64)->&'a i64{middle(x)} fn main(){}";
        let error=bad(src);
        assert!(error.contains("local") || error.contains("lifetime"),"{error}");
    }
    #[test]
    fn recursively_defined_wrapper_is_not_a_proven_identity() {
        let src="fn recur<'a>(x:&'a i64)->&'a i64{recur(x)} fn main(){}";
        assert!(bad(src).contains("cannot prove lifetime"));
    }
}

#[cfg(test)]
mod interprocedural_region_0629_tests {
    use super::*;
    fn valid(source:&str)->crate::ir::Program {
        compile(source).expect("safe multi-source region call was rejected")
    }
    fn rejected(source:&str)->String {
        compile(source).expect_err("unproven returned reference was accepted").message
    }
    #[test]
    fn if_result_flows_through_two_multi_argument_functions() {
        let code="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} \
            fn middle<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{choose(c,x,y)} \
            fn outer<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{middle(c,x,y)} \
            fn main(){let a:i64=8;let b:i64=17;let r=outer(false,&a,&b);let q=qubit();rx(*r,q);}";
        assert_eq!(valid(code).angles.as_slice(),&[17.0]);
    }
    #[test]
    fn match_result_flows_through_multi_argument_function() {
        let code="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{match c{true=>{x},false=>{y}}} \
            fn outer<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{choose(c,x,y)} \
            fn main(){let a:i64=4;let b:i64=13;let r=outer(true,&a,&b);let q=qubit();ry(*r,q);}";
        assert_eq!(valid(code).angles.as_slice(),&[4.0]);
    }
    #[test]
    fn missing_caller_outlives_rejects_uninstantiated_wrapper() {
        let code="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} \
            fn wrong<'a,'b>(c:bool,x:&'a i64,y:&'b i64)->&'a i64{choose(c,x,y)} fn main(){}";
        assert!(!rejected(code).is_empty());
    }
    #[test]
    fn explicit_outlives_contract_can_be_forwarded() {
        let code="fn choose<'a,'b>(c:bool,x:&'a i64,y:&'b i64)->&'a i64 where 'b:'a {if c{x}else{y}} \
            fn outer<'a,'b>(c:bool,x:&'a i64,y:&'b i64)->&'a i64 where 'b:'a {choose(c,x,y)} \
            fn main(){let a:i64=3;let b:i64=12;let r=outer(false,&a,&b);let q=qubit();rx(*r,q);}";
        assert_eq!(valid(code).angles.as_slice(),&[12.0]);
    }
    #[test]
    fn mutable_result_through_multi_source_call_keeps_exclusivity() {
        let code="fn choose<'a>(c:bool,x:&'a mut i64,y:&'a mut i64)->&'a mut i64{if c{x}else{y}} \
            fn outer<'a>(c:bool,x:&'a mut i64,y:&'a mut i64)->&'a mut i64{choose(c,x,y)} \
            fn main(){let mut a:i64=4;let mut b:i64=7;let r=outer(true,&mut a,&mut b);*r=22;let q=qubit();rx(*r,q);}";
        assert_eq!(valid(code).angles.as_slice(),&[22.0]);
    }
    #[test]
    fn pure_multi_source_call_cannot_upgrade_shared_to_mutable() {
        let code="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} \
            fn wrong<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a mut i64{choose(c,x,y)} fn main(){}";
        assert!(!rejected(code).is_empty());
    }
    #[test]
    fn impure_call_argument_does_not_gain_provenance_from_its_name() {
        let code="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} \
            fn wrong<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{choose(c,x,*y)} fn main(){}";
        assert!(!rejected(code).is_empty());
    }
    #[test]
    fn local_reference_argument_cannot_be_silently_treated_as_formal() {
        let code="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} \
            fn wrong<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{let local:i64=3;let z=&local;choose(c,x,z)} fn main(){}";
        assert!(!rejected(code).is_empty());
    }
    #[test]
    fn recursive_multi_reference_wrapper_has_no_trusted_summary() {
        let code="fn first<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{second(c,x,y)} \
            fn second<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{first(c,x,y)} fn main(){}";
        assert!(!rejected(code).is_empty());
    }
    #[test]
    fn quantum_values_do_not_gain_copy_through_reference_summary() {
        let code="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} \
            fn outer<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{choose(c,x,y)} \
            fn main(){let a:i64=1;let b:i64=2;let r=outer(true,&a,&b);let q=qubit();rx(*r,q);ry(*r,q);}";
        let program=valid(code);
        assert_eq!(program.qubits,1);
        assert_eq!(program.instructions.len(),2);
    }
    #[test]
    fn return_through_mutable_reborrow_wrapper_still_checks_parent() {
        let code="fn child<'a>(x:&'a mut i64)->&'a mut i64{&mut *x} \
            fn choose<'a>(c:bool,x:&'a mut i64,y:&'a mut i64)->&'a mut i64{if c{x}else{y}} \
            fn outer<'a>(c:bool,x:&'a mut i64,y:&'a mut i64)->&'a mut i64{choose(c,x,y)} \
            fn main(){let mut a:i64=1;let mut b:i64=2;let ra=child(&mut a);let r=outer(false,ra,&mut b);*r=31;let q=qubit();rx(*r,q);}";
        assert_eq!(valid(code).angles.as_slice(),&[31.0]);
    }
}

#[cfg(test)]
mod shared_alias_regions_0630_tests {
    use super::*;
    fn good(source:&str)->crate::ir::Program {
        compile(source).expect("verified shared alias chain should be safe")
    }
    fn bad(source:&str) {
        assert!(compile(source).is_err(),"unproven alias origin was accepted");
    }
    #[test]
    fn multi_hop_local_shared_alias_survives_two_calls(){
        let src="fn alias<'a>(x:&'a i64)->&'a i64{let a=x;let b=a;let c=b;c} \
            fn outer<'a>(x:&'a i64)->&'a i64{alias(x)} \
            fn main(){let v:i64=31;let r=outer(&v);let q=qubit();rx(*r,q);}";
        assert_eq!(good(src).angles.as_slice(),&[31.0]);
    }
    #[test]
    fn distinct_shared_alias_sources_flow_through_if(){
        let src="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{let left=x;let right=y;if c{left}else{right}} \
            fn outer<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{choose(c,x,y)} \
            fn main(){let a:i64=4;let b:i64=8;let r=outer(false,&a,&b);let q=qubit();ry(*r,q);}";
        assert_eq!(good(src).angles.as_slice(),&[8.0]);
    }
    #[test]
    fn distinct_shared_alias_sources_flow_through_match(){
        let src="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{let aa=x;let bb=y;match c{true=>{aa},false=>{bb}}} \
            fn outer<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{choose(c,x,y)} \
            fn main(){let a:i64=4;let b:i64=12;let r=outer(true,&a,&b);let q=qubit();rx(*r,q);}";
        assert_eq!(good(src).angles.as_slice(),&[4.0]);
    }
    #[test]
    fn alias_cannot_forge_outlives_from_shorter_parameter(){
        let src="fn pick<'a,'b>(x:&'a i64,y:&'b i64)->&'a i64{let alias=y;alias} \
            fn wrapper<'a,'b>(x:&'a i64,y:&'b i64)->&'a i64{pick(x,y)} fn main(){}";
        bad(src);
    }
    #[test]
    fn alias_of_local_owner_cannot_escape(){
        let src="fn escape<'a>(x:&'a i64)->&'a i64{let n:i64=7;let alias=&n;alias} \
            fn wrapper<'a>(x:&'a i64)->&'a i64{escape(x)} fn main(){}";
        bad(src);
    }
    #[test]
    fn mutable_alias_requires_linear_move_not_implicit_copy(){
        let src="fn alias<'a>(x:&'a mut i64)->&'a mut i64{let y=x;y} \
            fn wrapper<'a>(x:&'a mut i64)->&'a mut i64{alias(x)} \
            fn main(){let mut n:i64=5;let r=wrapper(&mut n);*r=9;let q=qubit();rx(*r,q);}";
        assert_eq!(good(src).angles.as_slice(), &[9.0]);
        bad("fn alias<'a>(x:&'a mut i64)->&'a mut i64{let y=x;x} fn main(){}");
    }
    #[test]
    fn alias_mutation_or_reassignment_has_no_proven_summary(){
        let src="fn choose<'a>(x:&'a i64,y:&'a i64)->&'a i64{let mut z=x;z=y;z} \
            fn wrapper<'a>(x:&'a i64,y:&'a i64)->&'a i64{choose(x,y)} fn main(){}";
        bad(src);
    }
    #[test]
    fn illegal_implicit_mutability_upgrade_remains_rejected(){
        let src="fn alias<'a>(x:&'a i64)->&'a mut i64{let y=x;y} fn main(){}";
        bad(src);
    }
}

#[cfg(test)]
mod non_reference_call_arguments_0630_fix1_tests {
    use super::*;
    #[test]
    fn bool_parameter_in_three_step_reference_call_keeps_provenance(){
        let source="fn choose<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{if c{x}else{y}} \
            fn middle<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{choose(c,x,y)} \
            fn outer<'a>(c:bool,x:&'a i64,y:&'a i64)->&'a i64{middle(c,x,y)} \
            fn main(){let a:i64=2;let b:i64=29;let r=outer(false,&a,&b);let q=qubit();rx(*r,q);}";
        assert_eq!(compile(source).expect("reference source must be preserved")
            .angles.as_slice(),&[29.0]);
    }
    #[test]
    fn integer_parameter_can_be_forwarded_while_reference_source_is_checked(){
        let source="fn source<'a>(count:i64,x:&'a i64)->&'a i64{x} \
            fn wrap<'a>(count:i64,x:&'a i64)->&'a i64{source(count,x)} \
            fn main(){let n:i64=9;let r=wrap(3,&n);let q=qubit();ry(*r,q);}";
        assert_eq!(compile(source).expect("non-reference argument is not a loan")
            .angles.as_slice(),&[9.0]);
    }
    #[test]
    fn wrong_non_reference_argument_type_cannot_pass_call_proof(){
        let source="fn choose<'a>(c:bool,x:&'a i64)->&'a i64{x} \
            fn invalid<'a>(c:i64,x:&'a i64)->&'a i64{choose(c,x)} fn main(){}";
        assert!(compile(source).is_err(),"call argument type mismatch was accepted");
    }
}

#[cfg(test)]
mod mutable_alias_regions_0631_tests {
    use super::*;
    fn accept(src:&str)->crate::ir::Program {
        compile(src).expect("valid linear mutable alias chain was rejected")
    }
    fn reject(src:&str) {
        assert!(compile(src).is_err(),"invalid mutable alias was certified");
    }
    #[test]
    fn move_only_mutable_alias_can_return_across_two_calls() {
        let src="fn first<'a>(x:&'a mut i64)->&'a mut i64{let a=x;let b=a;b} \
            fn second<'a>(x:&'a mut i64)->&'a mut i64{first(x)} \
            fn main(){let mut n:i64=5;let r=second(&mut n);*r=28;let q=qubit();rx(*r,q);}";
        assert_eq!(accept(src).angles.as_slice(), &[28.0]);
    }
    #[test]
    fn mutable_alias_of_each_if_source_has_distinct_owner() {
        let src="fn pick<'a>(c:bool,x:&'a mut i64,y:&'a mut i64)->&'a mut i64{let a=x;let b=y;if c{a}else{b}} \
            fn main(){let mut x:i64=4;let mut y:i64=8;let r=pick(false,&mut x,&mut y);*r=19;let q=qubit();rx(*r,q);}";
        assert_eq!(accept(src).angles.as_slice(), &[19.0]);
    }
    #[test]
    fn mutable_alias_of_each_match_source_has_distinct_owner() {
        let src="fn pick<'a>(c:bool,x:&'a mut i64,y:&'a mut i64)->&'a mut i64{let a=x;let b=y;match c{true=>{a},false=>{b}}} \
            fn main(){let mut x:i64=4;let mut y:i64=8;let r=pick(true,&mut x,&mut y);*r=19;let q=qubit();rx(*r,q);}";
        assert_eq!(accept(src).angles.as_slice(), &[19.0]);
    }
    #[test]
    fn mutable_alias_reborrow_keeps_lease_parent() {
        let src="fn child<'a>(x:&'a mut i64)->&'a mut i64{let a=x;&mut *a} \
            fn main(){let mut n:i64=5;let r=child(&mut n);*r=37;let q=qubit();rx(*r,q);}";
        assert_eq!(accept(src).angles.as_slice(), &[37.0]);
    }
    #[test]
    fn mutable_alias_to_shared_reborrow_has_no_mutability_upgrade() {
        let src="fn share<'a>(x:&'a mut i64)->&'a i64{let a=x;&*a} \
            fn main(){let mut n:i64=12;let r=share(&mut n);let q=qubit();rx(*r,q);}";
        assert_eq!(accept(src).angles.as_slice(), &[12.0]);
    }
    #[test]
    fn moved_mutable_parameter_cannot_be_returned_from_unused_helper() {
        reject("fn bad<'a>(x:&'a mut i64)->&'a mut i64{let alias=x;x} fn main(){}");
    }
    #[test]
    fn moved_mutable_alias_cannot_be_returned_from_unused_helper() {
        reject("fn bad<'a>(x:&'a mut i64)->&'a mut i64{let a=x;let b=a;a} fn main(){}");
    }
    #[test]
    fn second_move_of_same_mutable_parameter_is_rejected() {
        reject("fn bad<'a>(x:&'a mut i64)->&'a mut i64{let a=x;let b=x;b} fn main(){}");
    }
    #[test]
    fn mutable_alias_cannot_forge_outlives() {
        reject("fn bad<'a,'b>(x:&'a mut i64,y:&'b mut i64)->&'a mut i64{let alias=y;alias} fn main(){}");
    }
    #[test]
    fn two_simultaneous_exclusive_call_arguments_are_rejected() {
        reject("fn first<'a>(x:&'a mut i64,y:&'a mut i64)->&'a mut i64{x} \
            fn bad<'a>(x:&'a mut i64)->&'a mut i64{let alias=x;first(alias,alias)} fn main(){}");
    }
    #[test]
    fn moved_alias_cannot_reborrow_old_parameter() {
        reject("fn bad<'a>(x:&'a mut i64)->&'a mut i64{let alias=x;&mut *x} fn main(){}");
    }
    #[test]
    fn shared_reference_cannot_be_upgraded_through_mut_alias() {
        reject("fn bad<'a>(x:&'a i64)->&'a mut i64{let alias=x;&mut *alias} fn main(){}");
    }
    #[test]
    fn explicit_return_of_moved_alias_is_certified() {
        let src="fn hop<'a>(x:&'a mut i64)->&'a mut i64{let a=x;return a;} \
            fn main(){let mut n:i64=3;let r=hop(&mut n);*r=14;let q=qubit();rx(*r,q);}";
        assert_eq!(accept(src).angles.as_slice(), &[14.0]);
    }
    #[test]
    fn actual_move_path_rejects_use_of_original_alias() {
        reject("fn main(){let mut n:i64=2;let r=&mut n;let alias=r;*r=9;}");
    }
    #[test]
    fn active_child_loan_suspends_mutable_alias() {
        reject("fn main(){let mut n:i64=2;let r=&mut n;let alias=r;let child=&mut *alias;*alias=9;*child=11;}");
    }
    #[test]
    fn unused_child_loan_ends_before_parent_access() {
        let src="fn main(){let mut n:i64=2;let r=&mut n;let alias=r;let child=&mut *alias;*alias=9;let q=qubit();rx(*alias,q);}";
        assert_eq!(accept(src).angles.as_slice(), &[9.0]);
    }
    #[test]
    fn nested_exclusive_reborrow_keeps_its_parent_suspended() {
        reject("fn main(){let mut n:i64=2;let parent=&mut n;let child=&mut *parent;let grandchild=&mut *child;*child=9;*grandchild=11;}");
    }
    #[test]
    fn nested_exclusive_reborrow_suspends_the_root_reference() {
        reject("fn main(){let mut n:i64=2;let parent=&mut n;let child=&mut *parent;let grandchild=&mut *child;*parent=9;*grandchild=11;}");
    }
    #[test]
    fn mutable_alias_does_not_copy_qubit_resources() {
        let src="fn hop<'a>(x:&'a mut i64)->&'a mut i64{let a=x;a} \
            fn main(){let mut n:i64=3;let r=hop(&mut n);let q=qubit();rx(*r,q);ry(*r,q);}";
        let p=accept(src);
        assert_eq!(p.qubits,1);
        assert_eq!(p.instructions.len(),2);
    }
}

#[cfg(test)]
mod mutable_rebinding_execution_0632_tests {
    use super::*;

    #[test]
    fn plain_mutable_reference_rebinding_changes_owner() {
        let program=compile("fn main(){let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;r=&mut b;*r=11;let q=qubit();rx(*r,q);}")
            .expect("safe rebind must be accepted");
        assert_eq!(program.angles.as_slice(),&[11.0]);
    }
    #[test]
    fn moved_reference_alias_after_rebinding_is_still_linear() {
        let program=compile("fn main(){let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;r=&mut b;let next=r;*next=13;let q=qubit();rx(*next,q);}")
            .expect("moving a reassigned &mut must preserve its lease");
        assert_eq!(program.angles.as_slice(),&[13.0]);
    }
    #[test]
    fn active_child_prevents_replacing_its_mutable_parent() {
        let src="fn main(){let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;let child=&mut *r;r=&mut b;let q=qubit();rx(*child,q);}";
        assert!(compile(src).is_err(),"a parent lease cannot be rebound while a child is live");
    }
    #[test]
    fn dead_child_may_expire_before_parent_rebinding() {
        let src="fn main(){let mut a:i64=1;let mut b:i64=2;let mut r=&mut a;let child=&mut *r;*child=7;r=&mut b;*r=15;let q=qubit();rx(*r,q);}";
        let program=compile(src).expect("NLL must end a child after its last use");
        assert_eq!(program.angles.as_slice(),&[15.0]);
    }
    #[test]
    fn mutable_reference_reassignment_must_preserve_pointee_type() {
        let src="fn main(){let mut a:i64=1;let mut b:u64=2;let mut r=&mut a;r=&mut b;}";
        assert!(compile(src).is_err(),"cannot rebind &mut i64 to &mut u64");
    }
}

#[cfg(test)]
mod bool_match_mutable_phi_frontend_0634_tests {
    use super::*;
    #[test]
    fn bool_match_executes_selected_arm_with_mutable_binding() {
        let src="fn main(){let mut a:i64=1;let mut b:i64=2;\
            let mut r=&mut a;match false{true=>{r=&mut a;},false=>{r=&mut b;}}\
            *r=7;let q=qubit();rz(*r,q);}";
        let actual=compile(src).expect("exhaustive bool match should compile");
        let expected=crate::compile("fn main(){let q=qubit();rz(7,q);}").unwrap();
        assert_eq!(crate::sema::emit_qasm(&actual),crate::sema::emit_qasm(&expected));
    }
    #[test]
    fn bool_match_rejects_missing_or_duplicate_arms() {
        let missing="fn main(){let c:bool=true;match c{true=>{}}}";
        let duplicate="fn main(){match true{true=>{},true=>{},false=>{}}}";
        assert!(compile(missing).is_err());
        assert!(compile(duplicate).is_err());
    }
}

#[cfg(test)]
mod enum_tuple_payload_0639_tests {
    use super::*;

    #[test]
    fn typed_tuple_variant_binds_exact_scalar_fields() {
        let code="enum Pulse{Idle,Angle(i64),Active(i64,bool)} fn main(){\
            let p:Pulse=Pulse::Active(17,true);\
            match p{Pulse::Idle=>{},Pulse::Angle(v)=>{},\
                Pulse::Active(v,enabled)=>{if enabled {let q=qubit();rx(v,q);}}}}";
        let result=compile(code).expect("typed enum payload match must compile");
        assert_eq!(result.angles,&[17.0]);
    }
    #[test]
    fn unit_and_tuple_variants_coexist() {
        let code="enum Event{Start,Value(i64)} fn main(){\
            let e:Event=Event::Start;match e{Event::Start=>{let q=qubit();h(q);},\
            Event::Value(v)=>{}}}";
        assert_eq!(compile(code).expect("unit enum regression").instructions.len(),1);
    }
    #[test]
    fn enum_payload_owner_remains_affine() {
        let src="enum E{V(i64)} fn main(){let x:E=E::V(3);\
            match x{E::V(v)=>{}}match x{E::V(v)=>{}}}";
        assert!(compile(src).is_err(),"enum value must not be implicitly Copy");
    }
    #[test]
    fn variant_payload_type_and_arity_are_checked() {
        for src in [
            "enum E{V(i64,bool)} fn main(){let e:E=E::V(1);}",
            "enum E{V(i64)} fn main(){let e:E=E::V(true);}",
            "enum E{V(i64)} fn main(){let e:E=E::V(1,2);}",
            "enum E{V} fn main(){let e:E=E::V(1);}",
            "enum E{V(i64)} fn main(){let e:E=E::V;}",
        ] {
            assert!(compile(src).is_err(),"invalid variant construction accepted: {src}");
        }
    }
    #[test]
    fn tuple_patterns_check_arity_and_duplicate_bindings() {
        for pattern in ["E::V(x)","E::V(x,x)","E::V(x,y,z)","E::V"] {
            let src=format!("enum E{{V(i64,bool)}} fn main(){{let e:E=E::V(1,true);match e{{{pattern}=>{{}}}}}}");
            assert!(compile(&src).is_err(),"invalid tuple pattern accepted: {pattern}");
        }
    }
    #[test]
    fn typed_payload_match_must_be_exhaustive() {
        let src="enum E{A(i64),B(bool)} fn main(){\
            let x:E=E::A(3);match x{E::A(v)=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn scalar_wildcard_and_pattern_wildcard_are_valid() {
        let src="enum E{A(i64,bool),B} fn main(){let x:E=E::A(8,false);\
            match x{E::A(v,_)=>{let q=qubit();rx(v,q);},_=>{}}}";
        assert_eq!(compile(src).unwrap().angles,&[8.0]);
    }
    #[test]
    fn reference_and_untyped_fields_are_not_silently_certified() {
        for src in [
            "enum E{V(&i64)} fn main(){}",
            "enum E{V(&mut i64)} fn main(){}",
            "struct S{r:&i64} enum E{V(S)} fn main(){}",
            "struct S{r:&mut i64} enum E{V(S)} fn main(){}",
            "enum E{V(Unknown)} fn main(){}",
            "enum E{V{x:i64}} fn main(){}",
        ] {
            assert!(compile(src).is_err(),"unsafe/unimplemented enum field accepted: {src}");
        }
    }
    #[test]
    fn unused_function_is_checked_with_payload_pattern_locals() {
        let src="enum E{V(i64),U} fn consume(e:E){            match e{E::V(v)=>{let copied:i64=v;},E::U=>{}}}            fn main(){}";
        assert!(compile(src).is_ok(),"uninvoked payload match must be typed and checked");
    }
    #[test]
    fn unused_function_cannot_move_enum_twice() {
        let src="enum E{V(i64),U} fn wrong(e:E){            match e{E::V(v)=>{},E::U=>{}}            match e{E::V(v)=>{},E::U=>{}}}            fn main(){}";
        assert!(compile(src).is_err(),"the enum scrutinee is an affine value");
    }
    #[test]
    fn contextual_unsigned_payload_and_pattern_binding() {
        let src="enum E{V(u64)} fn main(){let e:E=E::V(4);\
            match e{E::V(v)=>{static_assert_eq(v,4);}}}";
        assert!(compile(src).is_ok());
    }
}

#[cfg(test)]
mod enum_owned_payload_0640_tests {
    use super::*;

    #[test]
    fn noncopy_struct_payload_moves_into_variant_pattern() {
        let code="struct P{n:i64} enum E{V(P),U} fn main(){
            let p:P=P{n:7};let e:E=E::V(p);let q=qubit();
            match e{E::V(x)=>{rx(x.n,q);},E::U=>{}}}";
        assert_eq!(compile(code).expect("owned payload match").angles,&[7.0]);
    }

    #[test]
    fn two_owned_payloads_are_bound_independently() {
        let code="struct P{n:i64} enum E{Pair(P,P)} fn main(){
            let a:P=P{n:4};let b:P=P{n:5};let e:E=E::Pair(a,b);
            let q=qubit();match e{E::Pair(left,right)=>{rx(left.n+right.n,q);}}}";
        assert_eq!(compile(code).expect("independent move paths").angles,&[9.0]);
    }

    #[test]
    fn nested_enum_payload_can_be_consumed_by_nested_match() {
        let code="enum Inner{V(i64)} enum Outer{Wrap(Inner),Empty} fn main(){
            let i:Inner=Inner::V(12);let o:Outer=Outer::Wrap(i);let q=qubit();
            match o{Outer::Wrap(value)=>{match value{Inner::V(n)=>{rx(n,q);}}},
                Outer::Empty=>{}}}";
        assert_eq!(compile(code).expect("nested owned enum").angles,&[12.0]);
    }

    #[test]
    fn wildcard_pattern_drops_owned_field_without_duplicating_it() {
        let code="struct P{n:i64} enum E{V(P),U} fn main(){
            let p:P=P{n:2};let e:E=E::V(p);let q=qubit();
            match e{E::V(_)=>{h(q);},E::U=>{}}}";
        assert_eq!(compile(code).unwrap().instructions.len(),1);
    }

    #[test]
    fn source_aggregate_cannot_be_used_after_enum_constructor() {
        let code="struct P{n:i64} enum E{V(P)} fn main(){
            let p:P=P{n:2};let e:E=E::V(p);let x:i64=p.n;}";
        assert!(compile(code).is_err(),"constructor must move non-Copy argument");
    }

    #[test]
    fn enum_cannot_be_matched_again_after_consuming_it() {
        let code="struct P{n:i64} enum E{V(P)} fn main(){
            let p:P=P{n:2};let e:E=E::V(p);
            match e{E::V(x)=>{}}
            match e{E::V(y)=>{}}}";
        assert!(compile(code).is_err(),"enum owner must move exactly once");
    }

    #[test]
    fn moved_pattern_binding_cannot_be_moved_twice() {
        let code="struct P{n:i64} enum E{V(P)} fn main(){
            let p:P=P{n:2};let e:E=E::V(p);
            match e{E::V(x)=>{let a:P=x;let b:P=x;}}}";
        assert!(compile(code).is_err(),"pattern binding must be affine");
    }

    #[test]
    fn nested_reference_containing_aggregate_is_rejected() {
        for code in [
            "struct R{r:&i64} struct Wrapper{nested:R} enum E{V(Wrapper)} fn main(){}",
            "struct R{r:&mut i64} enum E{V(R)} fn main(){}",
        ] {
            assert!(compile(code).is_err(),"references hidden in enum payload must not pass: {code}");
        }
    }

    #[test]
    fn aggregate_payload_type_must_match_constructor_argument() {
        let code="struct P{n:i64} struct Q{n:i64} enum E{V(P)} fn main(){
            let q:Q=Q{n:1};let e:E=E::V(q);}";
        assert!(compile(code).is_err(),"structural equality cannot replace exact TypeId");
    }

    #[test]
    fn uninvoked_function_uses_owned_pattern_bindings_safely() {
        let code="struct P{n:i64} enum E{V(P),U} fn consume(e:E){
            match e{E::V(x)=>{let n:i64=x.n;},E::U=>{}}}
            fn main(){}";
        assert!(compile(code).is_ok(),"unused function must be checked with owned patterns");
    }
}

#[cfg(test)]
mod enum_ref_patterns_0641_tests {
    use super::*;

    #[test]
    fn shared_ref_pattern_does_not_consume_enum_owner() {
        let src="enum E{V(i64),Other} fn main(){
            let e:E=E::V(6);let q=qubit();
            match &e {E::V(ref x)=>{rx(*x,q);},E::Other=>{}}
            match e {E::V(x)=>{ry(x,q);},E::Other=>{}}
        }";
        assert_eq!(compile(src).unwrap().angles,&[6.0,6.0]);
    }

    #[test]
    fn mutable_ref_pattern_writes_original_enum_field() {
        let src="enum E{V(i64),Other} fn main(){
            let mut e:E=E::V(6);let q=qubit();
            match &mut e {E::V(ref mut x)=>{*x=13;},E::Other=>{}}
            match e {E::V(x)=>{rx(x,q);},E::Other=>{}}
        }";
        assert_eq!(compile(src).unwrap().angles,&[13.0]);
    }

    #[test]
    fn sibling_mutable_enum_payloads_are_disjoint() {
        let src="enum E{Pair(i64,i64)} fn main(){
            let mut e:E=E::Pair(1,2);let q=qubit();
            match &mut e {E::Pair(ref mut a,ref mut b)=>{*a=3;*b=4;}}
            match e {E::Pair(a,b)=>{rx(a+b,q);}}
        }";
        assert_eq!(compile(src).unwrap().angles,&[7.0]);
    }

    #[test]
    fn readonly_match_rejects_exclusive_pattern() {
        let src="enum E{V(i64)} fn main(){let mut e:E=E::V(1);
            match &e{E::V(ref mut x)=>{*x=4;}}}";
        assert!(compile(src).is_err());
    }

    #[test]
    fn borrowed_enum_rejects_implicit_by_value_payload_binding() {
        let src="enum E{V(i64)} fn main(){let e:E=E::V(1);
            match &e{E::V(x)=>{let n:i64=x;}}}";
        assert!(compile(src).is_err());
    }

    #[test]
    fn owned_ref_pattern_keeps_its_enum_owner_live() {
        let src="enum E{V(i64)} fn main(){let e:E=E::V(1);let q=qubit();
            match e{E::V(ref x)=>{rx(*x,q);}}
            match e{E::V(n)=>{ry(n,q);}}}";
        assert_eq!(compile(src).unwrap().angles,&[1.0,1.0]);
    }

    #[test]
    fn enum_owner_cannot_move_while_payload_ref_is_live() {
        let src="enum E{V(i64)} fn main(){let e:E=E::V(1);
            match &e{E::V(ref x)=>{let moved:E=e;let q=qubit();rx(*x,q);}}}";
        assert!(compile(src).is_err());
    }

    #[test]
    fn mutable_borrow_requires_mutable_enum_owner() {
        let src="enum E{V(i64)} fn main(){let e:E=E::V(1);
            match &mut e{E::V(ref mut x)=>{*x=3;}}}";
        assert!(compile(src).is_err());
    }

    #[test]
    fn nested_mut_reborrow_of_enum_field_resumes_parent() {
        let src="enum E{V(i64)} fn main(){let mut e:E=E::V(2);let q=qubit();
            match &mut e{E::V(ref mut a)=>{
                {let child=&mut *a;*child=8;}
                *a=11;
            }}
            match e{E::V(x)=>{rx(x,q);}}
        }";
        assert_eq!(compile(src).unwrap().angles,&[11.0]);
    }

    #[test]
    fn borrowed_aggregate_payload_supports_field_projection() {
        let src="struct P{n:i64,m:i64} enum E{V(P)} fn main(){
            let p:P=P{n:3,m:5};let mut e:E=E::V(p);let q=qubit();
            match &mut e{E::V(ref mut inner)=>{inner.n=9;}}
            match e{E::V(inner)=>{rx(inner.n+inner.m,q);}}
        }";
        assert_eq!(compile(src).unwrap().angles,&[14.0]);
    }

    #[test]
    fn suspended_enum_ref_parent_cannot_be_used() {
        let src="enum E{V(i64)} fn main(){let mut e:E=E::V(2);
          match &mut e{E::V(ref mut a)=>{
            let child=&mut *a;*a=3;*child=4;
          }}}";
        assert!(compile(src).is_err());
    }

    #[test]
    fn selected_shared_pattern_loan_remains_valid_through_last_use() {
        let code="enum E{V(i64)} fn main(){let e:E=E::V(4);let q=qubit();
            match &e{E::V(ref a)=>{let b:i64=*a;rx(b,q);}}}";
        assert_eq!(compile(code).unwrap().angles,&[4.0]);
    }

    #[test]
    fn enum_pattern_loans_end_at_arm_scope() {
        let code="enum E{V(i64)} fn main(){let mut e:E=E::V(2);let q=qubit();
            match &mut e{E::V(ref mut a)=>{*a=9;}}
            match e{E::V(value)=>{rx(value,q);}}}";
        assert_eq!(compile(code).unwrap().angles,&[9.0]);
    }

    #[test]
    fn nested_block_reborrow_releases_child_before_parent_reuse() {
        let code="fn main(){let mut x:i64=1;let a=&mut x;{let b=&mut *a;*b=7;}*a=11;
            let q=qubit();rx(*a,q);}";
        assert_eq!(compile(code).unwrap().angles,&[11.0]);
    }

    #[test]
    fn borrowed_enum_payload_field_read_is_copy_not_move() {
        let code="struct P{x:i64} enum E{V(P)} fn main(){let p:P=P{x:7};
            let e:E=E::V(p);let q=qubit();match &e{E::V(ref a)=>{rx(a.x,q);}}
            match e{E::V(data)=>{ry(data.x,q);}}}";
        assert_eq!(compile(code).unwrap().angles,&[7.0,7.0]);
    }

    #[test]
    fn reference_field_projection_is_variant_sensitive() {
        let src="enum E{A(i64),B(i64)} fn main(){let mut e:E=E::B(2);
            let q=qubit();match &mut e{
              E::A(ref mut a)=>{*a=99;},
              E::B(ref mut b)=>{*b=5;}}
            match e{E::A(n)=>{rx(n,q);},E::B(n)=>{ry(n,q);}}
        }";
        assert_eq!(compile(src).unwrap().angles,&[5.0]);
    }
}

#[cfg(test)]
mod enum_pattern_nll_last_use_0642_tests {
    use super::*;

    #[test]
    fn shared_pattern_last_use_allows_owner_move_in_same_arm() {
        let code="enum E{V(i64)} fn main(){let e:E=E::V(3);let q=qubit();
            match &e{E::V(ref a)=>{rx(*a,q);let taken:E=e;}}}";
        assert!(compile(code).is_ok(),"shared pattern should end after last use");
    }

    #[test]
    fn mutable_pattern_last_use_allows_reinitializing_owner_in_arm() {
        let code="enum E{V(i64)} fn main(){let mut e:E=E::V(1);let q=qubit();
            match &mut e{E::V(ref mut a)=>{*a=2;e=E::V(9);}}
            match e{E::V(n)=>{rx(n,q);}}}";
        assert_eq!(compile(code).unwrap().angles,&[9.0]);
    }

    #[test]
    fn live_pattern_reference_still_prevents_early_owner_move() {
        let code="enum E{V(i64)} fn main(){let e:E=E::V(3);
            match &e{E::V(ref a)=>{let taken:E=e;let n:i64=*a;}}}";
        assert!(compile(code).is_err(),"moving an owner before last loan use is unsound");
    }

    #[test]
    fn distinct_variant_loans_do_not_escape_into_another_arm() {
        let code="enum E{A(i64),B(i64)} fn main(){let mut e:E=E::B(2);let q=qubit();
            match &mut e{
                E::A(ref mut a)=>{*a=7;},
                E::B(ref mut b)=>{*b=4;e=E::B(8);}}
            match e{E::A(n)=>{rx(n,q);},E::B(n)=>{ry(n,q);}}}";
        assert_eq!(compile(code).unwrap().angles,&[8.0]);
    }

    #[test]
    fn live_nested_child_keeps_pattern_parent_suspended() {
        let code="enum E{V(i64)} fn main(){let mut e:E=E::V(1);
            match &mut e{E::V(ref mut a)=>{
                let c=&mut *a;*a=8;*c=9;
            }}}";
        assert!(compile(code).is_err(),"a live child cannot release its parent");
    }
}

#[cfg(test)]
mod pure_match_guards_0643_tests {
    use super::*;

    #[test]
    fn guarded_bool_arm_falls_through_when_false() {
        let src="fn main(){let allow:bool=false;let q=qubit();
            match true{true if allow=>{rx(1,q);},true=>{ry(2,q);},false=>{h(q);}}}";
        assert_eq!(compile(src).unwrap().angles,&[2.0]);
    }
    #[test]
    fn guarded_bool_arm_runs_when_true() {
        let src="fn main(){let allow:bool=true;let q=qubit();
            match true{true if allow=>{rx(1,q);},true=>{ry(2,q);},false=>{h(q);}}}";
        assert_eq!(compile(src).unwrap().angles,&[1.0]);
    }
    #[test]
    fn guarded_unit_enum_variant_with_fallback() {
        let src="enum Mode{A,B} fn main(){let go:bool=false;let m:Mode=Mode::A;let q=qubit();
            match m{Mode::A if go=>{rx(1,q);},Mode::A=>{ry(3,q);},Mode::B=>{h(q);}}}";
        assert_eq!(compile(src).unwrap().angles,&[3.0]);
    }
    #[test]
    fn guarded_enum_wildcard_can_be_false() {
        let src="enum E{A,B} fn main(){let e:E=E::A;let q=qubit();
            match e{_ if false=>{rx(1,q);},E::A=>{ry(4,q);},E::B=>{h(q);}}}";
        assert_eq!(compile(src).unwrap().angles,&[4.0]);
    }
    #[test]
    fn guarded_arm_alone_does_not_prove_coverage() {
        let src="enum E{A,B} fn main(){let e:E=E::A;
            match e{E::A if true=>{},E::B=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn guarded_wildcard_alone_is_not_exhaustive() {
        let src="fn main(){match true{_ if true=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn duplicate_unconditional_enum_arm_is_rejected() {
        let src="enum E{A,B} fn main(){let e:E=E::A;
            match e{E::A=>{},E::A=>{},E::B=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn non_bool_guard_is_rejected() {
        let src="fn main(){let count:i64=1;
            match true{true if count=>{},true=>{},false=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn function_call_as_guard_is_rejected() {
        let src="fn ready()->bool{true} fn main(){
            match true{true if ready()=>{},true=>{},false=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn payload_binding_in_guard_is_explicitly_unsupported() {
        let src="enum E{A(i64),B} fn main(){let e:E=E::A(1);
            match e{E::A(v) if true=>{},E::A(v)=>{},E::B=>{}}}";
        assert!(compile(src).is_err());
    }
}

#[cfg(test)]
mod unsupported_pattern_safety_0643_tests {
    use super::*;
    #[test]
    fn nested_singleton_enum_pattern_is_exhaustive_and_lowered() {
        let src="enum Inner{N(i64)} enum Outer{W(Inner)} fn main(){
            let i:Inner=Inner::N(3);let e:Outer=Outer::W(i);let q=qubit();
            match e{Outer::W(Inner::N(value))=>{rx(value,q);}}}";
        assert_eq!(compile(src).expect("single-variant nested match").angles,&[3.0]);
    }
    #[test]
    fn partial_move_from_borrowed_enum_is_not_permitted() {
        let src="struct P{n:i64} enum E{V(P)} fn main(){
            let p:P=P{n:2};let e:E=E::V(p);
            match &e{E::V(moved)=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn named_local_regions_do_not_silently_erase_lifetime_constraints() {
        let src="fn identity<'a>(x:&'a i64)->&'a i64{x}
            fn main(){let x:i64=2;let alias:&'a i64=&x;}";
        assert!(compile(src).is_err());
    }
}

#[cfg(test)]
mod recursive_enum_patterns_0644_tests {
    use super::*;
    #[test]
    fn nested_enum_struct_destructure_transfers_copy_leaf() {
        let src="struct P{n:i64,m:i64} enum Inner{A(P),B} enum Outer{Wrap(Inner),Nil}
            fn main(){let p:P=P{n:5,m:8};let inner:Inner=Inner::A(p);
            let outer:Outer=Outer::Wrap(inner);let q=qubit();
            match outer{Outer::Wrap(Inner::A(P{n:value,m:_}))=>{rx(value,q);},
                _=>{ry(0,q);}}}";
        assert_eq!(compile(src).unwrap().angles,&[5.0]);
    }
    #[test]
    fn false_nested_discriminant_selects_fallback() {
        let src="struct P{n:i64} enum Inner{A(P),B} enum Outer{Wrap(Inner),Nil}
            fn main(){let inner:Inner=Inner::B;let outer:Outer=Outer::Wrap(inner);
            let q=qubit();match outer{Outer::Wrap(Inner::A(P{n:value}))=>{rx(value,q);},
                _=>{ry(9,q);}}}";
        assert_eq!(compile(src).unwrap().angles,&[9.0]);
    }
    #[test]
    fn two_owned_nested_aggregate_bindings_have_distinct_places() {
        let src="struct P{n:i64} enum Inner{Pair(P,P),Empty} enum Outer{Wrap(Inner)}
            fn main(){let a:P=P{n:4};let b:P=P{n:7};
            let inner:Inner=Inner::Pair(a,b);let outer:Outer=Outer::Wrap(inner);
            let q=qubit();match outer{
            Outer::Wrap(Inner::Pair(left,right))=>{rx(left.n+right.n,q);},
            _=>{ry(0,q);}}}";
        assert_eq!(compile(src).unwrap().angles,&[11.0]);
    }
    #[test]
    fn nested_discriminant_without_fallback_is_not_exhaustive(){
        let src="enum Inner{A(i64),B} enum Outer{Wrap(Inner)} fn main(){
            let i:Inner=Inner::A(3);let o:Outer=Outer::Wrap(i);
            match o{Outer::Wrap(Inner::A(x))=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn duplicate_deep_name_is_rejected(){
        let src="struct P{a:i64,b:i64} enum E{V(P)} fn main(){
            let p:P=P{a:1,b:2};let e:E=E::V(p);
            match e{E::V(P{a:x,b:x})=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn nested_type_id_mismatch_is_not_structural_typing(){
        let src="struct A{x:i64} struct B{x:i64} enum E{V(A)} fn main(){
            let a:A=A{x:1};let e:E=E::V(a);
            match e{E::V(B{x:y})=>{}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn nested_shared_pattern_ref_reads_original_payload(){
        let src="struct P{n:i64} enum Inner{A(P)} enum Outer{Wrap(Inner)} fn main(){
            let p:P=P{n:6};let inner:Inner=Inner::A(p);
            let outer:Outer=Outer::Wrap(inner);let q=qubit();
            match &outer{Outer::Wrap(Inner::A(P{n:ref x}))=>{rx(*x,q);},_=>{}}
            match outer{Outer::Wrap(Inner::A(P{n:y}))=>{ry(y,q);},_=>{}}}";
        assert_eq!(compile(src).unwrap().angles,&[6.0,6.0]);
    }
    #[test]
    fn nested_mutable_pattern_ref_releases_on_arm_exit(){
        let src="struct P{n:i64} enum Inner{A(P)} enum Outer{Wrap(Inner)} fn main(){
            let p:P=P{n:6};let inner:Inner=Inner::A(p);
            let mut outer:Outer=Outer::Wrap(inner);let q=qubit();
            match &mut outer{Outer::Wrap(Inner::A(P{n:ref mut x}))=>{*x=12;},_=>{}}
            match outer{Outer::Wrap(Inner::A(P{n:y}))=>{rx(y,q);},_=>{}}}";
        assert_eq!(compile(src).unwrap().angles,&[12.0]);
    }
    #[test]
    fn nested_borrow_cannot_move_owner_while_live(){
        let src="struct P{n:i64} enum E{V(P)} fn main(){
            let p:P=P{n:1};let e:E=E::V(p);
            match &e{E::V(P{n:ref x})=>{let removed:E=e;let q=qubit();rx(*x,q);}}}";
        assert!(compile(src).is_err());
    }
    #[test]
    fn matched_owner_cannot_be_moved_twice(){
        let src="struct P{n:i64} enum E{V(P)} fn main(){
            let p:P=P{n:1};let e:E=E::V(p);
            match e{E::V(P{n:x})=>{}}
            match e{E::V(P{n:y})=>{}}}";
        assert!(compile(src).is_err());
    }
}

#[cfg(test)]
mod deep_pattern_and_live_enum_0645_tests {
    use crate::compile;

    #[test]
    fn deep_mut_pattern_ends_after_last_use_before_owner_assignment(){
        let src="struct P{n:i64} enum Inner{A(P)} enum Outer{Wrap(Inner)} fn main(){
            let p:P=P{n:6};let inner:Inner=Inner::A(p);
            let mut outer:Outer=Outer::Wrap(inner);
            match &mut outer{Outer::Wrap(Inner::A(P{n:ref mut x}))=>{
                *x=8; outer=Outer::Wrap(Inner::A(P{n:11}));
            },_=>{}}
            let q=qubit();
            match outer{Outer::Wrap(Inner::A(P{n:y}))=>{rx(y,q);},_=>{}}
        }";
        let result=compile(src).expect("deep pattern must release at last use");
        assert_eq!(result.angles,&[11.0]);
    }
    #[test]
    fn deep_pattern_cannot_be_used_after_reinitializing_its_owner(){
        let src="struct P{n:i64} enum Inner{A(P)} enum Outer{Wrap(Inner)} fn main(){
            let p:P=P{n:6};let inner:Inner=Inner::A(p);
            let mut outer:Outer=Outer::Wrap(inner);
            match &mut outer{Outer::Wrap(Inner::A(P{n:ref mut x}))=>{
                *x=8;outer=Outer::Wrap(Inner::A(P{n:11})); *x=9;
            },_=>{}}
        }";
        assert!(compile(src).is_err(),"a live pattern reference must block owner replacement");
    }
    #[test]
    fn two_independent_owned_fields_move_across_sequential_matches(){
        let src="struct P{n:i64} enum E{Pair(P,P)} fn main(){
            let a:P=P{n:2};let b:P=P{n:3};let e:E=E::Pair(a,b);
            let q=qubit();
            match e{E::Pair(left,_)=>{rx(left.n,q);}}
            match e{E::Pair(_,right)=>{ry(right.n,q);}}
        }";
        let result=compile(src).expect("sibling should remain after partial move");
        assert_eq!(result.angles,&[2.0,3.0]);
    }
    #[test]
    fn moving_the_same_enum_payload_twice_is_rejected(){
        let src="struct P{n:i64} enum E{Pair(P,P)} fn main(){
            let a:P=P{n:2};let b:P=P{n:3};let e:E=E::Pair(a,b);
            match e{E::Pair(left,_)=>{}}
            match e{E::Pair(left,_)=>{}}
        }";
        assert!(compile(src).is_err(),"duplicate field moves must fail");
    }
    #[test]
    fn whole_enum_read_after_partial_move_is_still_rejected(){
        let src="struct P{n:i64} enum E{Pair(P,P)} fn main(){
            let a:P=P{n:2};let b:P=P{n:3};let e:E=E::Pair(a,b);
            match e{E::Pair(left,_)=>{}}
            let whole:E=e;
        }";
        assert!(compile(src).is_err(),"partially moved owner is not wholly initialized");
    }
    #[test]
    fn partially_moved_enum_can_be_wholly_reinitialized(){
        let src="struct P{n:i64} enum E{Pair(P,P)} fn main(){
            let a:P=P{n:2};let b:P=P{n:3};let mut e:E=E::Pair(a,b);
            match e{E::Pair(left,_)=>{}}
            e=E::Pair(P{n:7},P{n:8});
            let q=qubit();match e{E::Pair(x,y)=>{rx(x.n+y.n,q);}}
        }";
        assert_eq!(compile(src).unwrap().angles,&[15.0]);
    }
}

#[cfg(test)]
mod mixed_enum_move_borrow_cfg_0646_tests {
    use crate::compile;

    #[test]
    fn owned_match_mixes_move_ref_mut_across_three_fields_and_variants() {
        let src="struct P{n:i64} enum E{Empty,Single(P),Triple(P,P,i64)}
            fn main(){let left:P=P{n:2};let right:P=P{n:3};
                let mut e:E=E::Triple(left,right,4);let q=qubit();
                match e {
                    E::Triple(first,ref second,ref mut theta)=>{
                        rx(first.n+second.n,q); *theta=7;
                    }, E::Single(_)=>{}, E::Empty=>{}
                }
                match e {
                    E::Triple(_,remaining,angle)=>{ry(remaining.n+angle,q);},
                    E::Single(_)=>{}, E::Empty=>{}
                }
            }";
        assert_eq!(compile(src).expect("mixed disjoint paths").angles,&[5.0,10.0]);
    }

    #[test]
    fn owned_shared_reference_does_not_consume_a_single_payload() {
        let src="enum E{One(i64),Empty} fn main(){let e:E=E::One(9);let q=qubit();
            match e{E::One(ref x)=>{rx(*x,q);},E::Empty=>{}}
            match e{E::One(x)=>{ry(x,q);},E::Empty=>{}}
        }";
        assert_eq!(compile(src).unwrap().angles,&[9.0,9.0]);
    }

    #[test]
    fn owned_ref_mut_requires_mutable_owner() {
        let src="enum E{One(i64)} fn main(){let e:E=E::One(2);
            match e{E::One(ref mut x)=>{*x=4;}}}";
        assert!(compile(src).is_err());
    }

    #[test]
    fn owned_mut_ref_blocks_move_of_the_entire_enum_while_live() {
        let src="enum E{One(i64)} fn main(){let mut e:E=E::One(2);
            match e{E::One(ref mut x)=>{
                let moved:E=e;*x=7;
            }}}";
        assert!(compile(src).is_err());
    }

    #[test]
    fn partially_moved_enum_cannot_be_used_as_a_whole_on_a_cfg_join() {
        let src="struct P{n:i64} enum E{Pair(P,P),Empty}
            fn verify(e:E,c:bool){
                if c {
                    match e{E::Pair(first,_)=>{},E::Empty=>{}}
                } else {
                    match e{E::Pair(_,ref right)=>{},E::Empty=>{}}
                }
                let whole:E=e;
            }
            fn main(){}";
        assert!(compile(src).is_err(),"MAY-moved path at merge must block whole read");
    }

    #[test]
    fn duplicate_owned_variant_field_move_is_rejected_after_other_field_borrow() {
        let src="struct P{n:i64} enum E{Pair(P,P)} fn main(){
            let a:P=P{n:1};let b:P=P{n:2};let e:E=E::Pair(a,b);
            match e{E::Pair(first,ref second)=>{}}
            match e{E::Pair(again,_)=>{}}
        }";
        assert!(compile(src).is_err());
    }

    #[test]
    fn nested_mut_reference_and_sibling_move_use_separate_paths() {
        let src="struct P{n:i64} enum Inner{Pair(P,i64)}
            enum Outer{Data(Inner,P),None} fn main(){
                let a:P=P{n:4};let b:P=P{n:6};
                let inner:Inner=Inner::Pair(a,2);
                let mut outer:Outer=Outer::Data(inner,b);
                let q=qubit();
                match outer {
                    Outer::Data(Inner::Pair(moved,ref mut value),ref sibling)=>{
                        *value=8;rx(moved.n+sibling.n,q);
                    },Outer::None=>{}
                }
            }";
        assert_eq!(compile(src).expect("nested mixed modes").angles,&[10.0]);
    }
}

#[cfg(test)]
mod interprocedural_region_graph_0647_tests {
    use crate::compile;

    #[test]
    fn three_way_else_if_preserves_second_reference_origin() {
        let src="fn choose<'a>(c:bool,d:bool,x:&'a i64,y:&'a i64,z:&'a i64)->&'a i64{
              if c{x}else if d{y}else{z}}
              fn outer<'a>(c:bool,d:bool,x:&'a i64,y:&'a i64,z:&'a i64)->&'a i64{
                choose(c,d,x,y,z)}
              fn main(){let a:i64=3;let b:i64=11;let c:i64=29;
                let r=outer(false,true,&a,&b,&c);let q=qubit();rx(*r,q);}";
        assert_eq!(compile(src).expect("all arms certified").angles,&[11.0]);
    }

    #[test]
    fn three_way_else_if_preserves_fallthrough_reference_origin() {
        let src="fn choose<'a>(c:bool,d:bool,x:&'a i64,y:&'a i64,z:&'a i64)->&'a i64{
              if c{x}else if d{y}else{z}}
              fn main(){let a:i64=3;let b:i64=11;let c:i64=29;
                let r=choose(false,false,&a,&b,&c);let q=qubit();ry(*r,q);}";
        assert_eq!(compile(src).expect("fallthrough origin").angles,&[29.0]);
    }

    #[test]
    fn three_way_inactive_invalid_lifetime_is_not_ignored() {
        let src="fn wrong<'a,'b,'c>(p:bool,q:bool,x:&'a i64,y:&'b i64,z:&'c i64)->&'a i64
              where 'b:'a {if p{x}else if q{y}else{z}} fn main(){}";
        assert!(compile(src).is_err(),"all possible returned regions need bounds");
    }

    #[test]
    fn three_way_explicit_outlives_proves_all_sources() {
        let src="fn choose<'a,'b,'c>(p:bool,q:bool,x:&'a i64,y:&'b i64,z:&'c i64)->&'a i64
              where 'b:'a,'c:'b {if p{x}else if q{y}else{z}} fn main(){}";
        assert!(compile(src).is_ok(),"transitive lifetime bounds certify every arm");
    }

    #[test]
    fn memoized_summary_handles_deep_acyclic_chain() {
        let mut src="fn f0<'a>(x:&'a i64)->&'a i64{x} ".to_owned();
        for i in 1..24 {
            src.push_str(&format!("fn f{i}<'a>(x:&'a i64)->&'a i64{{f{}(x)}} ",i-1));
        }
        src.push_str("fn main(){}");
        compile(&src).expect("pure 24-function chain should not depend on a depth-16 cutoff");
    }

    #[test]
    fn branching_diamond_reuses_shared_function_summary() {
        let src="fn core<'a>(x:&'a i64)->&'a i64{x}
          fn left<'a>(x:&'a i64)->&'a i64{core(x)}
          fn right<'a>(x:&'a i64)->&'a i64{core(x)}
          fn diamond<'a>(flag:bool,x:&'a i64)->&'a i64{
            if flag{left(x)}else{right(x)}}
          fn main(){let n:i64=42;let r=diamond(false,&n);let q=qubit();rx(*r,q);}";
        assert_eq!(compile(src).expect("diamond call graph").angles,&[42.0]);
    }

    #[test]
    fn impure_else_if_condition_fails_closed_even_in_uncalled_function() {
        let src="fn bad<'a>(x:&'a i64,y:&'a i64)->&'a i64{
          if true{x}else if *y{y}else{x}} fn main(){}";
        assert!(compile(src).is_err(),"non-bool/side-effecting conditions are unproven");
    }

    #[test]
    fn recursive_cycle_cannot_forge_reference_provenance() {
        let src="fn first<'a>(x:&'a i64)->&'a i64{second(x)}
          fn second<'a>(x:&'a i64)->&'a i64{third(x)}
          fn third<'a>(x:&'a i64)->&'a i64{first(x)} fn main(){}";
        assert!(compile(src).is_err(),"recursion has no trusted finite summary");
    }

    #[test]
    fn ambiguous_mutable_call_must_not_alias_an_exclusive_parameter() {
        let src="fn choose<'a>(p:bool,x:&'a mut i64,y:&'a mut i64)->&'a mut i64{
          if p{x}else{y}}
          fn bad<'a>(x:&'a mut i64)->&'a mut i64{choose(true,x,x)} fn main(){}";
        assert!(compile(src).is_err(),"two exclusive actuals may not have one owner");
    }
}

#[cfg(test)]
mod projected_interprocedural_region_0648_tests {
    use super::*;

    #[test]
    fn two_distinct_fields_keep_distinct_typed_paths_through_a_call() {
        let source="struct Pair{left:i64,right:i64}
          fn choose<'a>(flag:bool,p:&'a Pair)->&'a i64{
            if flag{&p.left}else{&p.right}}
          fn forward<'a>(flag:bool,p:&'a Pair)->&'a i64{
            choose(flag,p)}
          fn main(){}";
        let tokens=syntax::lex(source).unwrap();
        let mut front=Front::new(tokens);
        front.parse_definitions().unwrap();
        let mut summaries=ReferenceSummarySolver::new(&front.fn_defs,&front.cur.tokens,
            &front.types,&front.type_ids,&front.type_names);
        assert_eq!(summaries.prove("forward"),Some(0b10));
        let paths=summaries.projected("forward").expect("exact projected summary");
        assert_eq!(paths.len(),2);
        assert!(paths.iter().all(|origin|origin.parameter==1 && origin.path.len()==1));
        let mut field_ids=paths.iter().map(|origin|origin.path[0].field.0).collect::<Vec<_>>();
        field_ids.sort_unstable();
        assert_eq!(field_ids,vec![0,1]);
    }

    #[test]
    fn nested_projection_in_return_is_typed_and_has_full_path() {
        let source="struct Inner{value:i64} struct Outer{inner:Inner,other:i64}
          fn get<'a>(p:&'a Outer)->&'a i64{&p.inner.value}
          fn forward<'a>(p:&'a Outer)->&'a i64{get(p)} fn main(){}";
        let tokens=syntax::lex(source).unwrap();
        let mut front=Front::new(tokens);
        front.parse_definitions().unwrap();
        let mut summaries=ReferenceSummarySolver::new(&front.fn_defs,&front.cur.tokens,
            &front.types,&front.type_ids,&front.type_names);
        assert_eq!(summaries.prove("forward"),Some(1));
        let paths=summaries.projected("forward").unwrap();
        assert_eq!(paths.len(),1);
        assert_eq!(paths[0].parameter,0);
        assert_eq!(paths[0].path.len(),2);
        assert_eq!(paths[0].path[0].field,FieldId(0));
        assert_eq!(paths[0].path[1].field,FieldId(0));
        assert_ne!(paths[0].path[0].aggregate,paths[0].path[1].aggregate);
    }

    #[test]
    fn mutable_projection_of_disjoint_fields_is_valid_in_pure_branches() {
        let src="struct Pair{left:i64,right:i64}
          fn selected<'a>(flag:bool,p:&'a mut Pair)->&'a mut i64{
            if flag{&mut p.left}else{&mut p.right}}
          fn main(){}";
        assert!(compile(src).is_ok(),"two exclusive alternatives never coexist on one CFG path");
    }

    #[test]
    fn wrong_projected_return_pointee_is_rejected_without_calling_function() {
        let src="struct Mixed{count:i64,ready:bool}
          fn wrong<'a>(p:&'a Mixed)->&'a i64{&p.ready} fn main(){}";
        assert!(compile(src).is_err(),"an uncalled function may not forge &i64 from &bool");
    }

    #[test]
    fn borrowed_field_by_value_cannot_be_returned_as_reference() {
        let src="struct Data{v:i64} fn bad<'a>(p:&'a Data)->&'a i64{p.v} fn main(){}";
        assert!(compile(src).is_err(),"a scalar field read is not a returned borrow");
    }

    #[test]
    fn mutable_field_reborrow_requires_mutable_input() {
        let src="struct Data{v:i64} fn bad<'a>(p:&'a Data)->&'a mut i64{&mut p.v}
          fn main(){}";
        assert!(compile(src).is_err(),"shared input does not grant exclusive field access");
    }

    #[test]
    fn typo_in_nested_return_path_is_rejected() {
        let src="struct Inner{value:i64} struct Outer{inner:Inner}
          fn bad<'a>(p:&'a Outer)->&'a i64{&p.inner.missing} fn main(){}";
        assert!(compile(src).is_err(),"unknown nested field cannot be a proven origin");
    }

    #[test]
    fn uncalled_helper_cannot_pass_same_mutable_reference_twice() {
        let src="fn select<'a>(a:&'a mut i64,b:&'a mut i64)->&'a mut i64{a}
          fn bad<'a>(x:&'a mut i64)->&'a mut i64{select(x,x)}
          fn main(){}";
        assert!(compile(src).is_err(),"duplicate &mut actuals must fail in preflight");
    }

    #[test]
    fn alternate_projected_fields_require_all_outlives_bounds() {
        let wrong="struct Pair{left:i64,right:i64}
          fn choose<'a,'b>(flag:bool,x:&'a Pair,y:&'b Pair)->&'a i64{
            if flag{&x.left}else{&y.right}} fn main(){}";
        assert!(compile(wrong).is_err(),"unproven alternative lifetime must be rejected");
        let correct="struct Pair{left:i64,right:i64}
          fn choose<'a,'b>(flag:bool,x:&'a Pair,y:&'b Pair)->&'a i64
          where 'b:'a {if flag{&x.left}else{&y.right}} fn main(){}";
        assert!(compile(correct).is_ok(),"a declared universal bound covers both alternatives");
    }

    #[test]
    fn projected_return_is_rejected_if_its_source_lifetime_is_too_short() {
        let src="struct Pair{left:i64,right:i64}
          fn bad<'a,'b>(p:&'b Pair)->&'a i64{&p.left} fn main(){}";
        assert!(compile(src).is_err(),"typed projections still obey universal outlives");
    }
}

#[cfg(test)]
mod certified_interproc_movepaths_0649_tests {
    use crate::compile;

    #[test]
    fn nested_unit_calls_preserve_unmoved_field() {
        let source="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
            fn consume(x:Blob){} fn forward(x:Blob){consume(x);}
            fn main(){let p:Pair=Pair{left:Blob{n:1},right:Blob{n:2}};
                forward(p.left);let q=qubit();rx(p.right.n,q);}";
        assert_eq!(compile(source).expect("verified call graph").angles,&[2.0]);
    }
    #[test]
    fn conditional_move_through_call_blocks_whole_owner() {
        let source="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
            fn consume(x:Blob){} fn main(){let p:Pair=Pair{left:Blob{n:1},right:Blob{n:2}};
                if false{consume(p.left);}else{}let moved:Pair=p;}";
        assert!(compile(source).is_err(),"untaken CFG arm must still move a field");
    }
    #[test]
    fn duplicate_argument_must_not_copy_affine_field() {
        let source="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
            fn consume_two(x:Blob,y:Blob){} fn main(){let p:Pair=Pair{left:Blob{n:1},right:Blob{n:2}};
                consume_two(p.left,p.left);}";
        assert!(compile(source).is_err(),"two by-value arguments cannot reuse the field");
    }
    #[test]
    fn borrowed_sibling_stays_live_after_move_on_other_field() {
        let source="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
            fn consume(x:Blob){} fn main(){let p:Pair=Pair{left:Blob{n:1},right:Blob{n:2}};
                consume(p.left);let q=qubit();rx(p.right.n,q);}";
        assert_eq!(compile(source).expect("sibling field must remain initialized").angles,&[2.0]);
    }
    #[test]
    fn reference_return_still_uses_region_contract() {
        let source="fn identity<'a>(x:&'a i64)->&'a i64{x}
            fn main(){let n:i64=4;let r=identity(&n);let q=qubit();rx(*r,q);}";
        assert_eq!(compile(source).expect("existing reference solve").angles,&[4.0]);
    }
    #[test]
    fn enum_payload_move_and_borrow_cross_a_verified_call() {
        let source="struct Blob{n:i64} enum E{Pair(Blob,Blob)}
            fn consume(x:Blob){} fn inspect(x:&Blob){}
            fn main(){let e:E=E::Pair(Blob{n:2},Blob{n:5});
                let q=qubit();match e{E::Pair(first,ref second)=>{
                    consume(first);inspect(second);rx(second.n,q);
                }}}";
        assert_eq!(compile(source).expect("distinct enum payload paths").angles,&[5.0]);
    }
    #[test]
    fn bad_reference_return_is_not_a_trusted_unit_call() {
        let source="fn bad<'a,'b>(x:&'a i64,y:&'b i64)->&'a i64{y}
            fn main(){}";
        assert!(compile(source).is_err(),"caller summary cannot bypass outlives proof");
    }
}

#[cfg(test)]
mod interproc_return_and_field_effects_0650_tests {
    use crate::compile;

    #[test]
    fn field_write_and_returned_mut_reference_use_same_owner() {
        let src="struct Pair{left:i64,right:i64}
          fn update<'a>(p:&'a mut Pair)->&'a mut i64{p.right=7;&mut p.left}
          fn main(){let mut p:Pair=Pair{left:1,right:2};
            let r=update(&mut p);*r=8;
            let q=qubit();rx(*r,q);ry(p.right,q);}";
        let compiled=compile(src).expect("verified effect and returned provenance");
        assert_eq!(compiled.angles,&[8.0,7.0]);
    }
    #[test]
    fn returned_projection_is_forwarded_through_another_function() {
        let src="struct Pair{left:i64,right:i64}
          fn update<'a>(p:&'a mut Pair)->&'a mut i64{p.right=7;&mut p.left}
          fn forward<'a>(p:&'a mut Pair)->&'a mut i64{update(p)}
          fn main(){let mut p:Pair=Pair{left:1,right:2};
            let r=forward(&mut p);*r=11;
            let q=qubit();rx(*r,q);ry(p.right,q);}";
        assert_eq!(compile(src).expect("forwarded effect + provenance").angles,&[11.0,7.0]);
    }
    #[test]
    fn returned_shared_field_does_not_move_unrelated_affine_field() {
        let src="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
          fn get<'a>(p:&'a Pair)->&'a Blob{&p.left}
          fn main(){let p:Pair=Pair{left:Blob{n:3},right:Blob{n:4}};
            let r=get(&p);let other:Blob=p.right;
            let q=qubit();rx(r.n,q);ry(other.n,q);}";
        assert_eq!(compile(src).expect("field-sensitive returned borrow").angles,&[3.0,4.0]);
    }
    #[test]
    fn temporary_shared_parameter_releases_unrelated_affine_sibling() {
        let src="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
          fn left<'a>(p:&'a Pair)->&'a Blob{&p.left}
          fn main(){let p:Pair=Pair{left:Blob{n:3},right:Blob{n:4}};
            let borrowed=left(&p);let other:Blob=p.right;
            let q=qubit();rx(borrowed.n,q);ry(other.n,q);}";
        assert_eq!(compile(src).expect("temporary root loan must be field-sensitive").angles,&[3.0,4.0]);
    }
    #[test]
    fn narrowed_temporary_still_prevents_move_of_borrowed_field() {
        let src="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
          fn left<'a>(p:&'a Pair)->&'a Blob{&p.left}
          fn main(){let p:Pair=Pair{left:Blob{n:3},right:Blob{n:4}};
            let borrowed=left(&p);let forbidden:Blob=p.left;
            let q=qubit();rx(borrowed.n,q);}";
        assert!(compile(src).is_err(),"returned borrow must still protect the borrowed field");
    }
    #[test]
    fn existing_named_root_reference_is_not_narrowed() {
        let src="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
          fn left<'a>(p:&'a Pair)->&'a Blob{&p.left}
          fn main(){let p:Pair=Pair{left:Blob{n:3},right:Blob{n:4}};
            let whole=&p;let borrowed=left(whole);let forbidden:Blob=p.right;
            let q=qubit();rx(borrowed.n,q);}";
        assert!(compile(src).is_err(),"named whole-owner lease must retain its root protection");
    }
    #[test]
    fn nested_returned_projection_can_move_separate_outer_field() {
        let src="struct Blob{n:i64} struct Inner{left:Blob,right:Blob}
          struct Outer{inner:Inner,tail:Blob}
          fn inside<'a>(p:&'a Outer)->&'a Blob{&p.inner.left}
          fn main(){let x:Outer=Outer{inner:Inner{left:Blob{n:2},right:Blob{n:3}},tail:Blob{n:4}};
            let r=inside(&x);let tail:Blob=x.tail;
            let q=qubit();rx(r.n,q);ry(tail.n,q);}";
        assert_eq!(compile(src).expect("deep projection keeps separate MovePath").angles,&[2.0,4.0]);
    }
    #[test]
    fn forwarding_chain_preserves_provenance_when_root_shortened() {
        let src="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
          fn left<'a>(p:&'a Pair)->&'a Blob{&p.left}
          fn forwarding<'a>(p:&'a Pair)->&'a Blob{left(p)}
          fn main(){let p:Pair=Pair{left:Blob{n:3},right:Blob{n:4}};
            let borrowed=forwarding(&p);let other:Blob=p.right;
            let q=qubit();rx(borrowed.n,q);ry(other.n,q);}";
        assert_eq!(compile(src).expect("loan narrowing must retain origin ancestry").angles,&[3.0,4.0]);
    }
    #[test]
    fn wrong_mutable_return_lifetime_is_not_certified() {
        let src="struct Pair{left:i64,right:i64}
          fn bad<'a,'b>(p:&'b mut Pair)->&'a mut i64{p.right=7;&mut p.left}
          fn main(){}";
        assert!(compile(src).is_err());
    }
}

#[cfg(test)]
mod interproc_alternative_reference_phi_0651_tests {
    use crate::compile;

    #[test]
    fn conditional_field_return_reads_selected_arm() {
        let src="struct Blob{n:i64} struct Pair{left:Blob,right:Blob}
            fn pick<'a>(which:bool,p:&'a Pair)->&'a Blob{
                if which{&p.left}else{&p.right}}
            fn main(){let p:Pair=Pair{left:Blob{n:3},right:Blob{n:4}};
                let r=pick(false,&p);let q=qubit();rx(r.n,q);}";
        assert_eq!(compile(src).expect("branch-specific field provenance").angles,&[4.0]);
    }
    #[test]
    fn independent_third_field_can_move_while_alternative_is_live() {
        let src="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
            fn pick<'a>(flag:bool,t:&'a Tri)->&'a Blob{
                if flag{&t.a}else{&t.b}}
            fn main(){let t:Tri=Tri{a:Blob{n:1},b:Blob{n:2},c:Blob{n:3}};
                let r=pick(true,&t);let spare:Blob=t.c;
                let q=qubit();rx(r.n,q);ry(spare.n,q);}";
        assert_eq!(compile(src).expect("disjoint sibling remains movable").angles,&[1.0,3.0]);
    }
    #[test]
    fn alternative_return_must_obey_each_lifetime_bound() {
        let src="struct P{a:i64,b:i64}
            fn bad<'a,'b>(flag:bool,x:&'a P,y:&'b P)->&'a i64{
                if flag{&x.a}else{&y.b}}
            fn main(){}";
        assert!(compile(src).is_err(),"must never invent missing 'b:'a");
    }
}

#[cfg(test)]
mod return_phi_forwarding_0652_tests {
    use crate::compile;

    #[test]
    fn two_function_chain_preserves_selected_reference(){
        let src="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
            fn choose<'a>(flag:bool,t:&'a Tri)->&'a Blob{
                if flag{&t.a}else{&t.b}}
            fn relay<'a>(flag:bool,t:&'a Tri)->&'a Blob{choose(flag,t)}
            fn main(){let t:Tri=Tri{a:Blob{n:1},b:Blob{n:2},c:Blob{n:3}};
                let r=relay(false,&t);let spare:Blob=t.c;
                let q=qubit();rx(r.n,q);ry(spare.n,q);}";
        assert_eq!(compile(src).expect("transparent multi-origin wrapper").angles,
            &[2.0,3.0]);
    }
    #[test]
    fn three_function_chain_preserves_alternatives(){
        let src="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
            fn choose<'a>(flag:bool,t:&'a Tri)->&'a Blob{
                if flag{&t.a}else{&t.b}}
            fn relay<'a>(flag:bool,t:&'a Tri)->&'a Blob{return choose(flag,t);}
            fn top<'a>(flag:bool,t:&'a Tri)->&'a Blob{relay(flag,t)}
            fn main(){let t:Tri=Tri{a:Blob{n:4},b:Blob{n:5},c:Blob{n:6}};
                let r=top(true,&t);let spare:Blob=t.c;
                let q=qubit();rx(r.n,q);ry(spare.n,q);}";
        assert_eq!(compile(src).expect("PHI projection survives multiple calls").angles,
            &[4.0,6.0]);
    }
    #[test]
    fn one_of_two_borrowed_fields_cannot_move_through_wrapper(){
        let src="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
            fn choose<'a>(flag:bool,t:&'a Tri)->&'a Blob{
                if flag{&t.a}else{&t.b}}
            fn relay<'a>(flag:bool,t:&'a Tri)->&'a Blob{choose(flag,t)}
            fn main(){let t:Tri=Tri{a:Blob{n:1},b:Blob{n:2},c:Blob{n:3}};
                let r=relay(true,&t);let stolen:Blob=t.b;
                let q=qubit();rx(r.n,q);}";
        assert!(compile(src).is_err(),"all returned alternatives must protect their referents");
    }
    #[test]
    fn invalid_universal_lifetime_is_not_certified_through_wrapper(){
        let src="struct Pair{a:i64,b:i64}
            fn choose<'a,'b>(flag:bool,x:&'a Pair,y:&'b Pair)->&'a i64{
                if flag{&x.a}else{&y.b}}
            fn relay<'a,'b>(flag:bool,x:&'a Pair,y:&'b Pair)->&'a i64{
                choose(flag,x,y)}
            fn main(){}";
        assert!(compile(src).is_err(),"a chain must not erase missing lifetime bounds");
    }
}

#[cfg(test)]
mod return_phi_forwarding_0652_fix1_tests {
    use crate::compile;

    const TYPES:&str="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
        fn choose<'a>(flag:bool,t:&'a Tri)->&'a Blob{
            if flag{&t.a}else{&t.b}}
        fn relay<'a>(flag:bool,t:&'a Tri)->&'a Blob{choose(flag,t)}";

    #[test]
    fn unselected_first_field_is_still_borrowed_through_wrapper() {
        let src=format!("{TYPES} fn main(){{
            let t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(false,&t);let forbidden:Blob=t.a;
            let q=qubit();rx(r.n,q);}}");
        assert!(compile(&src).is_err(),"PHI must protect unchosen first origin");
    }
    #[test]
    fn unselected_second_field_is_still_borrowed_through_wrapper() {
        let src=format!("{TYPES} fn main(){{
            let t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(true,&t);let forbidden:Blob=t.b;
            let q=qubit();rx(r.n,q);}}");
        assert!(compile(&src).is_err(),"PHI must protect unchosen second origin");
    }
    #[test]
    fn unrelated_third_field_remains_movable_on_both_arms() {
        for flag in [true,false] {
            let src=format!("{TYPES} fn main(){{
                let t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
                let r=relay({flag},&t);let spare:Blob=t.c;
                let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
            let result=compile(&src).expect("disjoint third field must remain movable");
            assert_eq!(result.angles,&[if flag{1.0}else{2.0},3.0]);
        }
    }
    #[test]
    fn two_argument_phi_guards_an_unselected_owner() {
        let src="struct Blob{n:i64} struct Pair{a:Blob,b:Blob}
            fn choose<'a>(flag:bool,x:&'a Pair,y:&'a Pair)->&'a Blob{
                if flag{&x.a}else{&y.b}}
            fn main(){let x:Pair=Pair{a:Blob{n:1},b:Blob{n:2}};
                let y:Pair=Pair{a:Blob{n:3},b:Blob{n:4}};
                let r=choose(false,&x,&y);let forbidden:Blob=x.a;
                let q=qubit();rx(r.n,q);}";
        assert!(compile(src).is_err(),"unselected owner must keep projected loan");
    }
    #[test]
    fn two_argument_phi_allows_unrelated_sibling_of_unselected_owner() {
        let src="struct Blob{n:i64} struct Pair{a:Blob,b:Blob}
            fn choose<'a>(flag:bool,x:&'a Pair,y:&'a Pair)->&'a Blob{
                if flag{&x.a}else{&y.b}}
            fn main(){let x:Pair=Pair{a:Blob{n:1},b:Blob{n:2}};
                let y:Pair=Pair{a:Blob{n:3},b:Blob{n:4}};
                let r=choose(false,&x,&y);let spare:Blob=x.b;
                let q=qubit();rx(r.n,q);ry(spare.n,q);}";
        assert_eq!(compile(src).expect("disjoint owner sibling remains live").angles,&[4.0,2.0]);
    }
    #[test]
    fn returned_phi_guards_end_at_end_of_scope() {
        let src=format!("{TYPES} fn main(){{
            let t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let q=qubit();{{let r=relay(true,&t);rx(r.n,q);}}
            let moved:Blob=t.b;ry(moved.n,q);}}");
        assert_eq!(compile(&src).expect("PHI guards are released with last result handle").angles,&[1.0,2.0]);
    }
}

#[cfg(test)]
mod mutable_return_phi_field_guards_0653_tests {
    use crate::compile;

    const TYPES:&str="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
        fn choose<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{
            if flag{&mut t.a}else{&mut t.b}}
        fn relay<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{
            choose(flag,t)}";

    #[test]
    fn returned_mut_phi_true_arm_writes_selected_and_moves_disjoint_sibling() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(true,&mut t);let spare:Blob=t.c;
            *r=Blob{{n:9}};
            let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
        assert_eq!(compile(&src).expect("exact mutable PHI guards should allow disjoint move and selected write")
            .angles,&[9.0,3.0]);
    }
    #[test]
    fn returned_mut_phi_false_arm_writes_selected_and_moves_disjoint_sibling() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(false,&mut t);let spare:Blob=t.c;
            *r=Blob{{n:8}};
            let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
        assert_eq!(compile(&src).expect("other PHI arm must be writable")
            .angles,&[8.0,3.0]);
    }
    #[test]
    fn mutable_phi_unselected_second_field_remains_exclusive() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(true,&mut t);let forbidden:Blob=t.b;
            let q=qubit();rx(r.n,q);}}");
        let error=compile(&src).expect_err("all possible mutable referents must be protected");
        assert!(error.message.contains("borrow"),"{error:?}");
    }
    #[test]
    fn mutable_phi_unselected_first_field_remains_exclusive() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(false,&mut t);let forbidden:Blob=t.a;
            let q=qubit();rx(r.n,q);}}");
        let error=compile(&src).expect_err("the other mutable possibility must be protected");
        assert!(error.message.contains("borrow"),"{error:?}");
    }
    #[test]
    fn mutable_phi_selected_field_cannot_be_moved_from_owner() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(true,&mut t);let forbidden:Blob=t.a;
            let q=qubit();rx(r.n,q);}}");
        assert!(compile(&src).is_err());
    }
    #[test]
    fn mutable_phi_guards_disjoint_mutable_borrow() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(true,&mut t);let c=&mut t.c;
            c.n=12;let q=qubit();rx(r.n,q);ry(c.n,q);}}");
        assert_eq!(compile(&src).expect("&mut PHI must allow independent mutable sibling").angles,&[1.0,12.0]);
    }
    #[test]
    fn mutable_phi_guards_reject_other_borrow_on_possible_referent() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=relay(true,&mut t);let x=&t.b;
            let q=qubit();rx(r.n,q);ry(x.n,q);}}");
        assert!(compile(&src).is_err(),"shared borrow of unselected mutable referent is prohibited");
    }
    #[test]
    fn mutable_phi_release_at_scope_end() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let q=qubit();{{let r=relay(false,&mut t);*r=Blob{{n:8}};rx(r.n,q);}}
            let moved:Blob=t.a;ry(moved.n,q);}}");
        assert_eq!(compile(&src).expect("guards must end after last returned reference").angles,&[8.0,1.0]);
    }
    #[test]
    fn named_mutable_source_remains_wide() {
        let src=format!("{TYPES} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let whole=&mut t;let r=relay(true,whole);
            let forbidden:Blob=t.c;let q=qubit();rx(r.n,q);}}");
        assert!(compile(&src).is_err(),"named mutable root must not be shortened");
    }
    #[test]
    fn single_origin_mutable_reference_still_writes() {
        let src="fn identity<'a>(x:&'a mut i64)->&'a mut i64{x}
            fn main(){let mut n:i64=2;let r=identity(&mut n);*r=9;
            let q=qubit();rx(*r,q);}";
        assert_eq!(compile(src).expect("single-path mutable return must remain writable").angles,&[9.0]);
    }
    #[test]
    fn nested_mutable_phi_retains_field_projection_and_allows_outer_sibling() {
        let src="struct Blob{n:i64} struct Inner{a:Blob,b:Blob} struct Outer{inner:Inner,tail:Blob}
            fn pick<'a>(flag:bool,t:&'a mut Outer)->&'a mut Blob{
                if flag{&mut t.inner.a}else{&mut t.inner.b}}
            fn main(){let mut t:Outer=Outer{inner:Inner{a:Blob{n:1},b:Blob{n:2}},tail:Blob{n:3}};
                let r=pick(true,&mut t);let spare:Blob=t.tail;
                *r=Blob{n:7};let q=qubit();rx(r.n,q);ry(spare.n,q);}";
        assert_eq!(compile(src).expect("nested &mut PHI projected guards").angles,&[7.0,3.0]);
    }
}

#[cfg(test)]
mod effectful_phi_chain_0654_tests {
    use crate::compile;
    const SETUP:&str="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
        fn choose<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{
            if flag{&mut t.a}else{&mut t.b}}
        fn relay<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{
            t.c.n=9;choose(flag,t)}
        fn hop<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{
            return relay(flag,t);}";
    #[test]
    fn field_write_before_multi_origin_return_preserves_third_field(){
        let src=format!("{SETUP} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=hop(false,&mut t);*r=Blob{{n:7}};
            let q=qubit();rx(r.n,q);ry(t.c.n,q);}}");
        assert_eq!(compile(&src).expect("effectful forwarding retains two origins").angles,
            &[7.0,9.0]);
    }
    #[test]
    fn possible_unselected_origin_cannot_move_after_effectful_wrapper(){
        let src=format!("{SETUP} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=hop(true,&mut t);let illegal:Blob=t.b;
            let q=qubit();rx(r.n,q);}}");
        assert!(compile(&src).is_err(),"forwarding cannot erase alternative &mut guards");
    }
    #[test]
    fn effectful_wrapper_must_not_erase_lifetime_bounds(){
        let src="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
            fn choose<'a,'b>(flag:bool,x:&'a mut Tri,y:&'b mut Tri)->&'a mut Blob{
                if flag{&mut x.a}else{&mut y.b}}
            fn relay<'a,'b>(flag:bool,x:&'a mut Tri,y:&'b mut Tri)->&'a mut Blob{
                x.c.n=9;choose(flag,x,y)} fn main(){}";
        assert!(compile(src).is_err(),"missing 'b:'a bound must fail");
    }
    #[test]
    fn effectful_phi_return_chain_preserves_unrelated_move(){
        let src=format!("{SETUP} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=hop(true,&mut t);let spare:Blob=t.c;
            *r=Blob{{n:8}};
            let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
        assert_eq!(compile(&src).expect("certified PHI return must not borrow unrelated field")
            .angles,&[8.0,9.0]);
    }
    #[test]
    fn effectful_phi_false_arm_preserves_unrelated_field_move(){
        let src=format!("{SETUP} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=hop(false,&mut t);let spare:Blob=t.c;
            *r=Blob{{n:8}};
            let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
        assert_eq!(compile(&src).expect("false PHI arm protects a/b, not c")
            .angles,&[8.0,9.0]);
    }
    #[test]
    fn effectful_phi_four_hops_preserve_unrelated_field_move(){
        let src=format!("{SETUP}
            fn top<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{{hop(flag,t)}}
            fn upper<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{{top(flag,t)}}
            fn main(){{let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
                let r=upper(false,&mut t);let spare:Blob=t.c;
                *r=Blob{{n:7}};let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
        assert_eq!(compile(&src).expect("verified forwarding chain retains precise guard paths")
            .angles,&[7.0,9.0]);
    }
    #[test]
    fn effectful_phi_both_arms_reject_moving_possible_referents(){
        for (flag,field) in [("true","b"),("false","a")] {
            let src=format!("{SETUP} fn main(){{
                let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
                let r=hop({flag},&mut t);let illegal:Blob=t.{field};
                let q=qubit();rx(r.n,q);}}");
            let error=compile(&src).expect_err("both PHI alternatives must remain borrowed");
            assert!(error.message.contains("borrow"),"{error:?}");
        }
    }
    #[test]
    fn effectful_phi_return_three_hops_preserve_all_guards(){
        let src=format!("{SETUP}
            fn top<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{{hop(flag,t)}}
            fn main(){{
                let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
                let r=top(false,&mut t);let illegal:Blob=t.a;
                let q=qubit();rx(r.n,q);}}");
        let error=compile(&src)
            .expect_err("forwarded PHI must protect even an unselected alternative");
        assert!(error.message.contains("borrow"),"{error:?}");
    }
}

#[cfg(test)]
mod conditional_effect_phi_0655_tests {
    use crate::compile;
    const TYPES:&str="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
        fn choose<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{
            if flag{&mut t.a}else{&mut t.b}}";
    const BRANCH:&str="
        fn branch<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{
            if flag {t.c.n=9;} else {t.c.n=11;}
            choose(flag,t)}
        fn forward<'a>(flag:bool,t:&'a mut Tri)->&'a mut Blob{
            branch(flag,t)}";
    const NESTED:&str="
        fn write_c(t:&mut Tri){t.c.n=13;}
        fn nested<'a>(flag:bool,alt:bool,t:&'a mut Tri)->&'a mut Blob{
            if flag {write_c(t);}
            else if alt {t.c.n=14;}
            else {t.c.n=15;}
            choose(flag,t)}
        fn forward2<'a>(flag:bool,alt:bool,t:&'a mut Tri)->&'a mut Blob{
            nested(flag,alt,t)}
        fn forward3<'a>(flag:bool,alt:bool,t:&'a mut Tri)->&'a mut Blob{
            forward2(flag,alt,t)}";
    #[test]
    fn conditional_effectful_phi_true_arm_preserves_unrelated_move(){
        let src=format!("{TYPES}{BRANCH} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=forward(true,&mut t);let spare:Blob=t.c;
            *r=Blob{{n:7}};let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
        assert_eq!(compile(&src).expect("conditional true arm is MIR-certified")
            .angles,&[7.0,9.0]);
    }
    #[test]
    fn conditional_effectful_phi_false_arm_preserves_unrelated_move(){
        let src=format!("{TYPES}{BRANCH} fn main(){{
            let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
            let r=forward(false,&mut t);let spare:Blob=t.c;
            *r=Blob{{n:8}};let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
        assert_eq!(compile(&src).expect("conditional false arm is MIR-certified")
            .angles,&[8.0,11.0]);
    }
    #[test]
    fn nested_else_if_call_effects_keep_exact_sibling_paths(){
        for (first,second,expected) in [(true,false,13.0),
            (false,true,14.0),(false,false,15.0)] {
            let src=format!("{TYPES}{NESTED} fn main(){{
                let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
                let r=forward3({first},{second},&mut t);
                let spare:Blob=t.c;*r=Blob{{n:8}};
                let q=qubit();rx(r.n,q);ry(spare.n,q);}}");
            assert_eq!(compile(&src).expect("all CFG arms and three hops certified")
                .angles,&[8.0,expected]);
        }
    }
    #[test]
    fn conditional_phi_alternative_remains_borrowed_through_three_hops(){
        for (first,other) in [(true,"b"),(false,"a")] {
            let src=format!("{TYPES}{NESTED} fn main(){{
                let mut t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};
                let r=forward3({first},true,&mut t);
                let forbidden:Blob=t.{other};let q=qubit();rx(r.n,q);}}");
            assert!(compile(&src).is_err(),"unselected alternative must stay guarded");
        }
    }
    #[test]
    fn conditional_return_does_not_hide_bad_lifetime(){
        let src="struct Blob{n:i64} struct Tri{a:Blob,b:Blob,c:Blob}
            fn choose<'a,'b>(flag:bool,x:&'a mut Tri,y:&'b mut Tri)->&'a mut Blob{
                if flag{&mut x.a}else{&mut y.b}}
            fn forward<'a,'b>(flag:bool,x:&'a mut Tri,y:&'b mut Tri)->&'a mut Blob{
                if flag {x.c.n=8;}else{y.c.n=7;}
                choose(flag,x,y)} fn main(){}";
        assert!(compile(src).is_err(),"every returned region must outlive the result");
    }
}

#[cfg(test)]
mod cyclic_path_phi_0657_tests {
    use crate::compile;

    #[test]
    fn cyclic_effects_and_forwarded_phi_keep_disjoint_sibling_accessible() {
        let src=include_str!("../examples/cyclic_effect_phi_0657.qr");
        let result=compile(src).expect("verified loop effects and PHI provenance");
        assert_eq!(result.angles,&[12.0,11.0]);
    }
    #[test]
    fn cyclic_wrapper_publishes_exact_verified_return_paths() {
        let source=include_str!("../examples/cyclic_effect_phi_0657.qr");
        let tokens=crate::syntax::lex(source).expect("valid typed program");
        let mut front=super::Front::new(tokens);
        front.parse_definitions().expect("all declarations parsed");
        let origins=front.validate_function_bodies()
            .expect("whole-body MIR and region proofs succeed");
        let relay=origins.get("relay")
            .expect("a cyclic, verified unit callee must not erase wrapper PHI origins");
        assert_eq!(relay.len(),2,"both returning fields must remain proven");
        assert!(relay.iter().all(|origin|origin.parameter==1));
        let fields=relay.iter().map(|origin|origin.path.first().map(|k|k.field.0))
            .collect::<Vec<_>>();
        assert!(fields.contains(&Some(0)) && fields.contains(&Some(1)));
    }
    #[test]
    fn cyclic_effects_false_phi_arm_preserves_sibling_move() {
        let source=include_str!("../examples/cyclic_effect_phi_0657.qr")
            .replace("relay(true, &mut t)","relay(false, &mut t)");
        let result=compile(&source).expect("false PHI arm must not lock c");
        assert_eq!(result.angles,&[12.0,11.0]);
    }
    #[test]
    fn cyclic_returned_phi_keeps_both_possible_referents_protected() {
        for field in ["a","b"] {
            let source=include_str!("../examples/cyclic_effect_phi_0657.qr")
                .replace("let spare: Blob = t.c;",&format!("let forbidden: Blob = t.{field};"));
            let error=compile(&source).expect_err("PHI cannot release a possible referent");
            assert!(error.message.contains("borrow"),"{error:?}");
        }
    }
}

#[cfg(test)]
mod interproc_alias_soundness_0658_tests {
    use crate::compile;
    #[test]
    fn unannotated_shared_if_uses_typed_let_for_local_bool_condition(){
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("let r = if true { &p.left } else { &p.left };",
                "let flag: bool = false; let r = if flag { &p.left } else { &p.left };");
        let compiled=compile(&src).expect("the entire shared if initializer must use the typed frontend");
        assert_eq!(compiled.angles,&[3.0]);
    }
    #[test]
    fn unannotated_if_initializer_rejects_mutable_branch_without_syntax_fallback(){
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("else { &p.left }", "else { &mut p.left }");
        let error=compile(&src).expect_err("cannot take &mut from immutable p");
        assert!(error.message.contains("cannot mutably borrow immutable binding"),"{error:?}");
    }
    #[test]
    fn mutable_if_initializer_must_not_mix_shared_and_exclusive_phi_origins(){
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("let p: Pair =", "let mut p: Pair =")
            .replace("else { &p.left }", "else { &mut p.left }");
        let error=compile(&src).expect_err("mixed reference kinds must fail closed");
        assert!(!error.message.contains("expected ';'"),"wrong parser used: {error:?}");
        assert!(error.message.contains("origin") || error.message.contains("borrow") ||
                error.message.contains("mismatch") || error.message.contains("type"),
                "unexpected failure rather than reference safety check: {error:?}");
    }
    #[test]
    fn unannotated_if_initializer_is_rejected_when_not_reference_valued(){
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("let r = if true { &p.left } else { &p.left };",
                "let r = if true { 1 } else { 2 };");
        let error=compile(&src).expect_err("the restricted reference-if path cannot certify value arms");
        assert!(error.message.contains("simple shared-borrow origins") ||
                error.message.contains("reference if initializer"),"{error:?}");
    }
    #[test]
    fn forwarding_a_unanimous_shared_phi_preserves_independent_field(){
        let result=compile(include_str!("../examples/alias_soundness_0658.qr"))
            .expect("all shared PHI candidates refer to exactly the same field");
        assert_eq!(result.angles,&[3.0]);
    }
    #[test]
    fn unanimous_shared_if_initializer_checks_both_boolean_choices(){
        for selected in ["true","false"] {
            let src=include_str!("../examples/alias_soundness_0658.qr")
                .replace("if true { &p.left } else { &p.left }",
                    &format!("if {selected} {{ &p.left }} else {{ &p.left }}"));
            assert!(compile(&src).is_ok(),"both exhaustive arms share one path");
        }
    }
    #[test]
    fn differing_if_initializer_sources_cannot_erase_phi_alternatives(){
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("else { &p.left }", "else { &p.right }")
            .replace("relay(r);\n    let spare: Blob = p.right;",
                "let spare: Blob = p.right;\n    relay(r);");
        let problem=compile(&src).expect_err("a possible PHI referent cannot move before its last use");
        assert!(problem.message.contains("borrow") || problem.message.contains("moved"),"{problem:?}");
    }
    #[test]
    fn incomplete_reference_if_initializer_fails_closed(){
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("else { &p.left }", "");
        assert!(compile(&src).is_err(),"missing else must never certify PHI");
    }
    #[test]
    fn shared_if_initializer_preserves_type_and_field_checks(){
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("let r = if", "let r: &i64 = if");
        assert!(compile(&src).is_err(),"incompatible reference annotation must be rejected");
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("&p.left", "&p.missing");
        assert!(compile(&src).is_err(),"nonexistent projected field must be rejected");
    }
    #[test]
    fn a_shared_phi_keeps_its_referent_borrowed_through_forwarding(){
        let src=include_str!("../examples/alias_soundness_0658.qr")
            .replace("let spare: Blob = p.right;", "let stolen: Blob = p.left;")
            .replace("rx(spare.n, q);", "rx(r.n, q); ry(stolen.n, q);");
        let problem=compile(&src).expect_err("shared PHI cannot permit a move of its referent");
        assert!(problem.message.contains("borrow"),"{problem:?}");
    }
    #[test]
    fn both_mutable_phi_return_candidates_block_moves_in_cyclic_wrapper(){
        let original=include_str!("../examples/cyclic_effect_phi_0657.qr");
        for field in ["a","b"] {
            let bad=original.replace("let spare: Blob = t.c;",
                &format!("let stolen: Blob = t.{field};"));
            assert!(compile(&bad).is_err(),"cannot move {field} through live PHI");
        }
    }
    #[test]
    fn a_cyclic_wrapper_leaves_disjoint_sibling_available_on_each_phi_arm(){
        let original=include_str!("../examples/cyclic_effect_phi_0657.qr");
        for flag in ["true","false"] {
            let src=original.replace("relay(true, &mut t)",
                &format!("relay({flag}, &mut t)"));
            assert!(compile(&src).is_ok(),"disjoint c is not a PHI candidate");
        }
    }
    #[test]
    fn partially_moved_aggregate_cannot_be_passed_as_whole_mutable_reference(){
        let original=include_str!("../examples/cyclic_effect_phi_0657.qr");
        let bad=original.replace("let r = relay(true, &mut t);",
            "let stolen: Blob = t.c; let r = relay(true, &mut t);");
        assert!(compile(&bad).is_err(),"cyclic callee requires a valid whole Tri");
    }
}

#[cfg(test)]
mod disjunctive_frontend_alias_0659_tests {
    use crate::compile;
    const SOURCE:&str=r#"
        struct Blob { n:i64 }
        struct Tri { a:Blob, b:Blob, c:Blob }
        fn inspect(x:&Blob) { let value:i64=x.n; }
        fn relay(x:&Blob) { inspect(x); }
        fn main() {
            let p:Tri=Tri{a:Blob{n:1},b:Blob{n:2},c:Blob{n:3}};
            let r=if true {&p.a} else {&p.b};
            let spare:Blob=p.c;
            relay(r);
            let q=qubit();rx(r.n,q);ry(spare.n,q);
        }
    "#;
    #[test]
    fn alternate_shared_sources_keep_unrelated_move_legal(){
        let result=compile(SOURCE).expect("both alternatives are type-checked");
        assert_eq!(result.angles,&[1.0,3.0]);
    }
    #[test]
    fn false_shared_branch_preserves_runtime_value(){
        let source=SOURCE.replace("if true {&p.a}","if false {&p.a}");
        assert_eq!(compile(&source).expect("false branch").angles,&[2.0,3.0]);
    }
    #[test]
    fn either_phi_referent_cannot_move_while_reference_live(){
        for field in ["a","b"] {
            let source=SOURCE.replace("let spare:Blob=p.c;",
                &format!("let bad:Blob=p.{field};"));
            let error=compile(&source).expect_err("every PHI origin is borrowed");
            assert!(error.message.contains("borrow") || error.message.contains("move"),"{error:?}");
        }
    }
    #[test]
    fn shared_and_exclusive_arms_cannot_be_joined(){
        let source=SOURCE.replace("let p:Tri=", "let mut p:Tri=")
            .replace("else {&p.b}","else {&mut p.b}");
        let error=compile(&source).expect_err("mixed kinds do not form shared PHI");
        assert!(error.message.contains("reference") || error.message.contains("borrow") ||
            error.message.contains("MIR"),"{error:?}");
    }
    #[test]
    fn inactive_uninitialized_field_cannot_be_a_phi_source(){
        let source=SOURCE.replace("let r=if true", "let taken:Blob=p.b;let r=if true");
        assert!(compile(&source).is_err(),"inactive moved origin must be rejected");
    }
    #[test]
    fn disjoint_owners_are_guarded_independently(){
        let source=r#"struct Blob{n:i64} fn inspect(x:&Blob){let n:i64=x.n;}
        fn main(){let left:Blob=Blob{n:1};let right:Blob=Blob{n:2};
          let r=if true {&left} else {&right};inspect(r);
          let q=qubit();rx(r.n,q);}"#;
        assert!(compile(source).is_ok(),"a shared root PHI can select the left owner");
        let false_branch=source.replace("if true {&left}","if false {&left}");
        assert!(compile(&false_branch).is_ok(),"a shared root PHI can select the right owner");
        for branch in [source,false_branch.as_str()] {
            for owner in ["left","right"] {
                let bad=branch.replace("inspect(r);",
                    &format!("let moved:Blob={owner};inspect(r);"));
                let error=compile(&bad).expect_err(
                    "both possible owners must remain borrowed until the PHI's last use");
                assert!(error.message.contains("borrow") || error.message.contains("move"),
                    "unexpected failure for {owner}: {error:?}");
            }
        }
    }
}

#[cfg(test)]
mod disjunctive_mutable_interproc_0659_tests {
    use crate::compile;
    #[test]
    fn returned_mutable_phi_can_be_passed_to_a_field_writer(){
        let src=include_str!("../examples/disjunctive_mutable_alias_0659.qr");
        let result=compile(src).expect("every exclusive provenance must be authorized");
        assert_eq!(result.angles,&[9.0,3.0]);
    }
    #[test]
    fn mutable_phi_false_return_origin_is_updated(){
        let src=include_str!("../examples/disjunctive_mutable_alias_0659.qr")
            .replace("choose(true,&mut t)","choose(false,&mut t)");
        let result=compile(&src).expect("both alternative mutable paths survive the call");
        assert_eq!(result.angles,&[9.0,3.0]);
    }
    #[test]
    fn mut_phi_write_cannot_suppress_possible_alias_conflict(){
        let src=include_str!("../examples/disjunctive_mutable_alias_0659.qr")
            .replace("set_n(r);", "let stolen:Blob=t.b;set_n(r);");
        let error=compile(&src).expect_err("b may be the returned exclusive loan");
        assert!(error.message.contains("borrow") || error.message.contains("move"),"{error:?}");
    }
}

#[cfg(test)]
mod disjunctive_0659_examples_tests {
    use crate::compile;
    #[test]
    fn shared_disjunctive_example_compiles(){
        let result=compile(include_str!("../examples/disjunctive_alias_0659.qr"))
            .expect("independent MovePath and both shared PHI origins");
        assert_eq!(result.angles,&[1.0,3.0]);
    }
    #[test]
    fn mutable_disjunctive_example_compiles(){
        let result=compile(include_str!("../examples/disjunctive_mutable_alias_0659.qr"))
            .expect("field-write effect is authorized by every exclusive PHI loan");
        assert_eq!(result.angles,&[9.0,3.0]);
    }
}


#[cfg(test)]
mod composed_phi_frontend_0660_tests {
    use super::*;
    const PREFIX:&str=r#"
        struct Blob { n:i64 }
        struct Tri { a:Blob, b:Blob, c:Blob }
        fn hop<'a>(x:&'a Blob)->&'a Blob { return x; }
        fn relay<'a>(x:&'a Blob)->&'a Blob { return hop(x); }
    "#;
    #[test]
    fn forwarded_shared_phi_both_choices_retain_independent_sibling(){
        for choice in ["true","false"] {
            let src=format!("{PREFIX} fn main(){{let t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};let r=if {choice}{{&t.a}}else{{&t.b}};let s=hop(r);let out=relay(s);let other:Blob=t.c;let q=qubit();rx(out.n,q);ry(other.n,q);}}");
            let program=compile(&src).expect("all PHI alternatives must keep field-level provenance");
            assert_eq!(program.angles,if choice=="true"{&[1.0,3.0][..]}else{&[2.0,3.0][..]});
        }
    }
    #[test]
    fn no_forwarded_phi_source_may_be_moved_while_result_is_live(){
        for field in ["a","b"] {
            let src=format!("{PREFIX} fn main(){{let t:Tri=Tri{{a:Blob{{n:1}},b:Blob{{n:2}},c:Blob{{n:3}}}};let r=if true{{&t.a}}else{{&t.b}};let s=hop(r);let out=relay(s);let bad:Blob=t.{field};let q=qubit();rx(out.n,q);}}");
            let error=compile(&src).expect_err("a live returned PHI must protect both owners");
            assert!(error.message.contains("borrow") || error.message.contains("move"),"{error:?}");
        }
    }
}
