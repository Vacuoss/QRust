//Recursive, type-checked patterns shared by the host frontend and Typed MIR
use std::collections::{HashMap,HashSet};
use crate::{syntax::{Token,TokenKind as K},ir::{ConstType,ConstValue,TypeId,FieldId},cfg_borrow::FieldKey};

const MAX_PATTERN_DEPTH:usize=16;
const MAX_PATTERN_BINDINGS:usize=64;

#[derive(Debug,Clone)]
pub enum Pattern<'a> {
    Wildcard,
    Boolean(bool),
    Binding {name:&'a str,token:usize,by_ref:Option<bool>},
    Enum {owner:&'a str,variant:&'a str,fields:Vec<Pattern<'a>>},
    Struct {owner:&'a str,fields:Vec<(&'a str,Pattern<'a>)>},
}

//Only explicit syntax is admitted: unknown forms return None and cannot receive a MIR ownership
//certificate. Recursion and arity are bounded
pub fn parse<'a>(tokens:&[Token<'a>],start:usize,limit:usize)
    ->Option<(Pattern<'a>,usize)> {
    parse_at(tokens,start,limit,0)
}
fn parse_at<'a>(tokens:&[Token<'a>],i:usize,limit:usize,depth:usize)
    ->Option<(Pattern<'a>,usize)> {
    if depth>MAX_PATTERN_DEPTH||i>=limit{return None;}
    let kind=tokens.get(i)?.kind;
    match kind {
        K::Ident("_")=>Some((Pattern::Wildcard,i+1)),
        K::Ident("true")=>Some((Pattern::Boolean(true),i+1)),
        K::Ident("false")=>Some((Pattern::Boolean(false),i+1)),
        K::Ident("ref")=>{
            let mutable=tokens.get(i+1).is_some_and(|t|t.kind==K::Ident("mut"));
            let j=i+1+usize::from(mutable);
            let K::Ident(name)=tokens.get(j)?.kind else{return None;};
            if name=="_"||name=="ref"||name=="mut" {return None;}
            Some((Pattern::Binding{name,token:j,by_ref:Some(mutable)},j+1))
        },
        K::Ident(owner)=>{
            if tokens.get(i+1).is_some_and(|t|t.kind==K::Colon) &&
                tokens.get(i+2).is_some_and(|t|t.kind==K::Colon) {
                let K::Ident(variant)=tokens.get(i+3)?.kind else{return None;};
                let mut next=i+4;
                let mut fields=Vec::new();
                if tokens.get(next).is_some_and(|t|t.kind==K::LParen) {
                    next+=1;
                    while !tokens.get(next).is_some_and(|t|t.kind==K::RParen) {
                        if fields.len()>=8 {return None;}
                        let (field,at)=parse_at(tokens,next,limit,depth+1)?;
                        fields.push(field);next=at;
                        if tokens.get(next).is_some_and(|t|t.kind==K::RParen){break;}
                        if tokens.get(next)?.kind!=K::Comma{return None;}
                        next+=1;
                        if tokens.get(next).is_some_and(|t|t.kind==K::RParen){break;}
                    }
                    if tokens.get(next)?.kind!=K::RParen{return None;}
                    next+=1;
                }
                Some((Pattern::Enum{owner,variant,fields},next))
            }else if tokens.get(i+1).is_some_and(|t|t.kind==K::LBrace){
                let mut next=i+2;
                let mut fields=Vec::new();
                while !tokens.get(next).is_some_and(|t|t.kind==K::RBrace) {
                    if fields.len()>=32{return None;}
                    let K::Ident(name)=tokens.get(next)?.kind else{return None;};
                    if tokens.get(next+1)?.kind!=K::Colon{return None;}
                    let (value,at)=parse_at(tokens,next+2,limit,depth+1)?;
                    fields.push((name,value));next=at;
                    if tokens.get(next).is_some_and(|t|t.kind==K::RBrace){break;}
                    if tokens.get(next)?.kind!=K::Comma{return None;}
                    next+=1;
                    if tokens.get(next).is_some_and(|t|t.kind==K::RBrace){break;}
                }
                if tokens.get(next)?.kind!=K::RBrace{return None;}
                Some((Pattern::Struct{owner,fields},next+1))
            }else {
                if owner=="mut" || owner=="ref"{return None;}
                Some((Pattern::Binding{name:owner,token:i,by_ref:None},i+1))
            }
        },
        _=>None,
    }
}

pub struct Schema<'a> {
    pub enums:&'a HashMap<String,Vec<String>>,
    pub payloads:&'a HashMap<String,Vec<Vec<ConstType>>>,
    pub structs:&'a HashMap<String,Vec<(String,ConstType)>>,
    pub type_ids:&'a HashMap<String,TypeId>,
}
#[derive(Debug,Clone)]
pub struct Binding<'a> {
    pub name:&'a str,
    pub token:usize,
    pub ty:ConstType,
    pub path:Vec<FieldKey>,
    pub by_ref:Option<bool>,
}
#[derive(Debug)]
pub struct Checked<'a> {
    pub variant:Option<usize>,
    pub covers_variant:bool,
    pub bindings:Vec<Binding<'a>>,
}
fn type_id(schema:&Schema<'_>,ty:&ConstType)->Option<TypeId>{
    match ty {ConstType::Named(n)=>schema.type_ids.get(n).copied(),
        ConstType::Resolved(id)=>Some(*id),_=>None}
}
fn check_inner<'a>(pattern:&Pattern<'a>,ty:&ConstType,path:&mut Vec<FieldKey>,
    borrowed:Option<bool>,schema:&Schema<'_>,names:&mut HashSet<&'a str>,
    bindings:&mut Vec<Binding<'a>>,depth:usize)->Result<bool,&'static str>{
    if depth>MAX_PATTERN_DEPTH{return Err("pattern nesting limit exceeded");}
    match pattern {
        Pattern::Wildcard=>Ok(true),
        Pattern::Boolean(_)=>if *ty==ConstType::Bool {Ok(false)}
            else{Err("bool pattern on non-bool payload")},
        Pattern::Binding{name,token,by_ref}=>{
            if borrowed.is_some() && by_ref.is_none(){
                return Err("by-value binding from borrowed match is not supported");
            }
            if by_ref==&Some(true) && borrowed==Some(false){
                return Err("ref mut requires an exclusive or mutable enum owner");
            }
            if !names.insert(*name) {return Err("duplicate nested pattern binding");}
            if bindings.len()>=MAX_PATTERN_BINDINGS{return Err("too many pattern bindings");}
            bindings.push(Binding{name:*name,token:*token,ty:ty.clone(),path:path.clone(),by_ref:*by_ref});
            Ok(true)
        },
        Pattern::Enum{owner,variant,fields}=>{
            let id=schema.type_ids.get(*owner).copied().ok_or("unknown enum pattern type")?;
            if type_id(schema,ty)!=Some(id){
                return Err(if depth==0 {
                    "enum match arm uses a variant of another enum type"
                }else{
                    "nested enum pattern type mismatch"
                });
            }
            let variants=schema.enums.get(*owner).ok_or("pattern type is not enum")?;
            let index=variants.iter().position(|name|name.as_str()==*variant)
                .ok_or("unknown nested enum variant")?;
            let payloads=schema.payloads.get(*owner).and_then(|v|v.get(index))
                .ok_or("missing nested enum payload schema")?;
            if index>=128||payloads.len()>8 {return Err("enum projection encoding limit exceeded");}
            if payloads.len()!=fields.len(){return Err("nested enum pattern arity mismatch");}
            let mut total=true;
            for (field_index,(part,part_ty)) in fields.iter().zip(payloads).enumerate(){
                path.push(FieldKey{aggregate:id,field:FieldId(0x8000_0000 |
                    ((index as u32)<<4) | field_index as u32)});
                let result=check_inner(part,part_ty,path,borrowed,schema,names,bindings,depth+1)?;
                total &= result;
                path.pop();
            }
            Ok(total && (depth==0 || variants.len()==1))
        },
        Pattern::Struct{owner,fields}=>{
            let id=schema.type_ids.get(*owner).copied().ok_or("unknown struct pattern type")?;
            if type_id(schema,ty)!=Some(id){return Err("nested struct pattern type mismatch");}
            let declared=schema.structs.get(*owner).ok_or("pattern type is not struct")?;
            if declared.len()!=fields.len(){return Err("struct pattern must list every field");}
            let mut seen=HashSet::new();let mut total=true;
            for (field_name,part) in fields {
                let index=declared.iter().position(|(n,_)|n.as_str()==*field_name)
                    .ok_or("unknown struct pattern field")?;
                if !seen.insert(index){return Err("duplicate struct pattern field");}
                path.push(FieldKey{aggregate:id,field:FieldId(index as u32)});
                total &= check_inner(part,&declared[index].1,path,borrowed,schema,names,bindings,depth+1)?;
                path.pop();
            }
            Ok(total)
        },
    }
}
pub fn check<'a>(pattern:&Pattern<'a>,root:&ConstType,borrowed:Option<bool>,
    schema:&Schema<'_>)->Result<Checked<'a>,&'static str>{
    let mut path=Vec::new();let mut names=HashSet::new();let mut bindings=Vec::new();
    let total=check_inner(pattern,root,&mut path,borrowed,schema,&mut names,&mut bindings,0)?;
    let variant=if let Pattern::Enum{owner,variant,..}=pattern {
        Some(schema.enums.get(*owner).and_then(|v|v.iter().position(|n|n.as_str()==*variant))
            .ok_or("unknown enum variant")?)
    }else{None};
    if !matches!(pattern,Pattern::Enum{..}|Pattern::Wildcard) {
        return Err("enum match requires a variant or wildcard arm");
    }
    Ok(Checked{variant,covers_variant:total,bindings})
}

pub fn matches_value(pattern:&Pattern<'_>,value:&ConstValue,schema:&Schema<'_>)->bool {
    match pattern {
        Pattern::Wildcard|Pattern::Binding{..}=>true,
        Pattern::Boolean(b)=>matches!(value,ConstValue::Bool(v) if b==v),
        Pattern::Enum{owner,variant,fields}=>{
            let Some(id)=schema.type_ids.get(*owner)else{return false;};
            let Some(variants)=schema.enums.get(*owner)else{return false;};
            let Some(index)=variants.iter().position(|name|name.as_str()==*variant)else{return false;};
            let actual=match value {
                ConstValue::Enum(actual,v) if actual==id && v.0 as usize==index=>fields.is_empty(),
                ConstValue::EnumData(actual,v,data) if actual==id && v.0 as usize==index && data.len()==fields.len()=>
                    fields.iter().zip(data).all(|(pattern,value)|matches_value(pattern,value,schema)),
                _=>false,
            };
            actual
        },
        Pattern::Struct{owner,fields}=>{
            let Some(id)=schema.type_ids.get(*owner)else{return false;};
            let ConstValue::Struct(actual,data)=value else{return false;};
            if id!=actual{return false;}
            let Some(declared)=schema.structs.get(*owner)else{return false;};
            fields.iter().all(|(field,pattern)|declared.iter()
                .position(|(name,_)|name.as_str()==*field).and_then(|i|data.get(i))
                .is_some_and(|v|matches_value(pattern,v,schema)))
        },
    }
}

pub fn collect_bindings<'a>(pattern:&Pattern<'a>,out:&mut Vec<(usize,&'a str,bool,bool)>) {
    match pattern {
        Pattern::Binding{name,token,by_ref}=>out.push((*token,*name,by_ref.is_some(),by_ref==&Some(true))),
        Pattern::Enum{fields,..}=>for field in fields {collect_bindings(field,out);},
        Pattern::Struct{fields,..}=>for (_,part) in fields {collect_bindings(part,out);},
        _=>(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn recursively_parses_and_types_nested_enum_struct_paths(){
        let src="Outer::Wrap(Inner::Pair(P { n: value }, _))";
        let tokens=crate::syntax::lex(src).unwrap();
        let (pattern,end)=parse(&tokens,0,tokens.len()).unwrap();
        assert_eq!(end,tokens.len());
        let ids=HashMap::from([("Outer".to_owned(),TypeId(0)),
            ("Inner".to_owned(),TypeId(1)),("P".to_owned(),TypeId(2))]);
        let enums=HashMap::from([("Outer".to_owned(),vec!["Wrap".to_owned()]),
            ("Inner".to_owned(),vec!["Pair".to_owned()])]);
        let payloads=HashMap::from([("Outer".to_owned(),vec![vec![ConstType::Resolved(TypeId(1))]]),
            ("Inner".to_owned(),vec![vec![ConstType::Resolved(TypeId(2)),ConstType::I64]])]);
        let structs=HashMap::from([("P".to_owned(),vec![("n".to_owned(),ConstType::I64)])]);
        let schema=Schema{enums:&enums,payloads:&payloads,structs:&structs,type_ids:&ids};
        let checked=check(&pattern,&ConstType::Resolved(TypeId(0)),None,&schema).unwrap();
        assert_eq!(checked.bindings.len(),1);
        assert_eq!(checked.bindings[0].path.len(),3);
        assert!(checked.covers_variant);
        let value=ConstValue::EnumData(TypeId(0),crate::ir::VariantId(0),vec![
            ConstValue::EnumData(TypeId(1),crate::ir::VariantId(0),vec![
                ConstValue::Struct(TypeId(2),vec![ConstValue::I64(7)]),ConstValue::I64(2)])]);
        assert!(matches_value(&pattern,&value,&schema));
    }
    #[test]
    fn nested_multi_variant_discriminant_still_needs_fallback(){
        let tokens=crate::syntax::lex("Outer::Wrap(Inner::Pair(value))").unwrap();
        let (pattern,_)=parse(&tokens,0,tokens.len()).unwrap();
        let ids=HashMap::from([("Outer".into(),TypeId(0)),("Inner".into(),TypeId(1))]);
        let enums=HashMap::from([("Outer".into(),vec!["Wrap".into()]),
            ("Inner".into(),vec!["Pair".into(),"Empty".into()])]);
        let payloads=HashMap::from([("Outer".into(),vec![vec![ConstType::Resolved(TypeId(1))]]),
            ("Inner".into(),vec![vec![ConstType::I64],vec![]])]);
        let structs=HashMap::new();
        let schema=Schema{enums:&enums,payloads:&payloads,structs:&structs,type_ids:&ids};
        assert!(!check(&pattern,&ConstType::Resolved(TypeId(0)),None,&schema)
            .unwrap().covers_variant);
    }
    #[test]
    fn nested_single_variant_with_boolean_literal_is_not_exhaustive(){
        let tokens=crate::syntax::lex("Outer::Wrap(Inner::Pair(true))").unwrap();
        let (pattern,_)=parse(&tokens,0,tokens.len()).unwrap();
        let ids=HashMap::from([("Outer".into(),TypeId(0)),("Inner".into(),TypeId(1))]);
        let enums=HashMap::from([("Outer".into(),vec!["Wrap".into()]),
            ("Inner".into(),vec!["Pair".into()])]);
        let payloads=HashMap::from([("Outer".into(),vec![vec![ConstType::Resolved(TypeId(1))]]),
            ("Inner".into(),vec![vec![ConstType::Bool]])]);
        let structs=HashMap::new();
        let schema=Schema{enums:&enums,payloads:&payloads,structs:&structs,type_ids:&ids};
        assert!(!check(&pattern,&ConstType::Resolved(TypeId(0)),None,&schema)
            .unwrap().covers_variant);
    }
    #[test]
    fn wrong_nested_type_and_duplicate_binders_fail(){
        let tokens=crate::syntax::lex("Outer::Wrap(Inner::Pair(a,a))").unwrap();
        let (pattern,_)=parse(&tokens,0,tokens.len()).unwrap();
        let ids=HashMap::from([("Outer".into(),TypeId(0)),("Inner".into(),TypeId(1))]);
        let enums=HashMap::from([("Outer".into(),vec!["Wrap".into()]),
            ("Inner".into(),vec!["Pair".into()])]);
        let payloads=HashMap::from([("Outer".into(),vec![vec![ConstType::Resolved(TypeId(1))]]),
            ("Inner".into(),vec![vec![ConstType::I64,ConstType::I64]])]);
        let structs=HashMap::new();
        let schema=Schema{enums:&enums,payloads:&payloads,structs:&structs,type_ids:&ids};
        assert!(check(&pattern,&ConstType::Resolved(TypeId(0)),None,&schema).is_err());
    }
}

#[cfg(test)]
mod root_enum_diagnostics_0644_fix1_tests {
    use super::*;

    #[test]
    fn mismatched_root_enum_reports_another_enum_without_relaxing_type_ids() {
        let tokens=crate::syntax::lex("B::X").unwrap();
        let (pattern,end)=parse(&tokens,0,tokens.len()).unwrap();
        assert_eq!(end,tokens.len());
        let ids=HashMap::from([("A".to_owned(),TypeId(1)),
            ("B".to_owned(),TypeId(2))]);
        let enums=HashMap::from([("A".to_owned(),vec!["X".to_owned()]),
            ("B".to_owned(),vec!["X".to_owned()])]);
        let payloads=HashMap::from([("A".to_owned(),vec![vec![]]),
            ("B".to_owned(),vec![vec![]])]);
        let structs=HashMap::new();
        let schema=Schema{enums:&enums,payloads:&payloads,
            structs:&structs,type_ids:&ids};
        let error=check(&pattern,&ConstType::Resolved(TypeId(1)),None,&schema)
            .unwrap_err();
        assert!(error.contains("another enum"));
        assert!(check(&pattern,&ConstType::Resolved(TypeId(2)),None,&schema).is_ok());
    }
}

#[cfg(test)]
mod mixed_mode_schema_0646_tests {
    use super::*;

    #[test]
    fn owned_pattern_uses_independent_binding_modes() {
        let input=crate::syntax::lex("E::Pair(first,ref second,ref mut count)").unwrap();
        let (pattern,end)=parse(&input,0,input.len()).unwrap();
        assert_eq!(end,input.len());
        let ids=HashMap::from([("E".into(),TypeId(1))]);
        let enums=HashMap::from([("E".into(),vec!["Pair".into()])]);
        let payloads=HashMap::from([("E".into(),vec![vec![
            ConstType::I64,ConstType::I64,ConstType::I64]])]);
        let structs=HashMap::new();
        let schema=Schema{enums:&enums,payloads:&payloads,structs:&structs,type_ids:&ids};
        let checked=check(&pattern,&ConstType::Resolved(TypeId(1)),None,&schema).unwrap();
        assert_eq!(checked.bindings.iter().map(|b|b.by_ref).collect::<Vec<_>>(),
            vec![None,Some(false),Some(true)]);
        assert_ne!(checked.bindings[0].path,checked.bindings[1].path);
        assert!(check(&pattern,&ConstType::Resolved(TypeId(1)),Some(false),&schema).is_err());
    }
}
