//Universal lifetime regions for the QRust 0.6 Rust-compatible host frontend
use std::collections::{HashMap,VecDeque};

#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RegionId(pub u32);

#[derive(Clone, Debug)]
pub struct RegionSignature {
    pub param: Vec<Option<RegionId>>,
    pub result: Option<RegionId>,
    //One bit per universal region: outlives[a] contains b iff a: b Maximum 32 named lifetimes + 'static
    //means one u64 per row
    outlives: Vec<u64>,
    static_region: RegionId,
}

impl RegionSignature {
    pub fn new(declared: &[String], param: &[Option<String>], result: Option<String>,
               bounds: &[(String, String)]) -> Result<Self, String> {
        if declared.len() > 32 { return Err("maximum 32 lifetime parameters".into()); }
        let mut ids = HashMap::with_capacity(declared.len()+1);
        for (index, name) in declared.iter().enumerate() {
            if name == "static" || name == "_" { return Err("'static and '_ cannot be lifetime parameters".into()); }
            if ids.insert(name.as_str(), RegionId(index as u32)).is_some() {
                return Err(format!("duplicate lifetime parameter '{name}"));
            }
        }
        ids.insert("static", RegionId(declared.len() as u32));
        let resolve = |name: &str| -> Result<RegionId, String> {
            ids.get(name).copied().ok_or_else(||format!("undeclared lifetime '{name}"))
        };
        let param = param.iter().map(|name|name.as_deref().map(&resolve).transpose())
            .collect::<Result<Vec<_>,_>>()?;
        let result = result.as_deref().map(&resolve).transpose()?;
        let size = declared.len()+1;
        let mut outlives = vec![0u64;size];
        for i in 0..size {
            outlives[i] |= 1u64 << i;
            outlives[size-1] |= 1u64 << i;
        }
        for (longer,shorter) in bounds {
            let a = resolve(longer)?.0 as usize;
            let b = resolve(shorter)?.0 as usize;
            outlives[a] |= 1u64 << b;
        }
        //Warshall closure over bit rows. The reachable set of k can be absorbed into any region already known
        //to outlive k
        for k in 0..size {
            let reachable = outlives[k];
            let via = 1u64 << k;
            for row in &mut outlives {
                if *row & via != 0 { *row |= reachable; }
            }
        }
        Ok(Self {param,result,outlives,static_region:RegionId((size-1) as u32)})
    }
    pub fn static_parameter(&self,i:usize)->bool{
        self.param.get(i).copied().flatten()==Some(self.static_region)
    }
    pub fn static_return(&self)->bool {self.result==Some(self.static_region)}
    pub fn permits(&self,source:RegionId,required:RegionId)->bool {
        if required.0 >= 64 {return false;}
        self.outlives.get(source.0 as usize)
            .is_some_and(|row|row & (1u64 << required.0) != 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn strvec(v:&[&str])->Vec<String>{v.iter().map(|s|s.to_string()).collect()}
    #[test] fn named_outlives_closure_is_transitive() {
        let p=RegionSignature::new(&strvec(&["a","b","c"]),&[],None,
            &[("a".into(),"b".into()),("b".into(),"c".into())]).unwrap();
        assert!(p.permits(RegionId(0),RegionId(2)));
        assert!(!p.permits(RegionId(2),RegionId(0)));
        assert!(p.permits(RegionId(3),RegionId(0)));
    }
    #[test] fn bitset_maximum_lifetimes_and_transitive_bounds() {
        let names=(0..32).map(|i|format!("r{i}")).collect::<Vec<_>>();
        let constraints=(0..31).map(|i|(format!("r{i}"),format!("r{}",i+1)))
            .collect::<Vec<_>>();
        let sig=RegionSignature::new(&names,&[],Some("r31".into()),&constraints).unwrap();
        assert!(sig.permits(RegionId(0),RegionId(31)));
        assert!(sig.permits(RegionId(32),RegionId(0))); //'static
        assert!(!sig.permits(RegionId(31),RegionId(0)));
        assert!(!sig.permits(RegionId(33),RegionId(0)));
        assert!(!sig.permits(RegionId(0),RegionId(65)));
    }
    #[test] fn universal_cycles_and_static_are_conservative() {
        let names=strvec(&["a","b","c"]);
        let sig=RegionSignature::new(&names,&[],None,&[
            ("a".into(),"b".into()),("b".into(),"a".into()),
            ("b".into(),"c".into())]).unwrap();
        assert!(sig.permits(RegionId(0),RegionId(2)));
        assert!(sig.permits(RegionId(1),RegionId(0)));
        assert!(!sig.permits(RegionId(2),RegionId(1)));
        assert!(!sig.permits(RegionId(0),RegionId(3))); //only 'static outlives 'static
    }
    #[test] fn undeclared_and_duplicate_lifetimes_are_rejected() {
        assert!(RegionSignature::new(&strvec(&["a","a"]),&[],None,&[]).is_err());
        assert!(RegionSignature::new(&strvec(&["a"]),&[],Some("b".into()),&[]).is_err());
        assert!(RegionSignature::new(&strvec(&["static"]),&[],None,&[]).is_err());
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ProvenanceVar(pub u32);

#[derive(Default, Debug)]
pub struct ProvenanceVariables {
    origins: Vec<u64>,
    edges: Vec<(ProvenanceVar, ProvenanceVar)>,
}
impl ProvenanceVariables {
    pub fn new() -> Self { Self::default() }
    pub fn fresh(&mut self) -> Result<ProvenanceVar,String> {
        if self.origins.len() >= 1024 { return Err("provenance variable limit exceeded".into()); }
        let id=ProvenanceVar(self.origins.len() as u32);
        self.origins.push(0);
        Ok(id)
    }
    pub fn parameter(&mut self,index:usize) -> Result<ProvenanceVar,String> {
        if index>=64 { return Err("provenance parameter limit exceeded".into()); }
        let id=self.fresh()?;
        self.origins[id.0 as usize]=1u64 << index;
        Ok(id)
    }
    pub fn flows_into(&mut self,source:ProvenanceVar,dest:ProvenanceVar)->Result<(),String>{
        if source.0 as usize>=self.origins.len() || dest.0 as usize>=self.origins.len(){
            return Err("unknown provenance variable".into());
        }
        if self.edges.len()>=32768 {return Err("provenance constraint limit exceeded".into());}
        self.edges.push((source,dest));
        Ok(())
    }
    pub fn solve(&mut self)->Result<(),String>{
        if self.edges.is_empty(){return Ok(());}
        if self.edges.len()<=8 {
            let limit=self.origins.len().saturating_mul(64).saturating_add(1);
            for _ in 0..limit {
                let mut changed=false;
                for &(src,dst) in &self.edges {
                    let mask=self.origins[src.0 as usize];
                    let target=&mut self.origins[dst.0 as usize];
                    let merged=*target|mask;
                    if merged!=*target {*target=merged;changed=true;}
                }
                if !changed{return Ok(());}
            }
            return Err("provenance fixed point did not converge".into());
        }
        let mut successors=vec![Vec::<usize>::new();self.origins.len()];
        for &(source,destination) in &self.edges {
            let (from,to)=(source.0 as usize,destination.0 as usize);
            if from>=successors.len() || to>=successors.len(){
                return Err("unknown provenance variable".into());
            }
            successors[from].push(to);
        }
        let mut queue=VecDeque::new();
        let mut queued=vec![false;self.origins.len()];
        for (i,&mask) in self.origins.iter().enumerate(){
            if mask!=0 {queue.push_back(i);queued[i]=true;}
        }
        while let Some(source)=queue.pop_front(){
            queued[source]=false;
            let mask=self.origins[source];
            for &dest in &successors[source] {
                let merged=self.origins[dest]|mask;
                if merged!=self.origins[dest] {
                    self.origins[dest]=merged;
                    if !queued[dest]{queue.push_back(dest);queued[dest]=true;}
                }
            }
        }
        Ok(())
    }
    pub fn instantiate_call_sources(&mut self,callee_origins:u64,
        actual_origins:&[u64])->Result<ProvenanceVar,String>{
        if actual_origins.len()>64 || callee_origins==0 {
            return Err("call has no valid reference provenance summary".into());
        }
        if actual_origins.len()<64 && callee_origins >> actual_origins.len()!=0 {
            return Err("callee provenance source is missing at call site".into());
        }
        let mut sources=callee_origins;
        let mut combined=0u64;
        while sources!=0 {
            let formal=sources.trailing_zeros() as usize;
            sources&=sources-1;
            let actual=*actual_origins.get(formal)
                .ok_or("callee provenance index exceeds actual arguments")?;
            if actual==0 {
                return Err("callee reference provenance has no actual source".into());
            }
            combined|=actual;
        }
        let result=self.fresh()?;
        while combined!=0 {
            let bit=combined.trailing_zeros() as usize;
            combined&=combined-1;
            let input=self.parameter(bit)?;
            self.flows_into(input,result)?;
        }
        Ok(result)
    }
    #[cfg(test)]
    pub fn instantiate_call(&mut self,callee_origins:u64,
        actual_parameters:&[usize])->Result<ProvenanceVar,String>{
        if actual_parameters.len()>64 {
            return Err("provenance argument limit exceeded".into());
        }
        let mut masks=[0u64;64];
        for (slot,&source) in masks.iter_mut().zip(actual_parameters.iter()) {
            if source>=64{return Err("provenance parameter limit exceeded".into());}
            *slot=1u64<<source;
        }
        self.instantiate_call_sources(callee_origins,&masks[..actual_parameters.len()])
    }
    pub fn origins(&self,id:ProvenanceVar)->Option<u64>{
        self.origins.get(id.0 as usize).copied()
    }
    pub fn verify_return(&self,id:ProvenanceVar,signature:&RegionSignature)->Result<(),String>{
        let mut mask=self.origins(id).ok_or("unknown provenance variable")?;
        if mask==0 {return Err("returned reference has no proven input origin".into());}
        let required=signature.result.ok_or("missing returned lifetime")?;
        while mask!=0 {
            let index=mask.trailing_zeros() as usize;
            mask &= mask-1;
            let input=signature.param.get(index).and_then(|region|*region)
                .ok_or("returned reference source is not a lifetime-bearing parameter")?;
            if !signature.permits(input,required) {
                return Err("returned reference lifetime does not outlive declared return region".into());
            }
        }
        Ok(())
    }
}

pub struct RegionConstraintSolver<'a> {
    signature:&'a RegionSignature,
    sources:ProvenanceVariables,
    locals:LocalRegionInference,
}
impl<'a> RegionConstraintSolver<'a> {
    pub fn new(signature:&'a RegionSignature)->Self {
        Self{signature,sources:ProvenanceVariables::new(),
            locals:LocalRegionInference::default()}
    }
    pub fn instantiate_call_sources(&mut self,summary:u64,actual:&[u64])
        ->Result<ProvenanceVar,String>{
        self.sources.instantiate_call_sources(summary,actual)
    }
    #[cfg(test)]
    pub fn local_regions_mut(&mut self)->&mut LocalRegionInference{&mut self.locals}
    pub fn solve_and_verify_return(&mut self,result:ProvenanceVar)->Result<(),String>{
        self.locals.solve()?;
        self.sources.solve()?;
        self.sources.verify_return(result,self.signature)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoanKind { Shared, Exclusive }

#[derive(Clone, Debug, Default)]
pub struct LocalRegionInference {
    regions: Vec<crate::cfg_nll::LocalRegion>,
    kinds: Vec<LoanKind>,
    outlives: Vec<(RegionId, RegionId)>,
}
impl LocalRegionInference {
    #[cfg(test)]
    pub fn add(&mut self, region: crate::cfg_nll::LocalRegion)->RegionId {
        self.add_loan(region,LoanKind::Shared)
    }
    pub fn add_loan(&mut self, region:crate::cfg_nll::LocalRegion,kind:LoanKind)->RegionId{
        let id=RegionId(self.regions.len() as u32);
        self.regions.push(region);
        self.kinds.push(kind);
        id
    }
    pub fn refine_place(&mut self,id:RegionId,owner:crate::ids::SymbolId,
        place:crate::ir::Place)->bool {
        let Some(region)=self.regions.get_mut(id.0 as usize) else{return false;};
        region.owner=owner;region.place=place;true
    }
    pub fn live_at(&self,id:RegionId,point:crate::cfg_nll::CfgPointId)->Option<bool>{
        Some(self.regions.get(id.0 as usize)?.points.contains(&point))
    }
    #[cfg(test)]
    pub fn loans_conflict_at(&self,a:RegionId,b:RegionId,point:crate::cfg_nll::CfgPointId)->Option<bool>{
        if a==b{return Some(false);}
        let x=self.regions.get(a.0 as usize)?;
        let y=self.regions.get(b.0 as usize)?;
        let ka=*self.kinds.get(a.0 as usize)?;
        let kb=*self.kinds.get(b.0 as usize)?;
        Some((ka==LoanKind::Exclusive||kb==LoanKind::Exclusive) &&
            x.owner==y.owner && x.place.overlaps(y.place) &&
            x.points.contains(&point) && y.points.contains(&point))
    }
    pub fn require_outlives(&mut self,long:RegionId,short:RegionId){
        self.outlives.push((long,short));
    }
    pub fn solve(&mut self)->Result<(),String>{
        let mut changes=true;
        let mut steps=0usize;
        while changes {
            changes=false;
            steps+=1;
            if steps>self.regions.len()+1{return Err("region fixed point did not converge".into());}
            for &(long,short) in &self.outlives {
                let a=long.0 as usize;let b=short.0 as usize;
                if a>=self.regions.len()||b>=self.regions.len(){return Err("unknown local region".into());}
                if a==b {continue;}
                let (dest,src)=if a<b {
                    let (left,right)=self.regions.split_at_mut(b);
                    (&mut left[a].points,&right[0].points)
                } else {
                    let (left,right)=self.regions.split_at_mut(a);
                    (&mut right[0].points,&left[b].points)
                };
                for &point in src {changes |= dest.insert(point);}
            }
        }
        Ok(())
    }
    #[allow(dead_code)]
    pub fn overlaps(&self,a:RegionId,b:RegionId)->Option<bool>{
        Some(self.regions.get(a.0 as usize)?.overlaps(self.regions.get(b.0 as usize)?))
    }
    #[allow(dead_code)]
    pub fn get(&self,id:RegionId)->Option<&crate::cfg_nll::LocalRegion>{
        self.regions.get(id.0 as usize)
    }
}

#[cfg(test)]
mod local_region_tests {
    use super::*;
    use crate::{cfg_nll::{CfgPointId,LocalRegion},ids::SymbolId,ir::{Place,FieldId}};
    use std::collections::HashSet;
    fn region(id:u32,owner:u32,place:Place,points:&[u32])->LocalRegion{
        LocalRegion{binding:SymbolId(id),owner:SymbolId(owner),place,
            points:points.iter().map(|&p|CfgPointId(p)).collect::<HashSet<_>>()}
    }
    #[test]fn unrelated_places_or_disjoint_cfg_points_do_not_intersect(){
        let mut engine=LocalRegionInference::default();
        let a=engine.add(region(1,5,Place::Field(FieldId(0)),&[1,2]));
        let b=engine.add(region(2,5,Place::Field(FieldId(1)),&[2,3]));
        let c=engine.add(region(3,5,Place::Root,&[4,5]));
        assert_eq!(engine.overlaps(a,b),Some(false));
        assert_eq!(engine.overlaps(a,c),Some(false));
    }
    #[test]fn outlives_constraints_reach_fixed_point_and_detect_overlap(){
        let mut engine=LocalRegionInference::default();
        let long=engine.add(region(1,5,Place::Root,&[1]));
        let middle=engine.add(region(2,5,Place::Root,&[2]));
        let short=engine.add(region(3,5,Place::Root,&[3]));
        engine.require_outlives(long,middle);
        engine.require_outlives(middle,short);
        engine.solve().unwrap();
        assert!(engine.get(long).unwrap().points.contains(&CfgPointId(3)));
        assert_eq!(engine.overlaps(long,short),Some(true));
    }
}

#[cfg(test)]
mod point_loan_tests_062 {
    use super::*;
    use crate::{cfg_nll::{CfgPointId, LocalRegion},ids::SymbolId,ir::{FieldId,Place}};
    use std::collections::HashSet;
    fn loan(binding:u32,owner:u32,place:Place,points:&[u32])->LocalRegion {
        LocalRegion{binding:SymbolId(binding),owner:SymbolId(owner),place,
            points:points.iter().copied().map(CfgPointId).collect::<HashSet<_>>()}
    }
    #[test]
    fn shared_loans_can_coexist_at_the_same_point() {
        let mut regions=LocalRegionInference::default();
        let a=regions.add_loan(loan(1,8,Place::Root,&[2,3]),LoanKind::Shared);
        let b=regions.add_loan(loan(2,8,Place::Root,&[3]),LoanKind::Shared);
        assert_eq!(regions.loans_conflict_at(a,b,CfgPointId(3)),Some(false));
    }
    #[test]
    fn mutable_loan_conflicts_only_when_place_and_cfg_point_overlap() {
        let mut regions=LocalRegionInference::default();
        let a=regions.add_loan(loan(1,8,Place::Root,&[1,2]),LoanKind::Exclusive);
        let b=regions.add_loan(loan(2,8,Place::Root,&[2,3]),LoanKind::Shared);
        assert_eq!(regions.loans_conflict_at(a,b,CfgPointId(1)),Some(false));
        assert_eq!(regions.loans_conflict_at(a,b,CfgPointId(2)),Some(true));
        assert_eq!(regions.loans_conflict_at(a,b,CfgPointId(3)),Some(false));
    }
    #[test]
    fn disjoint_fields_and_distinct_symbol_owners_are_independent() {
        let mut regions=LocalRegionInference::default();
        let a=regions.add_loan(loan(1,8,Place::Field(FieldId(0)),&[2]),LoanKind::Exclusive);
        let b=regions.add_loan(loan(2,8,Place::Field(FieldId(1)),&[2]),LoanKind::Exclusive);
        let c=regions.add_loan(loan(3,9,Place::Root,&[2]),LoanKind::Exclusive);
        assert_eq!(regions.loans_conflict_at(a,b,CfgPointId(2)),Some(false));
        assert_eq!(regions.loans_conflict_at(a,c,CfgPointId(2)),Some(false));
    }
    #[test]
    fn solved_outlives_extends_parent_to_child_use_points() {
        let mut regions=LocalRegionInference::default();
        let outer=regions.add_loan(loan(1,7,Place::Root,&[1]),LoanKind::Exclusive);
        let inner=regions.add_loan(loan(2,7,Place::Root,&[2,3]),LoanKind::Shared);
        regions.require_outlives(outer,inner);
        regions.solve().unwrap();
        assert_eq!(regions.live_at(outer,CfgPointId(3)),Some(true));
        assert_eq!(regions.live_at(inner,CfgPointId(1)),Some(false));
        assert_eq!(regions.live_at(RegionId(999),CfgPointId(3)),None);
    }
}

#[cfg(test)]
mod provenance_variables_0627_tests {
    use super::*;
    fn names(v:&[&str])->Vec<String>{v.iter().map(|s|s.to_string()).collect()}
    #[test]
    fn region_variable_phi_accumulates_all_alternative_sources(){
        let mut v=ProvenanceVariables::new();
        let a=v.parameter(0).unwrap();let b=v.parameter(1).unwrap();
        let left=v.fresh().unwrap();let right=v.fresh().unwrap();let merged=v.fresh().unwrap();
        v.flows_into(a,left).unwrap();v.flows_into(b,right).unwrap();
        v.flows_into(left,merged).unwrap();v.flows_into(right,merged).unwrap();
        v.solve().unwrap();
        assert_eq!(v.origins(merged),Some(3));
        let sig=RegionSignature::new(&names(&["a","b"]),&[Some("a".into()),Some("b".into())],
            Some("a".into()),&[]).unwrap();
        assert!(v.verify_return(merged,&sig).is_err());
        let bound=RegionSignature::new(&names(&["a","b"]),&[Some("a".into()),Some("b".into())],
            Some("a".into()),&[("b".into(),"a".into())]).unwrap();
        v.verify_return(merged,&bound).unwrap();
    }
    #[test]
    fn nested_reborrow_constraints_propagate_origins_through_cycles(){
        let mut v=ProvenanceVariables::new();
        let source=v.parameter(0).unwrap();
        let outer=v.fresh().unwrap();let middle=v.fresh().unwrap();let inner=v.fresh().unwrap();
        v.flows_into(source,outer).unwrap();v.flows_into(outer,middle).unwrap();
        v.flows_into(middle,inner).unwrap();v.flows_into(inner,middle).unwrap();
        v.solve().unwrap();
        assert_eq!(v.origins(inner),Some(1));
        let sig=RegionSignature::new(&names(&["a"]),&[Some("a".into())],Some("a".into()),&[]).unwrap();
        v.verify_return(inner,&sig).unwrap();
    }
    #[test]
    fn unbound_result_rejected_and_no_unproven_sources_added(){
        let mut v=ProvenanceVariables::new();
        let result=v.fresh().unwrap();
        let sig=RegionSignature::new(&names(&["a"]),&[Some("a".into())],Some("a".into()),&[]).unwrap();
        v.solve().unwrap();
        assert!(v.verify_return(result,&sig).is_err());
        assert!(v.flows_into(ProvenanceVar(999),result).is_err());
    }
}

#[cfg(test)]
mod interprocedural_region_constraints_0636_tests {
    use super::*;
    fn signature(outlives:bool)->RegionSignature {
        let bounds=if outlives {vec![("b".into(),"a".into())]}else{Vec::new()};
        RegionSignature::new(&["a".into(),"b".into()],
            &[Some("a".into()),Some("b".into())],Some("a".into()),&bounds).unwrap()
    }
    #[test]
    fn instantiated_call_preserves_all_return_alternatives(){
        let mut vars=ProvenanceVariables::new();
        let ret=vars.instantiate_call(0b11,&[0,1]).unwrap();
        vars.solve().unwrap();
        assert_eq!(vars.origins(ret),Some(0b11));
        assert!(vars.verify_return(ret,&signature(false)).is_err());
        assert!(vars.verify_return(ret,&signature(true)).is_ok());
    }
    #[test]
    fn forwarding_twice_keeps_concrete_caller_sources(){
        let mut vars=ProvenanceVariables::new();
        let first=vars.instantiate_call(0b11,&[0,1]).unwrap();
        let second=vars.fresh().unwrap();
        vars.flows_into(first,second).unwrap();
        vars.solve().unwrap();
        assert_eq!(vars.origins(second),Some(0b11));
        assert!(vars.verify_return(second,&signature(true)).is_ok());
    }
    #[test]
    fn call_summary_cannot_silently_drop_missing_formals(){
        let mut vars=ProvenanceVariables::new();
        assert!(vars.instantiate_call(0b10,&[0]).is_err());
        assert!(vars.instantiate_call(0,&[0,1]).is_err());
        assert!(vars.instantiate_call(1,&[64]).is_err());
    }
    #[test]
    fn shared_caller_parameter_remap_does_not_invent_a_region(){
        let mut vars=ProvenanceVariables::new();
        let ret=vars.instantiate_call(0b11,&[0,0]).unwrap();
        vars.solve().unwrap();
        assert_eq!(vars.origins(ret),Some(1));
        assert!(vars.verify_return(ret,&signature(false)).is_ok());
    }
}

#[cfg(test)]
mod interprocedural_alternative_sources_0637_tests {
    use super::*;
    fn signature(include_c:bool)->RegionSignature{
        let mut bounds=vec![("b".into(),"a".into())];
        if include_c{bounds.push(("c".into(),"a".into()));}
        RegionSignature::new(&["a".into(),"b".into(),"c".into()],
            &[Some("a".into()),Some("b".into()),Some("c".into())],
            Some("a".into()),&bounds).unwrap()
    }
    #[test]
    fn nested_calls_preserve_all_alternative_regions(){
        let mut vars=ProvenanceVariables::new();
        let first=vars.instantiate_call_sources(0b11,&[0b001,0b110]).unwrap();
        vars.solve().unwrap();
        assert_eq!(vars.origins(first),Some(0b111));
        let next=vars.instantiate_call_sources(0b1,&[vars.origins(first).unwrap()]).unwrap();
        vars.solve().unwrap();
        assert_eq!(vars.origins(next),Some(0b111));
        assert!(vars.verify_return(next,&signature(true)).is_ok());
        assert!(vars.verify_return(next,&signature(false)).is_err());
    }
    #[test]
    fn a_missing_or_empty_actual_reference_is_never_ignored(){
        let mut vars=ProvenanceVariables::new();
        assert!(vars.instantiate_call_sources(0b11,&[1]).is_err());
        assert!(vars.instantiate_call_sources(0b11,&[1,0]).is_err());
        assert!(vars.instantiate_call_sources(0,&[1,2]).is_err());
    }
    #[test]
    fn unselected_formals_do_not_create_unproven_sources(){
        let mut vars=ProvenanceVariables::new();
        let returned=vars.instantiate_call_sources(0b10,&[0,0b100]).unwrap();
        vars.solve().unwrap();
        assert_eq!(vars.origins(returned),Some(0b100));
    }
    #[test]
    fn source_union_preserves_no_copy_semantics(){
        let mut vars=ProvenanceVariables::new();
        let ret=vars.instantiate_call_sources(0b11,&[0b10,0b10]).unwrap();
        vars.solve().unwrap();
        assert_eq!(vars.origins(ret),Some(0b10));
    }
}

#[cfg(test)]
mod combined_region_solver_0637_tests {
    use super::*;
    use crate::{cfg_nll::{CfgPointId,LocalRegion},ids::SymbolId,ir::Place};
    use std::collections::HashSet;
    fn signature(allow_b:bool)->RegionSignature {
        let bounds=if allow_b{vec![("b".into(),"a".into())]}else{Vec::new()};
        RegionSignature::new(&["a".into(),"b".into()],
            &[Some("a".into()),Some("b".into())],Some("a".into()),&bounds).unwrap()
    }
    fn local(binding:u32,points:&[u32])->LocalRegion {
        LocalRegion{binding:SymbolId(binding),owner:SymbolId(50),place:Place::Root,
            points:points.iter().map(|&p|CfgPointId(p)).collect::<HashSet<_>>()}
    }
    #[test]
    fn local_outlives_and_interprocedural_sources_are_solved_together(){
        let sig=signature(true);
        let mut solver=RegionConstraintSolver::new(&sig);
        let parent=solver.local_regions_mut().add_loan(local(1,&[1]),LoanKind::Exclusive);
        let child=solver.local_regions_mut().add_loan(local(2,&[2,3]),LoanKind::Shared);
        solver.local_regions_mut().require_outlives(parent,child);
        let result=solver.instantiate_call_sources(0b11,&[0b01,0b10]).unwrap();
        solver.solve_and_verify_return(result).unwrap();
        assert_eq!(solver.local_regions_mut().live_at(parent,CfgPointId(3)),Some(true));
    }
    #[test]
    fn local_solution_cannot_hide_an_invalid_universal_return(){
        let sig=signature(false);
        let mut solver=RegionConstraintSolver::new(&sig);
        let parent=solver.local_regions_mut().add_loan(local(1,&[1]),LoanKind::Shared);
        let child=solver.local_regions_mut().add_loan(local(2,&[2]),LoanKind::Shared);
        solver.local_regions_mut().require_outlives(parent,child);
        let result=solver.instantiate_call_sources(0b11,&[0b01,0b10]).unwrap();
        assert!(solver.solve_and_verify_return(result).is_err());
    }
}

#[cfg(test)]
mod call_region_constraints_0638_tests {
    use super::*;
    fn strings(input:&[&str])->Vec<String>{input.iter().map(|s|(*s).to_owned()).collect()}

    #[test]
    fn nested_calls_propagate_every_origin_from_alternative_actuals(){
        let sig=RegionSignature::new(&strings(&["a","b","c"]),
            &[Some("a".into()),Some("b".into()),Some("c".into())],
            Some("a".into()),&[("b".into(),"a".into()),("c".into(),"b".into())]).unwrap();
        let mut solver=RegionConstraintSolver::new(&sig);
        let value=solver.instantiate_call_sources(0b011,&[0b001,0b110,0]).unwrap();
        solver.solve_and_verify_return(value).unwrap();
        let invalid=RegionSignature::new(&strings(&["a","b","c"]),
            &[Some("a".into()),Some("b".into()),Some("c".into())],
            Some("a".into()),&[("b".into(),"a".into())]).unwrap();
        let mut bad=RegionConstraintSolver::new(&invalid);
        let value=bad.instantiate_call_sources(0b011,&[0b001,0b110,0]).unwrap();
        assert!(bad.solve_and_verify_return(value).is_err());
    }

    #[test]
    fn call_summary_must_not_drop_missing_or_unproven_actuals(){
        let sig=RegionSignature::new(&strings(&["a"]),
            &[Some("a".into())],Some("a".into()),&[]).unwrap();
        let mut solver=RegionConstraintSolver::new(&sig);
        assert!(solver.instantiate_call_sources(0b10,&[1]).is_err());
        assert!(solver.instantiate_call_sources(0b11,&[1,0]).is_err());
        assert!(solver.instantiate_call_sources(0,&[1]).is_err());
    }
}

#[cfg(test)]
mod interprocedural_graph_worklist_0647_tests {
    use super::*;
    #[test]
    fn reverse_order_long_chain_converges_with_all_origins() {
        let mut graph=ProvenanceVariables::new();
        let left=graph.parameter(0).unwrap();
        let right=graph.parameter(1).unwrap();
        let mut nodes=Vec::new();
        for _ in 0..256 {nodes.push(graph.fresh().unwrap());}
        for i in (1..nodes.len()).rev(){
            graph.flows_into(nodes[i-1],nodes[i]).unwrap();
        }
        graph.flows_into(left,nodes[0]).unwrap();
        graph.flows_into(right,nodes[0]).unwrap();
        graph.solve().unwrap();
        assert_eq!(graph.origins(*nodes.last().unwrap()),Some(0b11));
    }

    #[test]
    fn diamond_with_cycle_never_discards_a_possible_origin(){
        let mut graph=ProvenanceVariables::new();
        let x=graph.parameter(0).unwrap();
        let y=graph.parameter(1).unwrap();
        let middle=graph.fresh().unwrap();
        let a=graph.fresh().unwrap();
        let b=graph.fresh().unwrap();
        let phi=graph.fresh().unwrap();
        for (src,dst) in [(x,a),(y,b),(a,phi),(b,phi),(phi,middle),
            (middle,a),(middle,b),(a,middle),(b,middle)] {
            graph.flows_into(src,dst).unwrap();
        }
        graph.solve().unwrap();
        assert_eq!(graph.origins(phi),Some(0b11));
        assert_eq!(graph.origins(middle),Some(0b11));
    }

    #[test]
    fn instantiated_multi_source_call_checks_all_caller_bounds(){
        let declared=vec!["a".to_owned(),"b".to_owned(),"c".to_owned()];
        let params=vec![Some("a".to_owned()),Some("b".to_owned()),
            Some("c".to_owned())];
        let bounds=vec![("b".to_owned(),"a".to_owned()),
            ("c".to_owned(),"b".to_owned())];
        let good=RegionSignature::new(&declared,&params,Some("a".to_owned()),&bounds).unwrap();
        let mut solver=RegionConstraintSolver::new(&good);
        let result=solver.instantiate_call_sources(0b111,&[0b001,0b110,0b100]).unwrap();
        solver.solve_and_verify_return(result).unwrap();
        let bad=RegionSignature::new(&declared,&params,Some("a".to_owned()),
            &bounds[..1]).unwrap();
        let mut solver=RegionConstraintSolver::new(&bad);
        let result=solver.instantiate_call_sources(0b111,&[0b001,0b110,0b100]).unwrap();
        assert!(solver.solve_and_verify_return(result).is_err());
    }
}
