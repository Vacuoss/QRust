//Compilation-local, path-sensitive ownership analysis for typed host code
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;
use crate::{ids::SymbolId, ir::{TypeId,FieldId,MovePathId}};

const MAX_NODES:usize=8192;
const MAX_EVENTS:usize=131072;
const MAX_STEPS:usize=2_000_000;

#[derive(Debug,Clone,Copy,PartialEq,Eq,Hash)]
pub struct FieldKey {pub aggregate:TypeId,pub field:FieldId}
#[derive(Debug,Clone,PartialEq,Eq,Hash)]
pub struct Path {pub owner:SymbolId,pub fields:Vec<FieldKey>}
impl Path {
    pub fn root(owner:SymbolId)->Self{Self{owner,fields:Vec::new()}}
    pub fn child(&self,field:FieldKey)->Self{let mut result=self.clone();result.fields.push(field);result}
    pub fn ancestor_of(&self,other:&Self)->bool {
        self.owner==other.owner && self.fields.len()<=other.fields.len() &&
        self.fields.iter().zip(&other.fields).all(|(a,b)|a==b)
    }
    pub fn overlaps(&self,other:&Self)->bool {
        if self.owner!=other.owner{return false;}
        for (a,b) in self.fields.iter().zip(other.fields.iter()) {
            if a.aggregate!=b.aggregate{return true;}
            if a.field!=b.field{return false;}
        }
        true
    }
}
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct PathNode {pub id:MovePathId,pub parent:Option<MovePathId>,pub place:Path}
#[derive(Debug,Default)]
pub struct Forest {
    nodes:Vec<PathNode>,
    roots:HashMap<SymbolId,MovePathId>,
    ids:HashMap<Path,MovePathId>, //projected paths only
}
impl Forest {
    pub fn intern(&mut self,path:&Path)->Result<MovePathId,String>{
        if path.fields.is_empty() {
            if let Some(&id)=self.roots.get(&path.owner){return Ok(id);}
            let id=MovePathId(u32::try_from(self.nodes.len()).map_err(|_|"too many move paths")?);
            self.nodes.push(PathNode{id,parent:None,place:path.clone()});
            self.roots.insert(path.owner,id);
            return Ok(id);
        }
        if let Some(&id)=self.ids.get(path){return Ok(id);}
        let mut parent_path=path.clone();
        parent_path.fields.pop();
        let parent=Some(self.intern(&parent_path)?);
        let id=MovePathId(u32::try_from(self.nodes.len()).map_err(|_|"too many move paths")?);
        self.nodes.push(PathNode{id,parent,place:path.clone()});
        self.ids.insert(path.clone(),id);
        Ok(id)
    }
    #[cfg(test)]
    pub fn path(&self,id:MovePathId)->Option<&Path>{self.nodes.get(id.0 as usize).map(|n|&n.place)}
    #[cfg(test)]
    pub fn nodes(&self)->&[PathNode]{&self.nodes}
}

//A typed reborrow records its parent loan; parent provenance cannot change at a CFG join
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Access {Read,Move,Write,Initialize,BorrowShared,BorrowMut,ReserveMut,ActivateMut,EndLoan,
    //Local-storage boundaries are MIR events, never QASM operations
    StorageLive,StorageDead,Drop,QuantumRequireConsumed,
    BindPhiMut}
#[derive(Debug,Clone)]
pub struct Event {
    pub op:Access,
    pub path:Path,
    pub loan:Option<SymbolId>,
    pub parent:Option<SymbolId>,
    pub token:usize,
}
#[derive(Debug,Clone,PartialEq,Eq)]
struct Loan {
    place:Path,
    exclusive:bool,
    parent:Option<SymbolId>,
    reserved:bool,
}
//This is a relational operation, not N sequential borrows. Exactly the child whose parent loan was
//chosen by the source PHI becomes live
#[derive(Debug,Clone,PartialEq,Eq)]
struct PhiReborrow {
    source:SymbolId,
    children:Vec<(SymbolId,SymbolId,Path)>,
}
#[derive(Debug,Clone,Default,PartialEq,Eq)]
struct State {
    uninit_roots:HashSet<SymbolId>,
    uninit_fields:HashSet<Path>,
    //MAY-live initialized roots: a quantum handle must be consumed on all paths before scope end; union is
    //deliberately conservative
    may_live:HashSet<Path>,
    monitored_quantum:Arc<HashSet<SymbolId>>,
    loans:HashMap<SymbolId,Loan>,
    by_owner:HashMap<SymbolId,Vec<SymbolId>>,
    //Reborrow children are sparse. An indexed lookup prevents every independent loan from being scanned for
    //each reference access
    by_parent:HashMap<SymbolId,Vec<SymbolId>>,
    //MUST-active subset. Access through a reference / reborrow requires it to exist on every incoming
    //branch, not just one of them
    definite:HashSet<SymbolId>,
    phi_presence:HashMap<SymbolId,Vec<u64>>,
    phi_groups:Arc<HashMap<SymbolId,Vec<SymbolId>>>,
    phi_roots:Arc<HashMap<SymbolId,SymbolId>>,
    phi_members:Arc<HashMap<SymbolId,Vec<(SymbolId,u64)>>>,
    phi_joint:Vec<HashSet<SymbolId>>,
    //When the relational state budget is exceeded, every subsequent PHI access fails closed; a widened MAY
    //set cannot prove exclusivity
    phi_joint_overflow:bool,
    phi_reborrows:Arc<HashMap<SymbolId,PhiReborrow>>,
}
impl State {
    fn join_needed(&self,another:&Self)->bool {
        if another.may_live.iter().any(|p|!self.may_live.contains(p)) ||
           another.uninit_roots.iter().any(|id|!self.uninit_roots.contains(id)) ||
           another.uninit_fields.iter().any(|p|!self.uninit_fields.contains(p)) ||
           self.definite.iter().any(|id|!another.definite.contains(id)) {
            return true;
        }
        if !self.phi_joint_overflow && (another.phi_joint_overflow ||
            another.phi_joint.iter().any(|scenario|!self.phi_joint.contains(scenario))) {
            return true;
        }
        const ZERO:[u64;1]=[0];
        for (&id,values) in &self.phi_presence {
            let other=another.phi_presence.get(&id).map(Vec::as_slice).unwrap_or(&ZERO);
            if other.iter().any(|mask|!values.contains(mask)){return true;}
        }
        for (&id,values) in &another.phi_presence {
            if !self.phi_presence.contains_key(&id) && values.iter().any(|mask|*mask!=0){return true;}
        }
        another.loans.iter().any(|(id,loan)|match self.loans.get(id){
            None=>true,
            Some(old)=>old.place!=loan.place || old.exclusive!=loan.exclusive ||
                old.parent!=loan.parent || (old.reserved && !loan.reserved),
        })
    }
    fn join(&mut self,another:&Self)->bool {
        let mut changed=false;
        for path in &another.may_live {changed|=self.may_live.insert(path.clone());}
        for &owner in &another.uninit_roots {changed|=self.uninit_roots.insert(owner);}
        for path in &another.uninit_fields {changed|=self.uninit_fields.insert(path.clone());}
        let old=self.definite.len();
        self.definite.retain(|id|another.definite.contains(id));
        changed|=old!=self.definite.len();
        for (&key,old) in &mut self.phi_presence {
            let incoming=another.phi_presence.get(&key).map(Vec::as_slice)
                .unwrap_or(&[0]);
            for &mask in incoming {
                if !old.contains(&mask) {
                    if old.len()>=64 {
                        //Saturation widens to a permanently failing empty scenario rather than certifying a possible dangling
                        //reference. This is deliberately fail-closed
                        old.clear();old.push(0);
                        changed=true;
                        break;
                    }
                    old.push(mask);changed=true;
                }
            }
        }
        for (&key,incoming) in &another.phi_presence {
            if incoming.iter().all(|mask|*mask==0){continue;}
            if let std::collections::hash_map::Entry::Vacant(slot)=self.phi_presence.entry(key){
                let mut states=Vec::with_capacity(incoming.len().saturating_add(1).min(64));
                states.push(0); //the old predecessor had no active candidate
                for &mask in incoming {
                    if states.contains(&mask){continue;}
                    if states.len()>=64 {
                        states.clear();states.push(0);
                        break;
                    }
                    states.push(mask);
                }
                slot.insert(states);
                changed=true;
            }
        }
        if !self.phi_joint_overflow && another.phi_joint_overflow {
            self.phi_joint_overflow=true;
            self.phi_joint.clear();changed=true;
        }else if !self.phi_joint_overflow {
            for scenario in &another.phi_joint {
                if !self.phi_joint.contains(scenario) {
                    if self.phi_joint.len()>=64 {
                        self.phi_joint_overflow=true;
                        self.phi_joint.clear();changed=true;
                        break;
                    }
                    self.phi_joint.push(scenario.clone());changed=true;
                }
            }
        }
        for (&id,loan) in &another.loans {
            if let Some(existing)=self.loans.get_mut(&id) {
                if existing.place!=loan.place || existing.exclusive!=loan.exclusive || existing.parent!=loan.parent {
                    existing.place=Path::root(existing.place.owner);
                    existing.exclusive=true;
                    existing.reserved=false;
                    changed=true;
                } else if existing.reserved && !loan.reserved {
                    existing.reserved=false;
                    changed=true;
                }
            }else {
                self.by_owner.entry(loan.place.owner).or_default().push(id);
                if let Some(parent)=loan.parent {
                    self.by_parent.entry(parent).or_default().push(id);
                }
                self.loans.insert(id,loan.clone());changed=true;
            }
        }
        changed
    }
    fn mark_uninit(&mut self,path:&Path){
        if path.fields.is_empty(){self.uninit_roots.insert(path.owner);}
        else{self.uninit_fields.insert(path.clone());}
    }
    fn clear_uninit_descendants(&mut self,path:&Path){
        if path.fields.is_empty(){
            self.uninit_roots.remove(&path.owner);
            self.uninit_fields.retain(|m|m.owner!=path.owner);
        }else{
            self.uninit_fields.retain(|m|!path.ancestor_of(m));
        }
    }
    fn initialized(&self,path:&Path)->bool {
        !self.uninit_roots.contains(&path.owner) &&
            !self.uninit_fields.iter().any(|m|m.owner==path.owner &&
                (m.ancestor_of(path)||path.ancestor_of(m)))
    }
    fn has_uninit_ancestor(&self,path:&Path,include_self:bool)->bool {
        if self.uninit_roots.contains(&path.owner) &&
            (include_self || !path.fields.is_empty()){return true;}
        self.uninit_fields.iter().any(|m|m.ancestor_of(path) &&
            (include_self || m!=path))
    }
    fn loan_ancestor(&self,borrowed:SymbolId,possible_parent:SymbolId)->bool {
        let mut current=Some(borrowed);
        for _ in 0..=self.loans.len() {
            let Some(id)=current else{return false;};
            if id==possible_parent{return true;}
            current=self.loans.get(&id).and_then(|l|l.parent);
        }
        false //corrupted cyclic provenance is detected during insertion
    }
    fn child_suspends(&self,id:SymbolId,for_exclusive:bool)->bool {
        self.by_parent.get(&id).is_some_and(|children|
            children.iter().any(|child|self.loans.get(child).is_some_and(|loan|
                for_exclusive || loan.exclusive)))
    }
    fn conflict(&self,path:&Path,op:Access,via:Option<SymbolId>)->bool {
        let overlaps=|id:SymbolId,loan:&Loan| {
            if loan.place.owner!=path.owner || !loan.place.overlaps(path){return false;}
            if via.is_some_and(|v|self.loan_ancestor(v,id)){return false;}
            match op {
                Access::Read|Access::BorrowShared=>loan.exclusive && !loan.reserved,
                Access::ReserveMut=>loan.exclusive,
                Access::Move|Access::Write|Access::Initialize|Access::BorrowMut|Access::ActivateMut=>true,
                Access::EndLoan=>false,
                Access::Drop|Access::StorageDead=>true,
                Access::StorageLive|Access::QuantumRequireConsumed|Access::BindPhiMut=>false,
            }
        };
        if !self.by_owner.contains_key(&path.owner){return false;}
        if self.loans.len()<8 {
            self.loans.iter().any(|(&id,loan)|overlaps(id,loan))
        }else {
            self.by_owner.get(&path.owner).is_some_and(|ids|
                ids.iter().any(|id|self.loans.get(id).is_some_and(|loan|overlaps(*id,loan))))
        }
    }
    //Read-only verification never changes an ownership snapshot
    fn update_phi_presence(&mut self,id:SymbolId,created:bool) {
        if !self.phi_joint_overflow {
            for scenario in &mut self.phi_joint {
                if created{scenario.insert(id);}else{scenario.remove(&id);}
            }
        }
        if let Some(groups)=self.phi_members.get(&id).cloned() {
            for (group,bit) in groups {
                let values=self.phi_presence.entry(group).or_insert_with(||vec![0]);
                for mask in values.iter_mut() {
                    if created{*mask|=bit}else{*mask&=!bit;}
                }
                values.sort_unstable();values.dedup();
            }
        }
    }
    fn independent_phi_never_cooccurs(&self,selected:SymbolId,other:SymbolId)->bool {
        !self.phi_joint_overflow && !self.phi_joint.is_empty() &&
            self.phi_members.contains_key(&selected) &&
            self.phi_joint.iter().any(|scenario|scenario.contains(&selected)) &&
            self.phi_joint.iter().any(|scenario|scenario.contains(&other)) &&
            !self.phi_joint.iter().any(|scenario|
                scenario.contains(&selected) && scenario.contains(&other))
    }
    fn inspect_phi_history(&self,choices:&[SymbolId],masks:&[u64])->Option<String> {
        if self.phi_joint_overflow || self.phi_joint.is_empty() {
            return Some("reference PHI lacks exact joint CFG provenance".into());
        }
        let mut witnessed=HashSet::new();
        for scenario in &self.phi_joint {
            let mut selected=0u64;
            for (index,&member) in choices.iter().enumerate() {
                if scenario.contains(&member){selected|=1u64<<index;}
            }
            if !selected.is_power_of_two() || !masks.contains(&selected) {
                return Some("reference PHI joint CFG selection disagrees with provenance".into());
            }
            let mut current=Some(choices[selected.trailing_zeros() as usize]);
            let mut depth=0usize;
            while let Some(loan_id)=current {
                if depth>self.loans.len() || !scenario.contains(&loan_id) {
                    return Some("reference PHI reborrow ancestor is absent on selected CFG path".into());
                }
                let Some(loan)=self.loans.get(&loan_id)else{
                    return Some("reference PHI has an unverified reborrow ancestor".into());
                };
                current=loan.parent;
                depth+=1;
            }
            witnessed.insert(selected);
        }
        if masks.iter().any(|mask|!witnessed.contains(mask)) {
            return Some("reference PHI has an unwitnessed CFG alternative".into());
        }
        None
    }
    fn inspect_phi(&self,event:&Event,id:SymbolId)->Option<String> {
        if self.phi_joint_overflow {
            return Some("cross-CFG PHI provenance exceeds relational budget".into());
        }
        if event.path.fields.len()!=0 ||
            self.phi_roots.get(&id)!=Some(&event.path.owner) {
            return Some("reference PHI generation does not match binding".into());
        }
        if !self.initialized(&event.path){
            return Some("reference PHI result is uninitialized".into());
        }
        let Some(choices)=self.phi_groups.get(&id) else {
            return Some("unknown reference PHI provenance group".into());
        };
        let Some(masks)=self.phi_presence.get(&id) else {
            return Some("reference PHI has a CFG path with no live provenance".into());
        };
        if masks.is_empty() || masks.contains(&0) {
            return Some("reference PHI has a CFG path with no live provenance".into());
        }
        let valid_bits=(1u64<<choices.len())-1;
        if masks.iter().any(|mask|!mask.is_power_of_two() || mask & !valid_bits != 0) {
            return Some("reference PHI has ambiguous or forged active provenance".into());
        }
        if let Some(error)=self.inspect_phi_history(choices,masks) {
            return Some(error);
        }
        for &mask in masks {
            for (i,loan_id) in choices.iter().enumerate() {
                if mask & (1u64<<i)==0{continue;}
                let Some(loan)=self.loans.get(loan_id) else {
                    return Some("reference PHI alternative loan is missing".into());
                };
                let independent_conflict=self.by_owner.get(&loan.place.owner).is_some_and(|ids|
                    ids.iter().any(|other_id|{
                        if choices.contains(other_id){return false;}
                        if self.independent_phi_never_cooccurs(*loan_id, *other_id) {
                            return false;
                        }
                        self.loans.get(other_id).is_some_and(|other|
                            other.place.overlaps(&loan.place) &&
                            other.exclusive && !other.reserved &&
                            !self.loan_ancestor(*loan_id,*other_id))
                    }));
                if !self.initialized(&loan.place) || self.child_suspends(*loan_id,true) ||
                    independent_conflict {
                    return Some("reference PHI alternative conflicts with ownership".into());
                }
            }
        }
        None
    }
    fn inspect_phi_write(&self,event:&Event,id:SymbolId)->Option<String> {
        //The read proof checks initialized provenance, nonempty masks and the absence of independent active
        //exclusive borrows
        if let Some(error)=self.inspect_phi(event,id){return Some(error);}
        let Some(choices)=self.phi_groups.get(&id)else{
            return Some("unknown mutable reference PHI group".into());
        };
        let Some(masks)=self.phi_presence.get(&id)else{
            return Some("mutable reference PHI missing provenance".into());
        };
        let valid_bits=(1u64<<choices.len())-1;
        for &mask in masks {
            if !mask.is_power_of_two() || mask & !valid_bits != 0 {
                return Some("mutable reference PHI must select exactly one valid loan per CFG path".into());
            }
            for (index,&loan_id) in choices.iter().enumerate() {
                if mask & (1u64<<index)==0{continue;}
                let Some(loan)=self.loans.get(&loan_id)else{
                    return Some("mutable reference PHI loan is missing".into());
                };
                if !loan.exclusive || loan.reserved || self.child_suspends(loan_id,true) {
                    return Some("mutable reference PHI loan is not writable".into());
                }
                let conflict=self.by_owner.get(&loan.place.owner).is_some_and(|ids|
                    ids.iter().any(|other_id| {
                        if choices.contains(other_id) ||
                           self.loan_ancestor(loan_id,*other_id) ||
                           self.independent_phi_never_cooccurs(loan_id,*other_id){return false;}
                        self.loans.get(other_id).is_some_and(|other|
                            other.place.overlaps(&loan.place))
                    }));
                if conflict {
                    return Some("conflicting access through mutable reference PHI".into());
                }
            }
        }
        None
    }
    fn bind_phi_mut(&mut self,event:&Event)->Option<String> {
        let Some(dest)=event.loan else{return Some("missing derived PHI generation".into())};
        let Some(spec)=self.phi_reborrows.get(&dest)else{
            return Some("unknown derived PHI generation".into());
        };
        let Some(source)=event.parent else{return Some("missing PHI parent generation".into())};
        if spec.source!=source || self.phi_roots.get(&dest)!=Some(&event.path.owner) ||
            self.phi_joint_overflow || spec.children.is_empty() ||
            spec.children.len()>32 {return Some("invalid late PHI reborrow identity".into());}
        let Some(old)=self.phi_groups.get(&source)else{
            return Some("derived PHI source generation not registered".into());
        };
        let Some(new)=self.phi_groups.get(&dest)else{
            return Some("derived PHI output generation not registered".into());
        };
        if old.len()!=spec.children.len() || new.len()!=old.len() ||
            spec.children.iter().enumerate().any(|(index,(parent,child,_))|
                *parent!=old[index] || *child!=new[index]) {
            return Some("late PHI reborrow candidates do not match parent generation".into());
        }
        let probe=Event{op:Access::Write,
            path:Path::root(*self.phi_roots.get(&source)
                .expect("registered derived PHI source root")),
            loan:Some(source),parent:None,token:event.token};
        if let Some(error)=self.inspect_phi_write(&probe,source){return Some(error);}
        let Some(masks)=self.phi_presence.get(&source).cloned()else{
            return Some("derived PHI lacks active source provenance".into());
        };
        if masks.is_empty() || masks.len()>64 || masks.iter().any(|m|!m.is_power_of_two()) {
            return Some("late PHI reborrow needs exactly one live source per path".into());
        }
        let mut destinations=Vec::with_capacity(masks.len());
        for mask in &masks {
            let position=mask.trailing_zeros() as usize;
            if position>=spec.children.len(){return Some("invalid late PHI selected parent".into());}
            destinations.push(1u64<<position);
        }
        for (parent,child,path) in &spec.children {
            if self.loans.contains_key(child) || self.definite.contains(child) {
                return Some("late PHI reborrow child is already active".into());
            }
            let Some(base)=self.loans.get(parent)else{
                return Some("late PHI reborrow parent is not live".into());
            };
            if !base.exclusive || base.reserved ||
                !base.place.ancestor_of(path) ||
                path.fields.len()>base.place.fields.len()+1 {
                return Some("late PHI reborrow parent is not exclusively writable".into());
            }
        }
        //Every joint history must contain exactly the parent selected by the source PHI, or the relational
        //model has lost its correlation
        if self.phi_joint.is_empty() {
            return Some("late PHI reborrow lacks joint CFG histories".into());
        }
        for scenario in &self.phi_joint {
            if spec.children.iter().filter(|(parent,_,_)|scenario.contains(parent)).count()!=1 {
                return Some("late PHI reborrow has ambiguous cross-CFG parent".into());
            }
        }
        for (parent,child,path) in &spec.children {
            self.by_owner.entry(path.owner).or_default().push(*child);
            self.by_parent.entry(*parent).or_default().push(*child);
            self.loans.insert(*child,Loan{place:path.clone(),exclusive:true,
                parent:Some(*parent),reserved:false});
        }
        for scenario in &mut self.phi_joint {
            for (parent,child,_) in &spec.children {
                if scenario.contains(parent) {scenario.insert(*child);break;}
            }
        }
        destinations.sort_unstable();destinations.dedup();
        self.phi_presence.insert(dest,destinations);
        let mut affected=HashSet::new();
        for (_,child,_) in &spec.children {
            if let Some(groups)=self.phi_members.get(child) {
                for &(group,_) in groups {
                    if group!=dest {affected.insert(group);}
                }
            }
        }
        for group in affected {
            let Some(members)=self.phi_groups.get(&group)else{
                return Some("late PHI child references unregistered result group".into());
            };
            let mut masks=Vec::new();
            for scenario in &self.phi_joint {
                let mut mask=0u64;
                for (index,member) in members.iter().enumerate() {
                    if scenario.contains(member) {mask|=1u64<<index;}
                }
                if !masks.contains(&mask){
                    if masks.len()>=64 {
                        return Some("late PHI result exceeds relational state budget".into());
                    }
                    masks.push(mask);
                }
            }
            self.phi_presence.insert(group,masks);
        }
        //None of the new loans is MUST-active separately. Exactly one is present per reachable path, proved by
        //the derived PHI generation
        None
    }
    fn inspect(&self,event:&Event)->Option<String> {
        if event.op==Access::Read {
            if let Some(id)=event.loan {
                if self.phi_groups.contains_key(&id){
                    return self.inspect_phi(event,id);
                }
            }
        }
        let p=&event.path;
        if event.op==Access::QuantumRequireConsumed {
            return self.may_live.contains(p).then(||
                "quantum-aware Drop: live Qubit must be measured, moved, or returned".into());
        }
        debug_assert_eq!(event.op,Access::Read);
        if !self.initialized(p) {
            if self.uninit_fields.iter().any(|m|p.ancestor_of(m) && p!=m) {
                return Some("use of partially moved value".into());
            }
            if !p.fields.is_empty() && self.has_uninit_ancestor(p,true) {
                return Some("use of moved field".into());
            }
            return Some("use of possibly uninitialized or moved path".into());
        }
        if let Some(id)=event.loan {
            if !self.definite.contains(&id) {
                return Some("reference not active on every CFG path".into());
            }
            let Some(base)=self.loans.get(&id) else {
                return Some("unknown reference loan".into());
            };
            if !base.place.ancestor_of(p) {
                return Some("reference access outside borrowed place".into());
            }
            if self.child_suspends(id,true) {
                return Some("reference suspended by live reborrow".into());
            }
        }
        if self.conflict(p,Access::Read,event.loan) {
            return Some("conflicting access to a borrowed place (CFG loan conflict)".into());
        }
        None
    }
    fn apply(&mut self,event:&Event)->Option<String> {
        if event.op==Access::BindPhiMut {return self.bind_phi_mut(event);}
        if matches!(event.op,Access::Read|Access::QuantumRequireConsumed) {
            return self.inspect(event);
        }
        if event.op==Access::Write {
            if let Some(id)=event.loan {
                if self.phi_groups.contains_key(&id){
                    return self.inspect_phi_write(event,id);
                }
            }
        }
        let p=&event.path;
        if event.op==Access::StorageLive {
            if !p.fields.is_empty(){return Some("StorageLive must target a local root".into());}
            if self.by_owner.get(&p.owner).is_some_and(|ids|
                ids.iter().any(|id|self.loans.get(id).is_some_and(|loan|loan.place.overlaps(p)))) {
                return Some("StorageLive overlaps a still active loan".into());
            }
            self.mark_uninit(p);
            self.may_live.remove(p);
            return None;
        }
        if event.op==Access::QuantumRequireConsumed {
            if self.may_live.contains(p){return Some("quantum-aware Drop: live Qubit must be measured, moved, or returned".into());}
            return None;
        }
        if event.op==Access::StorageDead {
            if !p.fields.is_empty(){return Some("StorageDead must target a local root".into());}
            if self.by_owner.get(&p.owner).is_some_and(|ids|
                ids.iter().any(|id|self.loans.get(id).is_some_and(|loan|loan.place.overlaps(p)))) {
                return Some("storage cannot end while borrowed".into());
            }
            self.clear_uninit_descendants(p);
            self.mark_uninit(p);
            self.may_live.remove(p);
            return None;
        }
        if event.op==Access::Drop {
            if !self.initialized(p) {return Some("cannot Drop partially moved or uninitialized value".into());}
            if self.conflict(p,Access::Drop,None) {return Some("cannot Drop a borrowed value".into());}
            self.mark_uninit(p);
            self.may_live.remove(p);
            return None;
        }
        if event.op==Access::EndLoan {
            let Some(id)=event.loan else{return Some("EndLoan missing loan ID".into());};
            if self.loans.get(&id).is_some_and(|loan|loan.place!=*p) {
                return Some("EndLoan path does not match live loan".into());
            }
            if self.by_parent.get(&id).is_some_and(|children|!children.is_empty()) {
                return Some("cannot end parent loan with active reborrow".into());
            }
            if let Some(old)=self.loans.remove(&id){
                let empty=if let Some(ids)=self.by_owner.get_mut(&old.place.owner){
                    ids.retain(|existing|*existing!=id);ids.is_empty()
                }else{false};
                if empty{self.by_owner.remove(&old.place.owner);}
                if let Some(parent)=old.parent {
                    let empty=if let Some(children)=self.by_parent.get_mut(&parent){
                        children.retain(|existing|*existing!=id);children.is_empty()
                    }else{false};
                    if empty{self.by_parent.remove(&parent);}
                }
            }
            self.definite.remove(&id);
            self.update_phi_presence(id,false);
            return None;
        }
        if event.op==Access::ActivateMut {
            let Some(id)=event.loan else{return Some("activation missing loan ID".into());};
            if !self.definite.contains(&id) {return Some("activation requires a loan on every CFG path".into());}
            let Some(loan)=self.loans.get(&id) else{return Some("activation of inactive loan".into());};
            if loan.place!=*p {return Some("activation place does not match reserved loan".into());}
            if !loan.exclusive || !loan.reserved {return Some("activation requires a reserved mutable loan".into());}
            if self.child_suspends(id,true) {return Some("activation blocked by a live reborrow".into());}
            //Activation upgrades the reserved shared-like loan to exclusive; independent shared loans must have
            //ended before this point
            if self.conflict(p,Access::ActivateMut,Some(id)) {
                return Some("two-phase mutable activation conflicts with active loan".into());
            }
            self.loans.get_mut(&id).expect("validated active loan").reserved=false;
            return None;
        }
        match event.op {
            Access::Read|Access::Move|Access::BorrowShared|Access::BorrowMut|Access::ReserveMut => {
                if !self.initialized(p) {
                    if self.uninit_fields.iter().any(|m|p.ancestor_of(m) && p!=m) {
                        return Some("use of partially moved value".into());
                    }
                    if !p.fields.is_empty() &&
                        self.has_uninit_ancestor(p,true) {
                        return Some("use of moved field".into());
                    }
                    return Some("use of possibly uninitialized or moved path".into());
                }
            }
            Access::Write|Access::Initialize => {
                if self.has_uninit_ancestor(p,false) {
                    return Some("write through an uninitialized ancestor".into());
                }
            }
            Access::EndLoan|Access::ActivateMut|Access::StorageLive|Access::StorageDead|Access::Drop|Access::QuantumRequireConsumed|Access::BindPhiMut=>unreachable!(),
        }
        let parent=if matches!(event.op,Access::BorrowShared|Access::BorrowMut|Access::ReserveMut){event.parent}
            else{None};
        if event.op==Access::ReserveMut && parent.is_some() {
            //A reserved reborrow needs a separate parent-activation proof; keep it unsupported rather than silently
            //accepting aliases
            return Some("two-phase reborrow is not yet supported".into());
        }
        if let Some(parent_id)=parent {
            let Some(base)=self.loans.get(&parent_id) else {
                return Some("reborrow of inactive parent loan".into());
            };
            if !self.definite.contains(&parent_id){
                return Some("reborrow of parent not active on every CFG path".into());
            }
            if !base.place.ancestor_of(p){
                return Some("reborrow path is outside the parent reference".into());
            }
            if event.op==Access::BorrowMut && (!base.exclusive || base.reserved) {
                return Some("cannot mutably reborrow shared reference".into());
            }
            if self.child_suspends(parent_id,event.op==Access::BorrowMut) {
                return Some("parent reference suspended by a live reborrow".into());
            }
        }
        let via=if parent.is_some(){parent}else{
            if matches!(event.op,Access::BorrowShared|Access::BorrowMut|Access::ReserveMut){None}else{event.loan}
        };
        if let Some(id)=via {
            if !self.definite.contains(&id){
                return Some("reference not active on every CFG path".into());
            }
            if parent.is_none() {
                let Some(base)=self.loans.get(&id)else{return Some("unknown reference loan".into());};
                if !base.place.ancestor_of(p){return Some("reference access outside borrowed place".into());}
                if matches!(event.op,Access::Write|Access::Initialize) {
                    if !base.exclusive {return Some("cannot write through shared reference".into());}
                    if base.reserved {return Some("activate reserved mutable loan before writing".into());}
                }
                if event.op==Access::Move {
                    return Some("cannot move through a borrowed reference".into());
                }
                if self.child_suspends(id,true){
                    return Some("reference suspended by live reborrow".into());
                }
            }
        }
        if self.conflict(p,event.op,via){return Some("conflicting access to a borrowed place (CFG loan conflict)".into());}
        match event.op {
            Access::Move=>{self.mark_uninit(p);self.may_live.remove(p);}
            Access::Write|Access::Initialize=>{
                self.clear_uninit_descendants(p);
                if self.monitored_quantum.contains(&p.owner){self.may_live.insert(p.clone());}
            }
            Access::BorrowShared|Access::BorrowMut|Access::ReserveMut=>{
                let Some(id)=event.loan else{return Some("borrow event without a loan ID".into());};
                if self.loans.contains_key(&id){return Some("loan ID already active".into());}
                self.by_owner.entry(p.owner).or_default().push(id);
                if let Some(parent_id)=parent {
                    self.by_parent.entry(parent_id).or_default().push(id);
                }
                self.loans.insert(id,Loan{place:p.clone(),
                    exclusive:matches!(event.op,Access::BorrowMut|Access::ReserveMut),
                    parent,reserved:event.op==Access::ReserveMut});
                self.definite.insert(id);
                self.update_phi_presence(id,true);
            }
            Access::Read|Access::EndLoan|Access::ActivateMut|Access::StorageLive|Access::StorageDead|Access::Drop|Access::QuantumRequireConsumed|Access::BindPhiMut=>{}
        }
        None
    }
}
#[derive(Debug,Clone,PartialEq,Eq)]
pub struct Conflict {pub node:usize,pub token:usize,pub message:String}
#[derive(Debug)]
pub struct Graph {
    pub entry:usize,
    pub successors:Vec<Vec<usize>>,
    pub events:Vec<Vec<Event>>,
    //Events attached to a particular outgoing CFG edge. For example a borrow invalidated on the else edge
    //must remain live on the then edge
    edge_events:HashMap<(usize,usize),Vec<Event>>,
    pub paths:Forest,
    event_count:usize,
    loan_origins:HashMap<SymbolId,(Path,bool,Option<SymbolId>)>,
    phi_groups:HashMap<SymbolId,Vec<SymbolId>>,
    phi_roots:HashMap<SymbolId,SymbolId>,
    phi_reborrows:HashMap<SymbolId,PhiReborrow>,
}
impl Graph {
    pub fn new(entry:usize,successors:Vec<Vec<usize>>)->Result<Self,String>{
        if successors.len()>MAX_NODES || entry>=successors.len() ||
           successors.iter().flatten().any(|&s|s>=successors.len()) {
            return Err("invalid or oversized borrow CFG".into());
        }
        Ok(Self{entry,events:vec![Vec::new();successors.len()],successors,
            edge_events:HashMap::new(),paths:Forest::default(),event_count:0,
            loan_origins:HashMap::new(),phi_groups:HashMap::new(),
            phi_reborrows:HashMap::new(),
            phi_roots:HashMap::new()})
    }
    #[cfg(test)]
    pub fn register_phi_group(&mut self,id:SymbolId,choices:Vec<SymbolId>)->Result<(),String>{
        self.register_phi_group_for_binding(id,id,choices)
    }
    pub fn register_phi_group_for_binding(&mut self,generation:SymbolId,owner:SymbolId,
        choices:Vec<SymbolId>)->Result<(),String>{
        if choices.is_empty() || choices.len()>32 || choices.contains(&generation) ||
            choices.iter().collect::<HashSet<_>>().len()!=choices.len() ||
            self.phi_groups.contains_key(&generation) {
            return Err("invalid reference PHI group".into());
        }
        self.phi_roots.insert(generation,owner);
        self.phi_groups.insert(generation,choices);
        Ok(())
    }
    pub fn register_phi_reborrow(&mut self,dest:SymbolId,source:SymbolId,
        children:Vec<(SymbolId,SymbolId,Path)>)->Result<(),String>{
        let old=self.phi_groups.get(&source)
            .ok_or("late PHI reborrow source generation missing")?;
        let new=self.phi_groups.get(&dest)
            .ok_or("late PHI reborrow output generation missing")?;
        if source==dest || children.len()<2 || children.len()!=old.len() ||
            children.len()!=new.len() ||
            children.iter().enumerate().any(|(index,(parent,child,path))|
                *parent!=old[index] || *child!=new[index] ||
                path.owner==self.phi_roots[&dest]) ||
            self.phi_reborrows.contains_key(&dest) {
            return Err("invalid late PHI reborrow parent-child correspondence".into());
        }
        let unique=children.iter().map(|(_,child,_)|*child)
            .collect::<HashSet<_>>();
        if unique.len()!=children.len() || children.iter().any(|(parent,child,_)|
            old.contains(child) || parent==child) {
            return Err("late PHI reborrow aliases a parent loan ID".into());
        }
        self.phi_reborrows.insert(dest,PhiReborrow{source,children});
        Ok(())
    }
    fn register(&mut self,event:&Event)->Result<(),String>{
        if self.event_count>=MAX_EVENTS{return Err("borrow event limit exceeded".into());}
        if matches!(event.op,Access::BorrowMut|Access::BorrowShared|Access::ReserveMut){
            let id=event.loan.ok_or("borrow event missing loan ID")?;
            if event.parent==Some(id){return Err("loan cannot reborrow itself".into());}
            let identity=(event.path.clone(),event.op!=Access::BorrowShared,event.parent);
            if let Some(existing)=self.loan_origins.get(&id) {
                if existing!=&identity{return Err("loan identity changes its referent, kind or parent".into());}
            }else {self.loan_origins.insert(id,identity);}
        }else if event.op==Access::BindPhiMut {
            let dest=event.loan.ok_or("late PHI bind requires output generation")?;
            let source=event.parent.ok_or("late PHI bind requires source generation")?;
            if self.phi_reborrows.get(&dest).is_none_or(|spec|spec.source!=source) ||
                self.phi_roots.get(&dest)!=Some(&event.path.owner) ||
                !event.path.fields.is_empty(){
                return Err("unregistered or forged late PHI reborrow event".into());
            }
        }else if event.parent.is_some(){return Err("only borrow events can have a parent".into());}
        self.paths.intern(&event.path)?;
        self.event_count+=1;Ok(())
    }
    pub fn event(&mut self,node:usize,event:Event)->Result<(),String>{
        if node>=self.events.len(){return Err("invalid CFG point".into());}
        self.register(&event)?;
        self.events[node].push(event);Ok(())
    }
    pub(crate) fn event_at(&mut self,node:usize,index:usize,event:Event)->Result<(),String>{
        if !self.events.get(node).is_some_and(|items|index<=items.len()){
            return Err("invalid CFG statement boundary".into());
        }
        self.register(&event)?;
        self.events[node].insert(index,event);
        Ok(())
    }
    pub fn event_on_edge(&mut self,from:usize,to:usize,event:Event)->Result<(),String>{
        if !self.successors.get(from).is_some_and(|v|v.contains(&to)){
            return Err("invalid CFG edge".into());
        }
        self.register(&event)?;
        self.edge_events.entry((from,to)).or_default().push(event);Ok(())
    }
    fn propagate(&self)->Result<Vec<Option<Arc<State>>>,String>{
        let mut incoming:Vec<Option<Arc<State>>>=vec![None;self.events.len()];
        let watched=Arc::new(self.events.iter().flat_map(|events|events.iter())
            .chain(self.edge_events.values().flat_map(|events|events.iter()))
            .filter(|event|event.op==Access::QuantumRequireConsumed)
            .map(|event|event.path.owner).collect::<HashSet<_>>());
        let mut entry_state=State::default();
        entry_state.monitored_quantum=watched;
        entry_state.phi_groups=Arc::new(self.phi_groups.clone());
        entry_state.phi_roots=Arc::new(self.phi_roots.clone());
        entry_state.phi_reborrows=Arc::new(self.phi_reborrows.clone());
        let mut members=HashMap::<SymbolId,Vec<(SymbolId,u64)>>::new();
        for (&group,choices) in &self.phi_groups {
            for (index,&id) in choices.iter().enumerate() {
                members.entry(id).or_default().push((group,1u64<<index));
            }
        }
        entry_state.phi_members=Arc::new(members);
        if !self.phi_groups.is_empty() {
            entry_state.phi_joint.push(HashSet::new());
        }
        incoming[self.entry]=Some(Arc::new(entry_state));
        let mut queue=VecDeque::from([self.entry]);
        let mut pending=vec![false;self.events.len()];pending[self.entry]=true;
        let mut steps=0usize;
        //During fixed-point propagation Read and QuantumRequireConsumed only validate state; they never change
        //it
        while let Some(node)=queue.pop_front(){
            pending[node]=false;steps+=1;
            if steps>MAX_STEPS {return Err("borrow fixed point exceeded analysis budget".into());}
            let mut state=Arc::clone(incoming[node].as_ref().ok_or("missing incoming borrow state")?);
            for event in &self.events[node] {
                if !matches!(event.op,Access::Read|Access::QuantumRequireConsumed){
                    let _=Arc::make_mut(&mut state).apply(event);
                }
            }
            let successors=&self.successors[node];
            if let [next]=successors.as_slice(){
                if let Some(events)=self.edge_events.get(&(node,*next)){
                    for event in events {
                        if !matches!(event.op,Access::Read|Access::QuantumRequireConsumed){
                            let _=Arc::make_mut(&mut state).apply(event);
                        }
                    }
                }
                let changed=match incoming[*next].as_mut(){
                    Some(existing) if Arc::ptr_eq(existing,&state)=>false,
                    Some(existing) if Arc::strong_count(existing)>1 &&
                        !existing.join_needed(&state)=>false,
                    Some(existing)=>Arc::make_mut(existing).join(&state),
                    None=>{incoming[*next]=Some(state);true},
                };
                if changed && !pending[*next]{queue.push_back(*next);pending[*next]=true;}
            }else{
                for &next in successors {
                    let mut outgoing=Arc::clone(&state);
                    if let Some(events)=self.edge_events.get(&(node,next)){
                        for event in events {
                            if !matches!(event.op,Access::Read|Access::QuantumRequireConsumed){
                                let _=Arc::make_mut(&mut outgoing).apply(event);
                            }
                        }
                    }
                    let changed=match incoming[next].as_mut(){
                        Some(existing) if Arc::ptr_eq(existing,&outgoing)=>false,
                        Some(existing) if Arc::strong_count(existing)>1 &&
                            !existing.join_needed(&outgoing)=>false,
                        Some(existing)=>Arc::make_mut(existing).join(&outgoing),
                        None=>{incoming[next]=Some(outgoing);true},
                    };
                    if changed && !pending[next]{queue.push_back(next);pending[next]=true;}
                }
            }
        }
        Ok(incoming)
    }

    pub fn check(&self)->Result<Vec<Conflict>,String>{
        let incoming=self.propagate()?;
        let mut diagnostics=HashMap::<(usize,usize,String),Conflict>::new();
        for (node,source) in incoming.iter().enumerate(){
            let Some(source)=source else{continue;};
            let events=&self.events[node];
            let only_reads=events.iter().all(|event|
                matches!(event.op,Access::Read|Access::QuantumRequireConsumed));
            let mut owned=if only_reads {None}else{Some((**source).clone())};
            for event in events {
                let message=if let Some(state)=owned.as_mut(){state.apply(event)}
                    else{source.inspect(event)};
                if let Some(message)=message {
                    diagnostics.insert((node,event.token,message.clone()),
                        Conflict{node,token:event.token,message});
                }
            }
            //Edges with only validation events borrow the stabilized state Mutating edges clone once, and never
            //mutate another outgoing branch's snapshot
            for &next in &self.successors[node] {
                if let Some(events)=self.edge_events.get(&(node,next)){
                    let edge_reads=events.iter().all(|event|
                        matches!(event.op,Access::Read|Access::QuantumRequireConsumed));
                    let mut edge_state=if edge_reads {None}else{
                        Some(owned.as_ref().unwrap_or(source.as_ref()).clone())
                    };
                    for event in events {
                        let message=if let Some(state)=edge_state.as_mut(){state.apply(event)}
                            else{owned.as_ref().unwrap_or(source.as_ref()).inspect(event)};
                        if let Some(message)=message {
                            diagnostics.insert((node,event.token,message.clone()),
                                Conflict{node,token:event.token,message});
                        }
                    }
                }
            }
        }
        let mut errors=diagnostics.into_values().collect::<Vec<_>>();
        errors.sort_by(|a,b|(a.token,a.node,&a.message).cmp(&(b.token,b.node,&b.message)));
        Ok(errors)
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    fn key(ty:u32,field:u32)->FieldKey{FieldKey{aggregate:TypeId(ty),field:FieldId(field)}}
    fn path(fields:&[(u32,u32)])->Path{
        let mut p=Path::root(SymbolId(42));
        for &(t,f) in fields {p=p.child(key(t,f));}p
    }
    fn e(op:Access,path:Path,loan:Option<u32>,token:usize)->Event{Event{op,path,loan:loan.map(SymbolId),parent:None,token}}
    #[test]fn join_phi_cases_without_heap_copy_of_incoming_masks(){
        let mut a=State::default();
        let mut b=State::default();
        assert!(!a.join(&b));
        b.phi_presence.insert(SymbolId(10),vec![1,2]);
        assert!(a.join_needed(&b));
        assert!(a.join(&b));
        assert_eq!(a.phi_presence.get(&SymbolId(10)),Some(&vec![0,1,2]));
        assert!(!a.join_needed(&b));
        assert!(!a.join(&b));
        let no_phi=State::default();
        assert!(!a.join_needed(&no_phi));
        assert!(!a.join(&no_phi));
        let mut only_zero=State::default();
        only_zero.phi_presence.insert(SymbolId(20),vec![0]);
        assert!(!a.join_needed(&only_zero));
        assert!(!a.join(&only_zero));
        assert!(!a.phi_presence.contains_key(&SymbolId(20)));
    }
    #[test]fn join_phi_missing_new_predecessor_widens_to_zero(){
        let mut a=State::default();
        a.phi_presence.insert(SymbolId(4),vec![1]);
        assert!(a.join(&State::default()));
        assert_eq!(a.phi_presence.get(&SymbolId(4)),Some(&vec![1,0]));
        let mut other=State::default();
        other.phi_presence.insert(SymbolId(4),vec![2]);
        assert!(a.join(&other));
        assert_eq!(a.phi_presence.get(&SymbolId(4)),Some(&vec![1,0,2]));
    }
    #[test]fn joining_maximum_phi_scenarios_remains_fail_closed(){
        let mut a=State::default();
        a.phi_presence.insert(SymbolId(1),(1..=64).collect());
        let mut b=State::default();
        b.phi_presence.insert(SymbolId(1),vec![65]);
        assert!(a.join(&b));
        assert!(a.phi_presence.get(&SymbolId(1)).unwrap().contains(&0));
    }
    #[test]fn storage_lifetime_requires_initialization(){
        let root=path(&[]);let mut graph=Graph::new(0,vec![vec![]]).unwrap();
        graph.event(0,e(Access::StorageLive,root.clone(),None,0)).unwrap();
        graph.event(0,e(Access::Read,root,None,1)).unwrap();
        assert!(graph.check().unwrap().iter().any(|e|e.message.contains("uninitialized")));
    }
    #[test]fn storage_dead_rejects_live_borrow(){
        let root=path(&[]);let mut graph=Graph::new(0,vec![vec![]]).unwrap();
        graph.event(0,e(Access::BorrowShared,root.clone(),Some(77),0)).unwrap();
        graph.event(0,e(Access::StorageDead,root,None,1)).unwrap();
        assert!(graph.check().unwrap().iter().any(|e|e.message.contains("while borrowed")));
    }
    #[test]fn drop_consumes_owned_value(){
        let root=path(&[]);let mut graph=Graph::new(0,vec![vec![]]).unwrap();
        graph.event(0,e(Access::Drop,root.clone(),None,0)).unwrap();
        graph.event(0,e(Access::Read,root,None,1)).unwrap();
        assert!(!graph.check().unwrap().is_empty());
    }
    #[test]fn host_and_quantum_use_the_same_loan_checker(){
        let root=path(&[]);let mut graph=Graph::new(0,vec![vec![]]).unwrap();
        graph.event(0,e(Access::BorrowShared,root.clone(),Some(77),0)).unwrap();
        graph.event(0,e(Access::Write,root,None,1)).unwrap();
        assert!(graph.check().unwrap().iter().any(|e|e.message.contains("loan conflict")));
    }
    #[test]fn reported_mutable_loan_conflicts_keep_the_conflicting_diagnostic() {
        let root=path(&[]);
        let mut graph=Graph::new(0,vec![vec![]]).unwrap();
        graph.event(0,e(Access::BorrowMut,root.clone(),Some(71),0)).unwrap();
        graph.event(0,e(Access::BorrowMut,root,Some(72),1)).unwrap();
        let conflicts=graph.check().unwrap();
        assert!(conflicts.iter().any(|c| c.token==1 &&
            c.message.contains("conflicting") && c.message.contains("CFG loan conflict")),
            "{conflicts:?}");

        let field=path(&[(1,0)]);
        let mut field_graph=Graph::new(0,vec![vec![]]).unwrap();
        field_graph.event(0,e(Access::BorrowMut,field.clone(),Some(81),0)).unwrap();
        field_graph.event(0,e(Access::BorrowMut,field,Some(82),1)).unwrap();
        let field_conflicts=field_graph.check().unwrap();
        assert!(field_conflicts.iter().any(|c| c.token==1 &&
            c.message.contains("conflicting") && c.message.contains("CFG loan conflict")),
            "{field_conflicts:?}");
    }
    #[test]fn partially_moved_parent_is_not_misreported_as_wholly_uninitialized(){
        let root=path(&[]);
        let left=path(&[(1,0)]);
        let other=path(&[(1,1)]);
        let mut graph=Graph::new(0,vec![vec![1],vec![]]).unwrap();
        graph.event(0,e(Access::Move,left.clone(),None,0)).unwrap();
        graph.event(1,e(Access::Read,root,None,1)).unwrap();
        let errors=graph.check().unwrap();
        assert!(errors.iter().any(|c|c.message.contains("partially moved")),"{errors:?}");
        let mut sibling=Graph::new(0,vec![vec![1],vec![]]).unwrap();
        sibling.event(0,e(Access::Move,left,None,0)).unwrap();
        sibling.event(1,e(Access::Read,other,None,1)).unwrap();
        assert!(sibling.check().unwrap().is_empty());
    }
    #[test]fn repeat_move_of_exact_field_reports_moved_field_not_partial_owner(){
        let field=path(&[(1,0)]);
        let mut graph=Graph::new(0,vec![vec![1],vec![]]).unwrap();
        graph.event(0,e(Access::Move,field.clone(),None,0)).unwrap();
        graph.event(1,e(Access::Move,field,None,1)).unwrap();
        let errors=graph.check().unwrap();
        assert!(errors.iter().any(|d|d.token==1 && d.message.contains("moved field")),"{errors:?}");
        assert!(!errors.iter().any(|d|d.token==1 && d.message.contains("partially moved")),"{errors:?}");
    }
    #[test]fn moved_parent_field_cannot_be_read_through_child_projection(){
        let parent=path(&[(1,0)]);
        let child=path(&[(1,0),(2,1)]);
        let mut graph=Graph::new(0,vec![vec![1],vec![]]).unwrap();
        graph.event(0,e(Access::Move,parent,None,0)).unwrap();
        graph.event(1,e(Access::Read,child,None,1)).unwrap();
        assert!(graph.check().unwrap().iter().any(|d|d.token==1 && d.message.contains("moved field")));
    }
    #[test]fn nested_move_path_ids_and_disjoint_siblings(){
        let mut f=Forest::default();let a=path(&[(1,0),(2,0),(3,2)]);
        let b=path(&[(1,0),(2,1),(3,2)]);
        assert!(!a.overlaps(&b));assert!(path(&[(1,0)]).overlaps(&a));
        let ia=f.intern(&a).unwrap();let ib=f.intern(&b).unwrap();
        assert_ne!(ia,ib);assert_eq!(f.path(ia),Some(&a));assert_eq!(f.nodes().len(),6);
    }
    #[test]fn definite_init_if_join_requires_all_paths(){
        let mut g=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        let p=path(&[(1,0)]);
        g.event(0,e(Access::Move,p.clone(),None,0)).unwrap();
        g.event(1,e(Access::Initialize,p.clone(),None,1)).unwrap();
        g.event(3,e(Access::Read,p,None,3)).unwrap();
        assert!(g.check().unwrap().iter().any(|d|d.token==3));
    }
    #[test]fn match_all_arms_reinitialize_is_safe(){
        let mut g=Graph::new(0,vec![vec![1,2,3],vec![4],vec![4],vec![4],vec![]]).unwrap();
        let p=path(&[(1,0),(2,1)]);
        g.event(0,e(Access::Move,p.clone(),None,0)).unwrap();
        for branch in 1..=3 {g.event(branch,e(Access::Initialize,p.clone(),None,branch)).unwrap();}
        g.event(4,e(Access::Read,p,None,4)).unwrap();
        assert!(g.check().unwrap().is_empty());
    }
    #[test]fn loop_backedge_and_zero_iterations_are_conservative(){
        let mut g=Graph::new(0,vec![vec![1],vec![2,3],vec![1],vec![]]).unwrap();
        let p=path(&[(1,0)]);
        g.event(0,e(Access::Move,p.clone(),None,0)).unwrap();
        g.event(2,e(Access::Initialize,p.clone(),None,2)).unwrap();
        g.event(3,e(Access::Read,p,None,3)).unwrap();
        assert!(!g.check().unwrap().is_empty());
    }
    #[test]fn mutable_loan_blocks_move_and_write_but_not_disjoint_paths(){
        let mut g=Graph::new(0,vec![vec![1],vec![]]).unwrap();
        let left=path(&[(1,0),(2,0)]);let right=path(&[(1,0),(2,1)]);
        g.event(0,e(Access::BorrowMut,left.clone(),Some(1),0)).unwrap();
        g.event(1,e(Access::Write,right,None,1)).unwrap();
        g.event(1,e(Access::Move,left,None,2)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|d|d.token).collect::<Vec<_>>(),vec![2]);
    }
    #[test]fn ending_loan_allows_reinitialization(){
        let mut g=Graph::new(0,vec![vec![]]).unwrap();let p=path(&[(1,0)]);
        g.event(0,e(Access::BorrowShared,p.clone(),Some(5),0)).unwrap();
        g.event(0,e(Access::EndLoan,p.clone(),Some(5),1)).unwrap();
        g.event(0,e(Access::Move,p.clone(),None,2)).unwrap();
        g.event(0,e(Access::Initialize,p.clone(),None,3)).unwrap();
        g.event(0,e(Access::Read,p,None,4)).unwrap();
        assert!(g.check().unwrap().is_empty());
    }
    #[test]fn different_type_ids_do_not_prove_disjointness(){
        assert!(path(&[(1,0)]).overlaps(&path(&[(2,0)])));
    }

    #[test]
    fn readonly_cfg_uses_one_ownership_snapshot_across_large_linear_chain(){
        const N:usize=512;
        let edges=(0..N).map(|i|if i+1<N{vec![i+1]}else{Vec::new()}).collect();
        let mut graph=Graph::new(0,edges).unwrap();
        for id in 1..=48u32 {
            let path=Path::root(SymbolId(id));
            graph.event(0,e(Access::StorageLive,path.clone(),None,id as usize*3)).unwrap();
            graph.event(0,e(Access::Initialize,path.clone(),None,id as usize*3+1)).unwrap();
            graph.event(0,e(Access::BorrowShared,path,Some(id+1000),id as usize*3+2)).unwrap();
        }
        let read=Path::root(SymbolId(7));
        for node in 1..N {
            graph.event(node,e(Access::Read,read.clone(),None,node+1000)).unwrap();
        }
        let incoming=graph.propagate().unwrap();
        let first=incoming[1].as_ref().unwrap();
        for state in incoming.iter().skip(2).flatten(){
            assert!(Arc::ptr_eq(first,state),"read-only node created a deep copy");
        }
        assert!(graph.check().unwrap().is_empty());
    }

    #[test]
    fn a_move_copies_on_write_and_read_after_move_is_still_diagnosed(){
        let mut graph=Graph::new(0,vec![vec![1],vec![2],vec![3],vec![]]).unwrap();
        let path=Path::root(SymbolId(8));
        graph.event(0,e(Access::Initialize,path.clone(),None,0)).unwrap();
        graph.event(1,e(Access::Read,path.clone(),None,1)).unwrap();
        graph.event(2,e(Access::Move,path.clone(),None,2)).unwrap();
        graph.event(3,e(Access::Read,path,None,3)).unwrap();
        let incoming=graph.propagate().unwrap();
        assert!(Arc::ptr_eq(incoming[1].as_ref().unwrap(),incoming[2].as_ref().unwrap()));
        assert!(!Arc::ptr_eq(incoming[2].as_ref().unwrap(),incoming[3].as_ref().unwrap()));
        let errors=graph.check().unwrap();
        assert_eq!(errors.iter().map(|c|c.token).collect::<Vec<_>>(),vec![3]);
    }

    #[test]
    fn cow_branch_join_preserves_may_active_loans(){
        let mut graph=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        let path=Path::root(SymbolId(9));
        graph.event(0,e(Access::Initialize,path.clone(),None,0)).unwrap();
        graph.event(1,e(Access::BorrowShared,path.clone(),Some(90),1)).unwrap();
        graph.event(3,e(Access::Write,path,None,3)).unwrap();
        let incoming=graph.propagate().unwrap();
        assert!(Arc::ptr_eq(incoming[1].as_ref().unwrap(),incoming[2].as_ref().unwrap()));
        let errors=graph.check().unwrap();
        assert_eq!(errors.iter().map(|c|c.token).collect::<Vec<_>>(),vec![3]);
    }

    #[test]
    fn quantum_move_on_one_branch_never_initializes_the_other(){
        let mut graph=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        let qubit=Path::root(SymbolId(101));
        graph.event(0,e(Access::Initialize,qubit.clone(),None,0)).unwrap();
        graph.event(1,e(Access::Move,qubit.clone(),None,1)).unwrap();
        graph.event(2,e(Access::Read,qubit.clone(),None,2)).unwrap();
        graph.event(3,e(Access::Read,qubit,None,3)).unwrap();
        let errors=graph.check().unwrap();
        assert_eq!(errors.iter().map(|c|c.token).collect::<Vec<_>>(),vec![3]);
    }

    #[test]
    fn quantum_consumption_on_cfg_edge_is_not_skipped_by_readonly_propagation(){
        let mut graph=Graph::new(0,vec![vec![1],vec![]]).unwrap();
        let qubit=Path::root(SymbolId(77));
        graph.event(0,e(Access::Initialize,qubit.clone(),None,0)).unwrap();
        graph.event_on_edge(0,1,e(Access::QuantumRequireConsumed,qubit,None,1)).unwrap();
        assert!(graph.check().unwrap().iter().any(|c|
            c.token==1 && c.message.contains("live Qubit")));
    }

    #[test] fn split_uninit_index_matches_original_path_semantics() {
        let mut state=State::default();
        let mut expected=HashSet::<Path>::new();
        let mut paths=Vec::new();
        for owner in 1..=16 {
            let root=Path::root(SymbolId(owner));
            paths.push(root.clone());
            for field in 0..3 {
                let child=root.child(key(1,field));
                paths.push(child.clone());
                paths.push(child.child(key(2,(field+1)%3)));
            }
        }
        for step in 0..512usize {
            let index=(step*37+step/5)%paths.len();
            let chosen=&paths[index];
            if step%5==0 || step%7==0 {
                state.clear_uninit_descendants(chosen);
                expected.retain(|old|!chosen.ancestor_of(old));
            }else{
                state.mark_uninit(chosen);
                expected.insert(chosen.clone());
            }
            for probe in &paths {
                let is_init=!expected.iter().any(|old|old.owner==probe.owner &&
                    (old.ancestor_of(probe)||probe.ancestor_of(old)));
                assert_eq!(state.initialized(probe),is_init,"step {step} path {probe:?}");
                for include_self in [true,false] {
                    let ancestor=expected.iter().any(|old|old.ancestor_of(probe) &&
                        (include_self || old!=probe));
                    assert_eq!(state.has_uninit_ancestor(probe,include_self),ancestor,
                        "step {step} path {probe:?}, include_self={include_self}");
                }
            }
        }
    }

    #[test] fn indexed_reborrows_survive_cfg_join_and_end_child_first() {
        let p=path(&[(1,0)]);
        let mut left=State::default();
        let parent=e(Access::BorrowMut,p.clone(),Some(77),0);
        assert_eq!(left.apply(&parent),None);
        let mut right=left.clone();
        assert_eq!(right.apply(&with_parent(e(Access::BorrowShared,p.clone(),Some(78),1),77)),None);
        assert!(left.join(&right));
        let parent_end=e(Access::EndLoan,p.clone(),Some(77),2);
        assert!(left.apply(&parent_end).unwrap().contains("active reborrow"));
        assert_eq!(left.apply(&e(Access::EndLoan,p.clone(),Some(78),3)),None);
        assert_eq!(left.apply(&parent_end),None);
        assert!(left.loans.is_empty());
        assert!(left.by_parent.is_empty());
        assert!(left.by_owner.is_empty());
    }

    #[test] fn independent_quantum_owners_keep_separate_borrow_conflicts() {
        let mut graph=Graph::new(0,vec![vec![]]).unwrap();
        for i in 1..=48 {
            let p=Path::root(SymbolId(i));
            graph.event(0,e(Access::StorageLive,p.clone(),None,(i*10) as usize)).unwrap();
            graph.event(0,e(Access::Initialize,p.clone(),None,(i*10+1) as usize)).unwrap();
            graph.event(0,e(Access::BorrowMut,p,Some(i+1000),(i*10+2) as usize)).unwrap();
        }
        let unborrowed=Path::root(SymbolId(49));
        graph.event(0,e(Access::StorageLive,unborrowed.clone(),None,490)).unwrap();
        graph.event(0,e(Access::Initialize,unborrowed.clone(),None,491)).unwrap();
        graph.event(0,e(Access::Write,unborrowed,None,492)).unwrap();
        graph.event(0,e(Access::Write,Path::root(SymbolId(1)),None,493)).unwrap();
        let result=graph.check().unwrap();
        assert_eq!(result.iter().map(|c|c.token).collect::<Vec<_>>(),vec![493]);
    }
    fn with_parent(mut event:Event,parent:u32)->Event {
        event.parent=Some(SymbolId(parent));event
    }
    #[test] fn edge_scoped_end_loan_does_not_kill_other_branch() {
        let mut g=Graph::new(0,vec![vec![1,2],vec![],vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::BorrowShared,p.clone(),Some(1),0)).unwrap();
        g.event_on_edge(0,1,e(Access::EndLoan,p.clone(),Some(1),1)).unwrap();
        g.event(1,e(Access::Write,p.clone(),None,2)).unwrap();
        g.event(2,e(Access::Write,p,None,3)).unwrap();
        let errors=g.check().unwrap();
        assert_eq!(errors.iter().map(|error|error.token).collect::<Vec<_>>(),vec![3]);
    }
    #[test] fn edge_specific_reinitialization_must_happen_on_every_path() {
        let mut g=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        let p=path(&[(4,0),(5,2)]);
        g.event(0,e(Access::Move,p.clone(),None,0)).unwrap();
        g.event_on_edge(0,1,e(Access::Initialize,p.clone(),None,1)).unwrap();
        g.event(3,e(Access::Read,p,None,4)).unwrap();
        assert!(g.check().unwrap().iter().any(|error|error.token==4));
    }
    #[test] fn reborrow_parent_is_provenance_not_an_independent_conflict() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(7,0)]);
        g.event(0,e(Access::BorrowMut,p.clone(),Some(1),0)).unwrap();
        g.event(0,with_parent(e(Access::BorrowShared,p.clone(),Some(2),1),1)).unwrap();
        g.event(0,e(Access::Read,p.clone(),Some(2),2)).unwrap();
        g.event(0,e(Access::Read,p.clone(),Some(1),3)).unwrap();
        g.event(0,e(Access::EndLoan,p.clone(),Some(2),4)).unwrap();
        g.event(0,e(Access::Read,p,Some(1),5)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|error|error.token)
            .collect::<Vec<_>>(),vec![3]);
    }
    #[test] fn shared_reference_cannot_spawn_mutable_child() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::BorrowShared,p.clone(),Some(1),0)).unwrap();
        g.event(0,with_parent(e(Access::BorrowMut,p,Some(2),1),1)).unwrap();
        assert!(g.check().unwrap().iter().any(|error|
            error.message.contains("mutably reborrow shared")));
    }
    #[test] fn sibling_shared_reborrows_are_allowed_until_mutable_activation() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::BorrowMut,p.clone(),Some(1),0)).unwrap();
        g.event(0,with_parent(e(Access::BorrowShared,p.clone(),Some(2),1),1)).unwrap();
        g.event(0,with_parent(e(Access::BorrowShared,p.clone(),Some(3),2),1)).unwrap();
        g.event(0,with_parent(e(Access::BorrowMut,p.clone(),Some(4),3),1)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|error|error.token)
            .collect::<Vec<_>>(),vec![3]);
    }
    #[test] fn reference_must_be_active_on_every_join_path() {
        let mut g=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(1,e(Access::BorrowShared,p.clone(),Some(1),1)).unwrap();
        g.event(3,e(Access::Read,p,Some(1),3)).unwrap();
        assert!(g.check().unwrap().iter().any(|error|
            error.message.contains("every CFG path")));
    }
    #[test] fn reference_cannot_write_outside_its_provenance() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let a=path(&[(4,0)]);let b=path(&[(4,1)]);
        g.event(0,e(Access::BorrowMut,a.clone(),Some(1),0)).unwrap();
        g.event(0,e(Access::Write,b,Some(1),1)).unwrap();
        g.event(0,e(Access::Write,a,Some(1),2)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|error|error.token)
            .collect::<Vec<_>>(),vec![1]);
    }
    #[test] fn loan_identity_and_edge_end_ids_are_checked() {
        let mut g=Graph::new(0,vec![vec![1],vec![]]).unwrap();
        let p=path(&[(4,0)]);let q=path(&[(4,1)]);
        assert!(g.event_on_edge(1,0,e(Access::EndLoan,p.clone(),Some(1),0)).is_err());
        g.event(0,e(Access::BorrowShared,p.clone(),Some(1),0)).unwrap();
        assert!(g.event(0,e(Access::BorrowShared,q,Some(1),1)).is_err());
        g.event_on_edge(0,1,e(Access::EndLoan,p,Some(1),2)).unwrap();
        assert!(g.check().unwrap().is_empty());
    }

    #[test] fn invalid_end_loan_does_not_release_a_different_place() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let a=path(&[(4,0)]);let b=path(&[(4,1)]);
        g.event(0,e(Access::BorrowShared,a.clone(),Some(1),0)).unwrap();
        g.event(0,e(Access::EndLoan,b,Some(1),1)).unwrap();
        g.event(0,e(Access::Write,a,None,2)).unwrap();
        let errors=g.check().unwrap();
        assert_eq!(errors.iter().map(|error|error.token).collect::<Vec<_>>(),vec![1,2]);
    }

    #[test] fn reserved_mutable_loan_allows_shared_read_until_activation() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::ReserveMut,p.clone(),Some(1),0)).unwrap();
        g.event(0,e(Access::Read,p.clone(),None,1)).unwrap();
        g.event(0,e(Access::ActivateMut,p.clone(),Some(1),2)).unwrap();
        g.event(0,e(Access::Read,p.clone(),None,3)).unwrap();
        g.event(0,e(Access::Write,p.clone(),Some(1),4)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|d|d.token).collect::<Vec<_>>(),vec![3]);
    }
    #[test] fn reserved_mutable_loan_blocks_other_mutable_access() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::ReserveMut,p.clone(),Some(1),0)).unwrap();
        g.event(0,e(Access::Write,p.clone(),None,1)).unwrap();
        g.event(0,e(Access::ReserveMut,p.clone(),Some(2),2)).unwrap();
        g.event(0,e(Access::Move,p,None,3)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|d|d.token).collect::<Vec<_>>(),vec![1,2,3]);
    }
    #[test] fn implicit_method_receiver_can_reserve_then_read_an_argument() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::ReserveMut,p.clone(),Some(1),0)).unwrap();
        g.event(0,e(Access::BorrowShared,p.clone(),Some(2),1)).unwrap();
        g.event(0,e(Access::Read,p.clone(),Some(2),2)).unwrap();
        g.event(0,e(Access::EndLoan,p.clone(),Some(2),3)).unwrap();
        g.event(0,e(Access::ActivateMut,p.clone(),Some(1),4)).unwrap();
        g.event(0,e(Access::Write,p,Some(1),5)).unwrap();
        assert!(g.check().unwrap().is_empty());
    }
    #[test] fn activation_waits_until_overlapping_shared_loan_ends() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::BorrowShared,p.clone(),Some(1),0)).unwrap();
        g.event(0,e(Access::ReserveMut,p.clone(),Some(2),1)).unwrap();
        g.event(0,e(Access::ActivateMut,p.clone(),Some(2),2)).unwrap();
        g.event(0,e(Access::EndLoan,p.clone(),Some(1),3)).unwrap();
        g.event(0,e(Access::ActivateMut,p.clone(),Some(2),4)).unwrap();
        g.event(0,e(Access::Write,p,Some(2),5)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|d|d.token).collect::<Vec<_>>(),vec![2]);
    }
    #[test] fn write_through_reserved_reference_requires_activation() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::ReserveMut,p.clone(),Some(1),0)).unwrap();
        g.event(0,e(Access::Write,p.clone(),Some(1),1)).unwrap();
        g.event(0,e(Access::ActivateMut,p.clone(),Some(1),2)).unwrap();
        g.event(0,e(Access::Write,p,Some(1),3)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|d|d.token).collect::<Vec<_>>(),vec![1]);
    }
    #[test] fn branch_join_may_activate_mutable_loan() {
        let mut g=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::ReserveMut,p.clone(),Some(1),0)).unwrap();
        g.event(1,e(Access::ActivateMut,p.clone(),Some(1),1)).unwrap();
        g.event(3,e(Access::Read,p,None,3)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|d|d.token).collect::<Vec<_>>(),vec![3]);
    }
    #[test] fn parent_cannot_end_while_reborrow_is_active() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let p=path(&[(4,0)]);
        g.event(0,e(Access::BorrowMut,p.clone(),Some(1),0)).unwrap();
        g.event(0,with_parent(e(Access::BorrowShared,p.clone(),Some(2),1),1)).unwrap();
        g.event(0,e(Access::EndLoan,p.clone(),Some(1),2)).unwrap();
        g.event(0,e(Access::EndLoan,p.clone(),Some(2),3)).unwrap();
        g.event(0,e(Access::EndLoan,p,Some(1),4)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|d|d.token).collect::<Vec<_>>(),vec![2]);
    }
    #[test] fn activation_does_not_allow_mutable_access_outside_reserved_path() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        let a=path(&[(4,0)]);let b=path(&[(4,1)]);
        g.event(0,e(Access::ReserveMut,a.clone(),Some(1),0)).unwrap();
        g.event(0,e(Access::ActivateMut,a.clone(),Some(1),1)).unwrap();
        g.event(0,e(Access::Write,b,Some(1),2)).unwrap();
        assert_eq!(g.check().unwrap().iter().map(|d|d.token).collect::<Vec<_>>(),vec![2]);
    }

}

#[cfg(test)]
mod owner_index_0616_tests {
    use super::*;
    #[test]
    fn large_independent_borrow_set_rejects_only_same_owner_conflict() {
        let mut graph=Graph::new(0,vec![Vec::new()]).unwrap();
        for i in 0..48u32 {
            let path=Path::root(SymbolId(i+1));
            graph.event(0,Event{op:Access::StorageLive,path:path.clone(),loan:None,parent:None,token:i as usize}).unwrap();
            graph.event(0,Event{op:Access::Initialize,path:path.clone(),loan:None,parent:None,token:i as usize}).unwrap();
            graph.event(0,Event{op:Access::BorrowMut,path,loan:Some(SymbolId(100+i)),parent:None,token:i as usize}).unwrap();
        }
        graph.event(0,Event{op:Access::Read,path:Path::root(SymbolId(1)),loan:None,parent:None,token:1000}).unwrap();
        let conflicts=graph.check().unwrap();
        assert!(conflicts.iter().any(|c|c.message.contains("loan conflict")));
    }
}

#[cfg(test)]
mod cfg_compact_0622_tests {
    use super::*;

    #[test]
    fn root_and_projected_move_path_ids_are_stable_and_parented() {
        let mut forest=Forest::default();
        for owner in 0..512u32 {
            let root=Path::root(SymbolId(owner));
            let first=forest.intern(&root).unwrap();
            assert_eq!(first,MovePathId(owner));
            assert_eq!(forest.intern(&root).unwrap(),first);
        }
        assert_eq!(forest.roots.len(),512);
        assert!(forest.ids.is_empty(),"root paths belong only in the compact index");
        let root=Path::root(SymbolId(7));
        let field=root.child(FieldKey{aggregate:TypeId(1),field:FieldId(2)});
        let nested=field.child(FieldKey{aggregate:TypeId(3),field:FieldId(4)});
        let field_id=forest.intern(&field).unwrap();
        let nested_id=forest.intern(&nested).unwrap();
        assert_eq!(forest.nodes[field_id.0 as usize].parent,Some(MovePathId(7)));
        assert_eq!(forest.nodes[nested_id.0 as usize].parent,Some(field_id));
        assert_eq!(forest.intern(&nested).unwrap(),nested_id);
        assert_eq!(forest.nodes.len(),514);
    }

    #[test]
    fn join_preflight_is_equivalent_to_real_may_must_join() {
        let p=Path::root(SymbolId(5));
        let field=p.child(FieldKey{aggregate:TypeId(1),field:FieldId(0)});
        let mut cases=vec![State::default()];
        let mut uninit=State::default();uninit.uninit_roots.insert(p.owner);
        cases.push(uninit);
        let mut projected=State::default();projected.uninit_fields.insert(field.clone());
        cases.push(projected);
        let mut quantum=State::default();quantum.may_live.insert(p.clone());
        cases.push(quantum);
        let mut definite=State::default();definite.definite.insert(SymbolId(99));
        cases.push(definite);
        let mut reserved=State::default();
        reserved.loans.insert(SymbolId(99),Loan{place:p.clone(),exclusive:true,parent:None,reserved:true});
        cases.push(reserved.clone());
        let mut active=reserved.clone();active.loans.get_mut(&SymbolId(99)).unwrap().reserved=false;
        cases.push(active);
        let mut different=reserved;
        different.loans.get_mut(&SymbolId(99)).unwrap().place=field;
        cases.push(different);
        for (a,left) in cases.iter().enumerate() {
            for (b,right) in cases.iter().enumerate() {
                let mut joined=left.clone();
                let actual=joined.join(right);
                assert_eq!(left.join_needed(right),actual,"join mismatch at {a}, {b}");
            }
        }
    }

    #[test]
    fn no_op_diamond_merge_shares_state_and_keeps_loan_conflicts() {
        let p=Path::root(SymbolId(30));
        let mut g=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        g.event(0,Event{op:Access::BorrowMut,path:p.clone(),loan:Some(SymbolId(80)),parent:None,token:0}).unwrap();
        g.event(1,Event{op:Access::Read,path:Path::root(SymbolId(99)),loan:None,parent:None,token:1}).unwrap();
        g.event(3,Event{op:Access::Read,path:p,loan:None,parent:None,token:3}).unwrap();
        let states=g.propagate().unwrap();
        assert!(Arc::ptr_eq(states[1].as_ref().unwrap(),states[3].as_ref().unwrap()));
        assert_eq!(g.check().unwrap().iter().map(|c|c.token).collect::<Vec<_>>(),vec![3]);
    }
}

#[cfg(test)]
mod read_only_0623_tests {
    use super::*;
    fn event(op:Access,owner:u32,loan:Option<u32>,token:usize)->Event{
        Event{op,path:Path::root(SymbolId(owner)),loan:loan.map(SymbolId),parent:None,token}
    }
    #[test]
    fn pure_read_diagnostic_matches_mutable_transfer(){
        let p=Path::root(SymbolId(4));
        let mut cases=vec![State::default()];
        let mut moved=State::default();moved.mark_uninit(&p);cases.push(moved);
        let mut borrowed=State::default();
        borrowed.apply(&event(Access::BorrowMut,4,Some(9),0));
        cases.push(borrowed);
        let events=[event(Access::Read,4,None,1),event(Access::Read,4,Some(9),1),
            event(Access::QuantumRequireConsumed,4,None,1)];
        for state in &cases {for event in &events {
            let mut copy=state.clone();
            assert_eq!(state.inspect(event),copy.apply(event));
            assert_eq!(&copy,state,"read-only verification must not modify state");
        }}
    }
    #[test]
    fn large_readonly_cfg_keeps_reference_and_quantum_diagnostics(){
        let mut g=Graph::new(0,(0..1000).map(|i|if i<999{vec![i+1]}else{vec![]}).collect()).unwrap();
        g.event(0,event(Access::BorrowMut,11,Some(7),0)).unwrap();
        for i in 1..999 {g.event(i,event(Access::Read,11,None,i)).unwrap();}
        assert_eq!(g.check().unwrap().len(),998);
    }
}

#[cfg(test)]
mod phi_path_presence_0625_tests {
    use super::*;
    fn event(op:Access,owner:u32,loan:Option<u32>,token:usize)->Event{
        Event{op,path:Path::root(SymbolId(owner)),loan:loan.map(SymbolId),parent:None,token}
    }
    #[test]
    fn phi_read_rejects_a_group_with_no_ever_created_loan(){
        let mut graph=Graph::new(0,vec![vec![]]).unwrap();
        graph.register_phi_group(SymbolId(40),vec![SymbolId(50),SymbolId(51)]).unwrap();
        graph.event(0,event(Access::Read,40,Some(40),1)).unwrap();
        assert!(graph.check().unwrap().iter().any(|c|c.message.contains("no live provenance")));
    }
    #[test]
    fn phi_read_rejects_a_path_without_any_live_candidate(){
        let mut graph=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        graph.register_phi_group(SymbolId(40),vec![SymbolId(50),SymbolId(51)]).unwrap();
        graph.event(1,event(Access::BorrowShared,1,Some(50),1)).unwrap();
        graph.event(3,event(Access::Read,40,Some(40),3)).unwrap();
        assert!(graph.check().unwrap().iter().any(|c|c.message.contains("no live provenance")));
    }
    #[test]
    fn phi_read_rejects_a_candidate_ended_on_one_path(){
        let mut graph=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        graph.register_phi_group(SymbolId(40),vec![SymbolId(50),SymbolId(51)]).unwrap();
        graph.event(1,event(Access::BorrowShared,1,Some(50),1)).unwrap();
        graph.event(1,event(Access::EndLoan,1,Some(50),2)).unwrap();
        graph.event(2,event(Access::BorrowShared,2,Some(51),2)).unwrap();
        graph.event(3,event(Access::Read,40,Some(40),3)).unwrap();
        assert!(graph.check().unwrap().iter().any(|c|c.message.contains("no live provenance")));
    }
    #[test]
    fn phi_reference_does_not_permit_moving_a_possible_borrowed_qubit(){
        let mut graph=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        graph.register_phi_group(SymbolId(40),vec![SymbolId(50),SymbolId(51)]).unwrap();
        graph.event(1,event(Access::BorrowShared,1,Some(50),1)).unwrap();
        graph.event(2,event(Access::BorrowShared,2,Some(51),2)).unwrap();
        graph.event(3,event(Access::Move,1,None,3)).unwrap();
        assert!(!graph.check().unwrap().is_empty());
    }
}

#[cfg(test)]
mod temporal_phi_exclusivity_0636_tests {
    use super::*;
    #[test]
    fn simultaneous_phis_are_not_confused_with_alternative_generations(){
        let mut graph=Graph::new(0,vec![vec![]]).unwrap();
        graph.register_phi_group(SymbolId(40),vec![SymbolId(50),SymbolId(51)]).unwrap();
        for loan in [50,51] {
            graph.event(0,Event{op:Access::BorrowShared,path:Path::root(SymbolId(1)),
                loan:Some(SymbolId(loan)),parent:None,token:loan as usize}).unwrap();
        }
        graph.event(0,Event{op:Access::Read,path:Path::root(SymbolId(40)),
            loan:Some(SymbolId(40)),parent:None,token:99}).unwrap();
        assert!(graph.check().unwrap().iter().any(|c|
            c.message.contains("ambiguous or forged active provenance")));
    }
}

#[cfg(test)]
mod cross_cfg_phi_joint_0664_tests {
    use super::*;
    fn loan(op:Access,root:u32,id:u32)->Event {
        Event{op,path:Path::root(SymbolId(root)),loan:Some(SymbolId(id)),
            parent:None,token:id as usize}
    }
    #[test]
    fn two_unsynchronized_mutable_phis_keep_four_real_cfg_histories(){
        let mut graph=Graph::new(0,vec![vec![1,2],vec![3],vec![3],
            vec![4,5],vec![6],vec![6],vec![]]).unwrap();
        graph.register_phi_group_for_binding(SymbolId(100),SymbolId(100),
            vec![SymbolId(11),SymbolId(12)]).unwrap();
        graph.register_phi_group_for_binding(SymbolId(200),SymbolId(200),
            vec![SymbolId(21),SymbolId(22)]).unwrap();
        graph.event(1,loan(Access::BorrowMut,1,11)).unwrap();
        graph.event(2,loan(Access::BorrowMut,2,12)).unwrap();
        graph.event(4,loan(Access::BorrowMut,3,21)).unwrap();
        graph.event(5,loan(Access::BorrowMut,4,22)).unwrap();
        graph.event(6,loan(Access::Write,100,100)).unwrap();
        graph.event(6,loan(Access::Write,200,200)).unwrap();
        assert!(graph.check().unwrap().is_empty());
        assert_eq!(graph.propagate().unwrap()[6].as_ref().unwrap().phi_joint.len(),4);
    }
    #[test]
    fn disjoint_actual_histories_are_not_an_unsafe_cartesian_alias(){
        let mut graph=Graph::new(0,vec![vec![1,2],vec![3],vec![4],
            vec![5],vec![5],vec![]]).unwrap();
        graph.register_phi_group_for_binding(SymbolId(100),SymbolId(100),
            vec![SymbolId(11),SymbolId(12)]).unwrap();
        graph.register_phi_group_for_binding(SymbolId(200),SymbolId(200),
            vec![SymbolId(21),SymbolId(22)]).unwrap();
        graph.event(1,loan(Access::BorrowMut,1,11)).unwrap();
        graph.event(2,loan(Access::BorrowMut,2,12)).unwrap();
        graph.event(3,loan(Access::BorrowMut,2,21)).unwrap();
        graph.event(4,loan(Access::BorrowMut,1,22)).unwrap();
        graph.event(5,loan(Access::Write,100,100)).unwrap();
        graph.event(5,loan(Access::Write,200,200)).unwrap();
        let state=graph.propagate().unwrap();
        assert_eq!(state[5].as_ref().unwrap().phi_joint.len(),2);
        assert!(graph.check().unwrap().is_empty());
    }
    #[test]
    fn genuinely_coexisting_exclusive_aliases_still_conflict(){
        let mut graph=Graph::new(0,vec![vec![1,2],vec![3],vec![4],
            vec![5],vec![5],vec![]]).unwrap();
        graph.register_phi_group_for_binding(SymbolId(100),SymbolId(100),
            vec![SymbolId(11),SymbolId(12)]).unwrap();
        graph.register_phi_group_for_binding(SymbolId(200),SymbolId(200),
            vec![SymbolId(21),SymbolId(22)]).unwrap();
        graph.event(1,loan(Access::BorrowMut,1,11)).unwrap();
        graph.event(2,loan(Access::BorrowMut,2,12)).unwrap();
        graph.event(3,loan(Access::BorrowMut,1,21)).unwrap();
        graph.event(4,loan(Access::BorrowMut,1,22)).unwrap();
        graph.event(5,loan(Access::Write,100,100)).unwrap();
        assert!(!graph.check().unwrap().is_empty());
    }
    #[test]
    fn joint_state_join_preflight_matches_real_join(){
        let mut a=State::default();a.phi_joint.push(HashSet::from([SymbolId(1)]));
        let mut b=State::default();b.phi_joint.push(HashSet::from([SymbolId(2)]));
        assert!(a.join_needed(&b));
        assert!(a.join(&b));
        assert!(!a.join_needed(&b));
        assert_eq!(a.phi_joint.len(),2);
    }
    #[test]
    fn cross_cfg_relational_budget_is_fail_closed(){
        let mut a=State::default();
        for i in 0..64u32 {a.phi_joint.push(HashSet::from([SymbolId(i)]));}
        let mut b=State::default();b.phi_joint.push(HashSet::from([SymbolId(99)]));
        assert!(a.join_needed(&b));
        assert!(a.join(&b));
        assert!(a.phi_joint_overflow);
        assert!(a.phi_joint.is_empty());
        let event=loan(Access::Write,100,100);
        assert!(a.inspect_phi(&event,SymbolId(100)).unwrap().contains("budget"));
    }
    #[test]
    fn unknown_non_phi_loan_is_never_pruned_by_correlation(){
        let mut state=State::default();
        state.phi_joint.push(HashSet::from([SymbolId(11)]));
        state.phi_members=Arc::new(HashMap::from([
            (SymbolId(11),vec![(SymbolId(100),1u64)]),
            (SymbolId(12),vec![(SymbolId(100),2u64)]),
        ]));
        assert!(!state.independent_phi_never_cooccurs(SymbolId(11),SymbolId(900)));
        assert!(!state.independent_phi_never_cooccurs(SymbolId(900),SymbolId(11)));
    }
}

#[cfg(test)]
mod late_selected_phi_reborrow_0665_tests {
    use super::*;
    fn e(op:Access,owner:u32,loan:Option<u32>,parent:Option<u32>)->Event{
        Event{op,path:Path::root(SymbolId(owner)),loan:loan.map(SymbolId),
            parent:parent.map(SymbolId),token:20}
    }
    fn graph()->Graph {
        let mut g=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        g.register_phi_group_for_binding(SymbolId(100),SymbolId(100),
            vec![SymbolId(11),SymbolId(12)]).unwrap();
        g.register_phi_group_for_binding(SymbolId(200),SymbolId(200),
            vec![SymbolId(21),SymbolId(22)]).unwrap();
        g.register_phi_reborrow(SymbolId(200),SymbolId(100),vec![
            (SymbolId(11),SymbolId(21),Path::root(SymbolId(1))),
            (SymbolId(12),SymbolId(22),Path::root(SymbolId(2))),
        ]).unwrap();
        for owner in [1,2,100,200] {
            g.event(0,e(Access::Initialize,owner,None,None)).unwrap();
        }
        g.event(1,e(Access::BorrowMut,1,Some(11),None)).unwrap();
        g.event(2,e(Access::BorrowMut,2,Some(12),None)).unwrap();
        g.event(3,e(Access::BindPhiMut,200,Some(200),Some(100))).unwrap();
        g
    }
    #[test]
    fn late_reborrow_inherits_exact_selected_parent_per_history(){
        let mut g=graph();
        g.event(3,e(Access::Write,200,Some(200),None)).unwrap();
        assert!(g.check().unwrap().is_empty());
        let state=g.propagate().unwrap();
        let mut merged=state[3].as_ref().unwrap().as_ref().clone();
        assert_eq!(merged.phi_joint.len(),2);
        assert!(merged.apply(&e(Access::BindPhiMut,200,Some(200),Some(100))).is_none());
        assert_eq!(merged.phi_joint.len(),2);
        for scenario in &merged.phi_joint {
            assert_eq!(scenario.contains(&SymbolId(11)),
                scenario.contains(&SymbolId(21)));
            assert_eq!(scenario.contains(&SymbolId(12)),
                scenario.contains(&SymbolId(22)));
            assert_ne!(scenario.contains(&SymbolId(21)),
                scenario.contains(&SymbolId(22)));
        }
    }
    #[test]
    fn late_children_publish_only_the_selected_member_to_a_future_value_phi(){
        let mut g=graph();
        g.register_phi_group_for_binding(SymbolId(300),SymbolId(300),
            vec![SymbolId(21),SymbolId(22)]).unwrap();
        g.event(0,e(Access::Initialize,300,None,None)).unwrap();
        g.event(3,e(Access::Read,300,Some(300),None)).unwrap();
        assert!(g.check().unwrap().is_empty());
        let incoming=g.propagate().unwrap();
        let mut state=incoming[3].as_ref().unwrap().as_ref().clone();
        assert!(state.apply(&e(Access::BindPhiMut,200,Some(200),Some(100))).is_none());
        let mut masks=state.phi_presence[&SymbolId(300)].clone();
        masks.sort_unstable();
        assert_eq!(masks,vec![1,2]);
        assert!(state.phi_joint.iter().all(|scenario|
            scenario.contains(&SymbolId(21)) != scenario.contains(&SymbolId(22))));
    }
    #[test]
    fn late_projection_preserves_exact_selected_parent_in_joint_histories(){
        let mut g=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![]]).unwrap();
        g.register_phi_group_for_binding(SymbolId(100),SymbolId(100),
            vec![SymbolId(11),SymbolId(12)]).unwrap();
        g.register_phi_group_for_binding(SymbolId(200),SymbolId(200),
            vec![SymbolId(21),SymbolId(22)]).unwrap();
        let key=FieldKey{aggregate:TypeId(9),field:FieldId(2)};
        let a=Path::root(SymbolId(1)).child(key);
        let b=Path::root(SymbolId(2)).child(key);
        g.register_phi_reborrow(SymbolId(200),SymbolId(100),vec![
            (SymbolId(11),SymbolId(21),a.clone()),
            (SymbolId(12),SymbolId(22),b.clone()),
        ]).unwrap();
        for owner in [1,2,100,200]{
            g.event(0,e(Access::Initialize,owner,None,None)).unwrap();
        }
        g.event(1,e(Access::BorrowMut,1,Some(11),None)).unwrap();
        g.event(2,e(Access::BorrowMut,2,Some(12),None)).unwrap();
        g.event(3,e(Access::BindPhiMut,200,Some(200),Some(100))).unwrap();
        g.event(3,e(Access::Write,200,Some(200),None)).unwrap();
        assert!(g.check().unwrap().is_empty());
        let incoming=g.propagate().unwrap();
        let mut state=incoming[3].as_ref().unwrap().as_ref().clone();
        assert!(state.apply(&e(Access::BindPhiMut,200,Some(200),Some(100))).is_none());
        assert_eq!(state.loans[&SymbolId(21)].place,a);
        assert_eq!(state.loans[&SymbolId(22)].place,b);
        for scenario in &state.phi_joint{
            assert_eq!(scenario.contains(&SymbolId(11)),scenario.contains(&SymbolId(21)));
            assert_eq!(scenario.contains(&SymbolId(12)),scenario.contains(&SymbolId(22)));
        }
    }
    #[test]
    fn late_projection_cannot_escape_the_parent_owner(){
        let mut g=graph();
        let key=FieldKey{aggregate:TypeId(9),field:FieldId(2)};
        let forged=Path::root(SymbolId(9)).child(key);
        g.phi_reborrows.get_mut(&SymbolId(200)).unwrap().children[0].2=forged;
        assert!(!g.check().unwrap().is_empty());
    }
    #[test]
    fn source_phi_becomes_suspended_when_child_is_active(){
        let mut g=graph();
        g.event(3,e(Access::Write,100,Some(100),None)).unwrap();
        assert!(g.check().unwrap().iter().any(|c|
            c.message.contains("suspended") || c.message.contains("conflict")));
    }
    #[test]
    fn invented_parent_child_pairing_is_not_registerable(){
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        g.register_phi_group_for_binding(SymbolId(100),SymbolId(100),
            vec![SymbolId(11),SymbolId(12)]).unwrap();
        g.register_phi_group_for_binding(SymbolId(200),SymbolId(200),
            vec![SymbolId(21),SymbolId(22)]).unwrap();
        assert!(g.register_phi_reborrow(SymbolId(200),SymbolId(100),vec![
            (SymbolId(12),SymbolId(21),Path::root(SymbolId(2))),
            (SymbolId(11),SymbolId(22),Path::root(SymbolId(1))),
        ]).is_err());
    }
    #[test]
    fn absent_source_alternative_is_a_failure_not_an_arbitrary_choice(){
        let mut g=graph();
        g.events[2].retain(|event|event.op!=Access::BorrowMut);
        g.event(3,e(Access::Write,200,Some(200),None)).unwrap();
        assert!(!g.check().unwrap().is_empty());
    }
}

#[cfg(test)]
mod nested_phi_nonmember_history_0671_fix1_tests {
    use super::*;
    fn borrow(owner:u32,loan:u32,parent:Option<u32>)->Event {
        Event{op:Access::BorrowMut,path:Path::root(SymbolId(owner)),
            loan:Some(SymbolId(loan)),parent:parent.map(SymbolId),token:loan as usize}
    }
    fn merge_three_arms()->Graph {
        let mut graph=Graph::new(0,vec![vec![1,2,3],vec![4],vec![4],vec![4],vec![]]).unwrap();
        graph.register_phi_group_for_binding(SymbolId(100),SymbolId(100),
            vec![SymbolId(11),SymbolId(12),SymbolId(13)]).unwrap();
        graph.event(1,borrow(1,31,None)).unwrap();
        graph.event(1,borrow(1,11,Some(31))).unwrap();
        graph.event(2,borrow(2,32,None)).unwrap();
        graph.event(2,borrow(2,12,Some(32))).unwrap();
        graph.event(3,borrow(2,33,None)).unwrap();
        graph.event(3,borrow(2,13,Some(33))).unwrap();
        graph.event(4,Event{op:Access::Write,path:Path::root(SymbolId(100)),
            loan:Some(SymbolId(100)),parent:None,token:100}).unwrap();
        graph
    }
    #[test]
    fn branch_local_non_phi_ancestors_do_not_create_phantom_ownership_aliases() {
        let graph=merge_three_arms();
        let incoming=graph.propagate().unwrap();
        let state=incoming[4].as_ref().unwrap();
        assert!(!state.phi_joint_overflow);
        assert_eq!(state.phi_joint.len(),3);
        for scenario in &state.phi_joint {
            let active=(11..=13).filter(|id|scenario.contains(&SymbolId(*id))).count();
            assert_eq!(active,1);
            for (parent,child) in [(31,11),(32,12),(33,13)] {
                assert_eq!(scenario.contains(&SymbolId(parent)),
                    scenario.contains(&SymbolId(child)));
            }
        }
        assert!(graph.check().unwrap().is_empty());
    }
    #[test]
    fn real_overlapping_non_phi_loan_is_not_ignored_by_the_phi_proof() {
        let mut graph=merge_three_arms();
        graph.event(2,borrow(2,39,None)).unwrap();
        assert!(!graph.check().unwrap().is_empty());
    }
}

#[cfg(test)]
mod transitive_phi_nll_0676_tests {
    use super::*;
    fn event(op:Access,owner:u32,loan:Option<u32>,parent:Option<u32>)->Event {
        Event{op,path:Path::root(SymbolId(owner)),loan:loan.map(SymbolId),
            parent:parent.map(SymbolId),token:76}
    }
    fn chain()->Graph {
        let mut g=Graph::new(0,vec![vec![1,2],vec![3],vec![3],vec![4],vec![5],vec![]]).unwrap();
        for (generation,owner,members) in [
            (100,100,vec![11,12]),(200,200,vec![21,22]),(300,300,vec![31,32])
        ] {
            g.register_phi_group_for_binding(SymbolId(generation),SymbolId(owner),
                members.into_iter().map(SymbolId).collect()).unwrap();
        }
        g.register_phi_reborrow(SymbolId(200),SymbolId(100),vec![
            (SymbolId(11),SymbolId(21),Path::root(SymbolId(1))),
            (SymbolId(12),SymbolId(22),Path::root(SymbolId(2))),
        ]).unwrap();
        g.register_phi_reborrow(SymbolId(300),SymbolId(200),vec![
            (SymbolId(21),SymbolId(31),Path::root(SymbolId(1))),
            (SymbolId(22),SymbolId(32),Path::root(SymbolId(2))),
        ]).unwrap();
        for owner in [1,2,100,200,300] {
            g.event(0,event(Access::Initialize,owner,None,None)).unwrap();
        }
        g.event(1,event(Access::BorrowMut,1,Some(11),None)).unwrap();
        g.event(2,event(Access::BorrowMut,2,Some(12),None)).unwrap();
        g.event(3,event(Access::BindPhiMut,200,Some(200),Some(100))).unwrap();
        g.event(4,event(Access::BindPhiMut,300,Some(300),Some(200))).unwrap();
        g
    }
    fn selected_state()->State {
        let state=chain().propagate().unwrap();
        state[5].as_ref().unwrap().as_ref().clone()
    }
    #[test]
    fn two_late_call_boundaries_keep_each_exact_ancestor_chain() {
        let mut g=chain();
        g.event(5,event(Access::Write,300,Some(300),None)).unwrap();
        assert!(g.check().unwrap().is_empty());
        let state=selected_state();
        assert_eq!(state.phi_joint.len(),2);
        for scenario in &state.phi_joint {
            for chain in [[11,21,31],[12,22,32]] {
                let present=chain.map(|id|scenario.contains(&SymbolId(id)));
                assert!(present.iter().all(|selected|*selected==present[0]));
            }
            assert_ne!(scenario.contains(&SymbolId(31)),
                scenario.contains(&SymbolId(32)));
        }
    }
    #[test]
    fn grandchild_cannot_use_an_ancestor_missing_from_its_real_history() {
        let mut state=selected_state();
        let first=state.phi_joint.iter_mut().find(|set|set.contains(&SymbolId(31))).unwrap();
        first.remove(&SymbolId(11));
        let issue=state.inspect_phi(&event(Access::Read,300,Some(300),None),SymbolId(300));
        assert!(issue.unwrap().contains("ancestor"));
    }
    #[test]
    fn returned_phi_mask_cannot_omit_a_still_feasible_history() {
        let mut state=selected_state();
        state.phi_presence.insert(SymbolId(300),vec![1]);
        assert!(state.inspect_phi(&event(Access::Read,300,Some(300),None),SymbolId(300))
            .unwrap().contains("disagrees"));
    }
    #[test]
    fn invented_joint_history_cannot_be_used_as_an_effect_witness() {
        let mut state=selected_state();
        state.phi_joint.push(HashSet::from([SymbolId(31),SymbolId(32)]));
        assert!(state.inspect_phi(&event(Access::Read,300,Some(300),None),SymbolId(300))
            .is_some());
    }
    #[test]
    fn earlier_interprocedural_phi_is_suspended_by_grandchild() {
        let mut g=chain();
        g.event(5,event(Access::Write,200,Some(200),None)).unwrap();
        assert!(!g.check().unwrap().is_empty());
    }
    #[test]
    fn original_input_phi_is_suspended_by_transitive_return() {
        let mut g=chain();
        g.event(5,event(Access::Write,100,Some(100),None)).unwrap();
        assert!(!g.check().unwrap().is_empty());
    }
    #[test]
    fn ending_a_parent_before_its_grandchild_is_rejected() {
        let mut g=chain();
        g.event(5,event(Access::EndLoan,1,Some(11),None)).unwrap();
        assert!(g.check().unwrap().iter().any(|issue|
            issue.message.contains("active reborrow")));
    }
    #[test]
    fn child_before_parent_lifetime_end_restores_both_owners() {
        let mut g=chain();
        for (owner,id) in [(1,31),(2,32),(1,21),(2,22),(1,11),(2,12)] {
            g.event(5,event(Access::EndLoan,owner,Some(id),None)).unwrap();
        }
        for owner in [1,2] {
            g.event(5,event(Access::Write,owner,None,None)).unwrap();
        }
        assert!(g.check().unwrap().is_empty());
    }
    #[test]
    fn transitive_child_cannot_switch_to_a_sibling_move_path() {
        let mut g=chain();
        g.phi_reborrows.get_mut(&SymbolId(300)).unwrap().children[0].2=
            Path::root(SymbolId(2));
        assert!(!g.check().unwrap().is_empty());
    }
    #[test]
    fn middle_generation_cannot_claim_wrong_parent_loan() {
        let mut g=chain();
        g.phi_reborrows.get_mut(&SymbolId(300)).unwrap().children[0].0=SymbolId(22);
        assert!(!g.check().unwrap().is_empty());
    }
}

#[cfg(test)]
mod statement_boundary_nll_0688_tests {
    use super::*;
    fn ev(op:Access,path:Path,loan:Option<u32>,token:usize)->Event {
        Event{op,path,loan:loan.map(SymbolId),parent:None,token}
    }
    #[test]
    fn synthetic_end_is_inserted_before_the_next_statement_not_at_block_tail() {
        let p=Path::root(SymbolId(901));
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        g.event(0,ev(Access::BorrowMut,p.clone(),Some(300),0)).unwrap();
        g.event(0,ev(Access::Read,p.clone(),Some(300),1)).unwrap();
        g.event(0,ev(Access::Write,p.clone(),None,2)).unwrap();
        g.event_at(0,2,ev(Access::EndLoan,p,Some(300),3)).unwrap();
        assert!(g.check().unwrap().is_empty());
    }
    #[test]
    fn synthetic_end_rejects_an_invalid_event_position() {
        let mut g=Graph::new(0,vec![vec![]]).unwrap();
        assert!(g.event_at(0,1,ev(Access::EndLoan,
            Path::root(SymbolId(901)),Some(300),0)).is_err());
    }
}
