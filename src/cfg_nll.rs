//Function-local, backward CFG reference liveness for QRust's typed host layer
use std::{collections::{HashMap, HashSet, VecDeque}, ops::Range, cell::RefCell, time::{Duration, Instant}};
use crate::{ids::SymbolId, ir::{Place,FieldId,TypeId}, region_infer::{LocalRegionInference,RegionId},
    syntax::{Token, TokenKind as K}};

//Per-stage timing is opt-in and thread-local; ordinary builds omit individual region timers
#[derive(Clone, Debug, Default)]
pub struct RegionProfile {
    pub plans: usize,
    pub successful_cfg: usize,
    pub nodes: usize,
    pub loans: usize,
    pub edges: usize,
    pub events: usize,
    pub edge_worklist_steps: usize,
    pub place_accesses: usize,
    pub binding: Duration,
    pub cfg_build: Duration,
    pub backward_liveness: Duration,
    pub region_solve: Duration,
    pub edge_events_and_forward: Duration,
}
thread_local! { static REGION_METRICS: RefCell<Option<RegionProfile>> = const { RefCell::new(None) }; }
pub fn begin_region_profile() { REGION_METRICS.with(|p|*p.borrow_mut()=Some(RegionProfile::default())); }
pub fn finish_region_profile()->RegionProfile {
    REGION_METRICS.with(|p|p.borrow_mut().take().unwrap_or_default())
}
fn region_profile_enabled()->bool { REGION_METRICS.with(|p|p.borrow().is_some()) }
fn commit_region_profile(other:RegionProfile) {
    REGION_METRICS.with(|slot|{
        if let Some(p)=slot.borrow_mut().as_mut() {
            p.plans+=other.plans;p.successful_cfg+=other.successful_cfg;
            p.nodes+=other.nodes;p.loans+=other.loans;p.edges+=other.edges;
            p.events+=other.events;p.edge_worklist_steps+=other.edge_worklist_steps;
            p.place_accesses+=other.place_accesses;
            p.binding+=other.binding;p.cfg_build+=other.cfg_build;
            p.backward_liveness+=other.backward_liveness;
            p.region_solve+=other.region_solve;
            p.edge_events_and_forward+=other.edge_events_and_forward;
        }
    });
}
fn observed_elapsed(start:Option<Instant>)->Duration {
    start.map_or(Duration::ZERO, |t|t.elapsed())
}

const NODE_LIMIT: usize = 8192;
const DEPTH_LIMIT: usize = 64;
const WORK_LIMIT: usize = 2_000_000;
const EDGE_EVENT_LIMIT: usize = 1_000_000;
const TYPED_ACCESS_LIMIT: usize = 32_768;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CfgPointId(pub u32);

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct LocalRegion {
    pub binding: SymbolId,
    pub owner: SymbolId,
    pub place: Place,
    pub points: HashSet<CfgPointId>,
}
#[allow(dead_code)]
impl LocalRegion {
    pub fn overlaps(&self, rhs: &Self) -> bool {
        self.owner == rhs.owner && self.place.overlaps(rhs.place) &&
            self.points.iter().any(|point| rhs.points.contains(point))
    }
}

fn match_pattern_arms<'a>(tokens:&[Token<'a>], start:usize, limit:usize)
    ->Option<(&'a str,bool,Vec<(usize,Vec<(usize,&'a str,bool,bool)>)>)>{
    let mut cursor=start+1;
    let borrowed=tokens.get(cursor)?.kind==K::Amp;
    if borrowed {cursor+=1;}
    if borrowed && tokens.get(cursor)?.kind==K::Ident("mut") {cursor+=1;}
    let subject=match tokens.get(cursor)?.kind {K::Ident(name)=>name,_=>return None};
    cursor+=1;
    if tokens.get(cursor)?.kind!=K::LBrace{return None;}
    cursor+=1;
    let mut arms=Vec::new();
    while cursor<limit && tokens[cursor].kind!=K::RBrace {
        let (pattern,mut arrow)=crate::typed_patterns::parse(tokens,cursor,limit)?;
        let mut names=Vec::new();
        crate::typed_patterns::collect_bindings(&pattern,&mut names);
        //A guard has its own uses, never declarations; the borrowing frontend rejects guards that inspect
        //payload bindings for now
        if tokens.get(arrow)?.kind==K::Ident("if") {
            arrow+=1;
            if !matches!(tokens.get(arrow)?.kind,K::Ident(_)){return None;}
            arrow+=1;
        }
        if tokens.get(arrow)?.kind!=K::FatArrow{return None;}
        let arm_open=arrow+1;
        if tokens.get(arm_open)?.kind!=K::LBrace{return None;}
        arms.push((arm_open,names));
        cursor=arm_open;
        let mut braces=0usize;
        while cursor<limit {
            match tokens[cursor].kind {
                K::LBrace=>braces+=1,
                K::RBrace=>{
                    braces=braces.checked_sub(1)?;
                    if braces==0{cursor+=1;break;}
                },
                _=>(),
            }
            cursor+=1;
        }
        if braces!=0{return None;}
        if tokens.get(cursor).is_some_and(|t|t.kind==K::Comma){cursor+=1;}
    }
    if tokens.get(cursor)?.kind!=K::RBrace{return None;}
    Some((subject,borrowed,arms))
}

#[derive(Debug)]
struct Bindings {
    uses: HashMap<usize, SymbolId>,
    declarations: HashMap<usize, SymbolId>,
    name_by_id: HashMap<SymbolId, String>,
    origins: HashMap<SymbolId, SymbolId>,
    loan_kinds: HashMap<SymbolId, crate::region_infer::LoanKind>,
    root_only_loans: HashSet<SymbolId>,
    //An arm's entry node defines its own pattern locals. An unrelated arm cannot gain access to these
    //bindings or inherit their loans
    arm_bindings: HashMap<usize,Vec<SymbolId>>,
    pattern_loan_ids: HashSet<SymbolId>,
}
impl Bindings {
    fn new<'a>(tokens: &[Token<'a>], range: Range<usize>, parameters: &[(String, SymbolId)]) -> Option<Self> {
        let mut scopes: Vec<Vec<(&str,Option<SymbolId>)>> = vec![Vec::new()];
        let mut active: HashMap<&str,SymbolId> = HashMap::new();
        let mut name_by_id = HashMap::new();
        for (name,id) in parameters {
            active.insert(name.as_str(),*id);
            name_by_id.insert(*id,name.clone());
        }
        let mut uses=HashMap::new();
        let mut declarations=HashMap::new();
        let mut origins=HashMap::new();
        let mut loan_kinds=HashMap::new();
        let mut root_only_loans=HashSet::new();
        let mut externals=HashMap::<&str,SymbolId>::new();
        let mut delayed: Option<(&str,SymbolId,usize)> = None;
        let mut for_scopes=HashMap::<usize,(&str,SymbolId)>::new();
        let mut pattern_at_brace=HashMap::<usize,Vec<(&str,SymbolId)>>::new();
        let mut arm_bindings=HashMap::<usize,Vec<SymbolId>>::new();
        let mut pattern_loan_ids=HashSet::new();
        for i in range.clone() {
            if tokens[i].kind==K::Ident("for") {
                if let Some(K::Ident(name))=tokens.get(i+1).map(|t|t.kind) {
                    let mut paren=0usize;
                    for j in i+2..range.end {
                        match tokens[j].kind {
                            K::LParen=>paren+=1,
                            K::RParen=>paren=paren.saturating_sub(1),
                            K::LBrace if paren==0=>{for_scopes.insert(j,(name,SymbolId((i+2) as u32)));break;},
                            _=>()
                        }
                    }
                }
            }
        }
        let mut next_external=usize::max(tokens.len()+parameters.len()+2,range.end+2);
        for i in range.clone() {
            if tokens[i].kind==K::Ident("match") {
                if let Some((subject,_borrowed,arms))=
                    match_pattern_arms(tokens,i,range.end) {
                    let owner=active.get(subject).copied();
                    for (open,names) in arms {
                        for (token,name,is_ref,is_mut) in names {
                            let id=SymbolId(u32::try_from(token+1).ok()?);
                            declarations.insert(token,id);
                            name_by_id.insert(id,name.to_owned());
                            pattern_at_brace.entry(open).or_default().push((name,id));
                            arm_bindings.entry(open+1).or_default().push(id);
                            //Owned `match e { E::V(ref x, ref mut y, z) => ... }` creates real loans too. Their origins and regions
                            //must be tracked just like `match &mut e` loans
                            if is_ref {
                                if let Some(owner)=owner {
                                    origins.insert(id,owner);
                                    loan_kinds.insert(id,if is_mut {
                                        crate::region_infer::LoanKind::Exclusive
                                    }else{crate::region_infer::LoanKind::Shared});
                                    pattern_loan_ids.insert(id);
                                }
                            }
                        }
                    }
                }
            }
            match tokens[i].kind {
                K::LBrace=>{
                    scopes.push(Vec::new());
                    if let Some((name,id))=for_scopes.get(&i) {
                        let previous=active.insert(*name,*id);
                        scopes.last_mut()?.push((*name,previous));
                        name_by_id.insert(*id,(*name).into());
                    }
                    if let Some(names)=pattern_at_brace.get(&i) {
                        for &(name,id) in names {
                            let previous=active.insert(name,id);
                            scopes.last_mut()?.push((name,previous));
                        }
                    }
                },
                K::RBrace=>{
                    if scopes.len()<=1 {return None;}
                    for (name,previous) in scopes.pop()?.into_iter().rev() {
                        if let Some(id)=previous {active.insert(name,id);}
                        else {active.remove(name);}
                    }
                },
                _=>(),
            }
            let is_let=matches!(tokens[i].kind,K::Ident("let"|"const"));
            if is_let {
                let pos=i+usize::from(tokens.get(i+1).is_some_and(|t|t.kind==K::Ident("mut")))+1;
                if let Some(K::Ident(name))=tokens.get(pos).map(|t|t.kind) {
                    let id=SymbolId(u32::try_from(pos+1).ok()?);
                    declarations.insert(pos,id);
                    name_by_id.insert(id,name.to_owned());
                    delayed=Some((name,id,pos));
                }
            }
            if let K::Ident(name)=tokens[i].kind {
                if declarations.contains_key(&i) || (i>range.start && tokens[i-1].kind==K::Dot) {continue;}
                if let Some(id)=active.get(name).copied() {
                    uses.insert(i,id);
                } else {
                    let id=if let Some(id)=externals.get(name){*id}else{
                        let id=SymbolId(u32::try_from(next_external).ok()?);next_external+=1;
                        externals.insert(name,id);name_by_id.insert(id,name.to_owned());id
                    };
                    uses.insert(i,id);
                }
            }
            if tokens[i].kind==K::Semi {
                if let Some((name,id,_))=delayed.take() {
                    let previous=active.insert(name,id);
                    scopes.last_mut()?.push((name,previous));
                }
            }
        }
        let pattern_ids=arm_bindings.values().flat_map(|ids|ids.iter().copied())
            .collect::<HashSet<_>>();
        //The referent of a new local reference is the owner, not the name of its lease. Ambiguous expressions
        //keep the conservative root place
        for (&at,&id) in &declarations {
            if pattern_ids.contains(&id){continue;}
            let mut i=at+1;
            while i<range.end && !matches!(tokens[i].kind,K::Equal|K::Semi) {i+=1;}
            if i<range.end && tokens[i].kind==K::Equal {
                i+=1;
                if i<range.end && tokens[i].kind==K::Amp {
                    i+=1;
                    let exclusive=i<range.end && tokens[i].kind==K::Ident("mut");
                    if exclusive {i+=1;}
                    if i<range.end && tokens[i].kind==K::Star {i+=1;}
                    if let Some(&owner)=uses.get(&i){
                        origins.insert(id,owner);
                        if !matches!(tokens.get(i+1).map(|t|t.kind),Some(K::Dot))
                            && tokens.get(i-1).is_some_and(|t|t.kind!=K::Star) {
                            root_only_loans.insert(id);
                        }
                        loan_kinds.insert(id,if exclusive {
                            crate::region_infer::LoanKind::Exclusive
                        } else {crate::region_infer::LoanKind::Shared});
                    }
                }
            }
        }
        Some(Self{uses,declarations,name_by_id,origins,loan_kinds,
            root_only_loans,arm_bindings,pattern_loan_ids})
    }
}


#[derive(Debug)]
struct Node {
    span: Range<usize>,
    uses: HashSet<SymbolId>,
    defines: HashSet<SymbolId>,
    successors: Vec<usize>,
    live_in: HashSet<SymbolId>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlaceAccessKind { Read, Write, Move, BorrowShared, BorrowExclusive }
impl PlaceAccessKind {
    fn conflicts_with(self,loan:crate::region_infer::LoanKind)->bool {
        use crate::region_infer::LoanKind;
        match self {
            Self::Read|Self::BorrowShared=>loan==LoanKind::Exclusive,
            Self::Write|Self::Move|Self::BorrowExclusive=>true,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypedFieldId { pub aggregate: TypeId, pub field: FieldId }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypedPlace { pub owner: SymbolId, pub field: Option<TypedFieldId> }
impl TypedPlace {
    pub fn new(owner:SymbolId,aggregate:Option<TypeId>,place:Place)->Option<Self> {
        let field=match place {
            Place::Root=>None,
            Place::Field(field)=>Some(TypedFieldId{aggregate:aggregate?,field}),
            Place::Deep(_)=>return None,
        };
        Some(Self{owner,field})
    }
    //Mismatched aggregate types cannot prove disjointness; a root overlaps every projection and distinct
    //verified fields do not overlap
    pub fn overlaps(self,other:Self)->bool {
        if self.owner!=other.owner{return false;}
        match (self.field,other.field) {
            (Some(a),Some(b)) if a.aggregate==b.aggregate=>a.field==b.field,
            _=>true,
        }
    }
    pub fn raw_place(self)->Place {self.field.map_or(Place::Root,|f|Place::Field(f.field))}
}

#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub struct TypedPlacePath {
    pub owner:SymbolId,
    pub fields:Vec<TypedFieldId>,
}
impl TypedPlacePath {
    pub fn from_verified(path:&crate::cfg_borrow::Path)->Option<Self>{
        if path.fields.len()>64{return None;}
        Some(Self {owner:path.owner,fields:path.fields.iter().map(|field|
            TypedFieldId{aggregate:field.aggregate,field:field.field}).collect()})
    }
    #[allow(dead_code)]
    pub fn parent(&self)->Option<Self>{
        let (_,rest)=self.fields.split_last()?;
        Some(Self{owner:self.owner,fields:rest.to_vec()})
    }
    #[allow(dead_code)]
    pub fn ancestor_of(&self,other:&Self)->bool{
        self.owner==other.owner && self.fields.len()<=other.fields.len() &&
            self.fields.iter().zip(&other.fields).all(|(a,b)|a==b)
    }
    pub fn overlaps(&self,other:&Self)->bool {
        if self.owner!=other.owner{return false;}
        for (a,b) in self.fields.iter().zip(&other.fields){
            if a.aggregate!=b.aggregate{return true;} //Fail closed
            if a.field!=b.field{return false;}
        }
        true
    }
    #[allow(dead_code)]
    pub fn raw_place(&self)->Option<Place>{
        Place::from_fields(&self.fields.iter().map(|f|f.field).collect::<Vec<_>>())
    }
    pub fn matches_verified(&self,path:&crate::cfg_borrow::Path)->bool {
        self.owner==path.owner && self.fields.len()==path.fields.len() &&
            self.fields.iter().zip(&path.fields).all(|(a,b)|
                a.aggregate==b.aggregate && a.field==b.field)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MovePathNode {
    pub id: crate::ir::MovePathId,
    pub place: TypedPlace,
    pub parent: Option<crate::ir::MovePathId>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MovePathEventKind { Initialize, Move }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MovePathEvent {
    pub path: crate::ir::MovePathId,
    pub point: CfgPointId,
    pub kind: MovePathEventKind,
}
#[derive(Debug, Default)]
pub struct MovePathForest {
    nodes: Vec<MovePathNode>,
    by_root: HashMap<SymbolId, crate::ir::MovePathId>,
    by_place: HashMap<TypedPlace, crate::ir::MovePathId>,
}
impl MovePathForest {
    pub fn intern(&mut self,place:TypedPlace)->Option<crate::ir::MovePathId>{
        if place.field.is_none() {
            if let Some(&id)=self.by_root.get(&place.owner){return Some(id);}
            let id=crate::ir::MovePathId(u32::try_from(self.nodes.len()).ok()?);
            self.nodes.push(MovePathNode{id,place,parent:None});
            self.by_root.insert(place.owner,id);
            return Some(id);
        }
        if let Some(&id)=self.by_place.get(&place){return Some(id);}
        let parent=Some(self.intern(TypedPlace{owner:place.owner,field:None})?);
        let id=crate::ir::MovePathId(u32::try_from(self.nodes.len()).ok()?);
        self.nodes.push(MovePathNode{id,place,parent});
        self.by_place.insert(place,id);
        Some(id)
    }
    #[cfg(test)]
    pub fn get(&self,place:TypedPlace)->Option<crate::ir::MovePathId>{
        if place.field.is_none() {self.by_root.get(&place.owner).copied()}
        else {self.by_place.get(&place).copied()}
    }
    #[cfg(test)]
    pub fn nodes(&self)->&[MovePathNode]{&self.nodes}
}

//A type-checked move/write/read attached to the executing CFG statement Unlike source-level candidates,
//a Move entry cannot represent a Copy read
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TypedPlaceAccess {
    pub point: CfgPointId,
    pub token: usize,
    pub place: TypedPlace,
    pub kind: PlaceAccessKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlaceEdgeAccess {
    pub point: CfgPointId,
    pub token: usize,
    pub owner: SymbolId,
    pub kind: PlaceAccessKind,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlaceEdgeConflict {
    pub access: PlaceEdgeAccess,
    pub loan: SymbolId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoanEdgeEventKind { Create, Activate, Invalidate }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoanEdgeEvent {
    pub loan: SymbolId,
    pub kind: LoanEdgeEventKind,
}

#[derive(Clone, Debug)]
pub struct LoanEdge {
    pub from: CfgPointId,
    pub to: CfgPointId,
    pub events: Vec<LoanEdgeEvent>,
}

#[derive(Clone, Debug, Default)]
pub struct EdgeLoanAnalysis {
    pub edges: Vec<LoanEdge>,
    active_in: Vec<HashSet<SymbolId>>,
    reachable: Vec<bool>,
    #[allow(dead_code)]
    pub iterations: usize,
}

impl EdgeLoanAnalysis {
    fn build(nodes: &[Node], entry: usize,
        origins: &HashMap<SymbolId,SymbolId>,
        regions: Option<&LocalRegionInference>,
        region_ids: &HashMap<SymbolId,RegionId>) -> Option<Self> {
        if entry>=nodes.len() {return None;}
        let mut point_live=nodes.iter().map(|node|node.live_in.iter()
            .filter(|id|origins.contains_key(*id)).copied().collect::<HashSet<_>>())
            .collect::<Vec<_>>();
        if let Some(regions)=regions {
            for (&binding,&region_id) in region_ids {
                if let Some(region)=regions.get(region_id) {
                    for &CfgPointId(point) in &region.points {
                        if let Some(set)=point_live.get_mut(point as usize) {
                            set.insert(binding);
                        }
                    }
                }
            }
        }
        let mut edges=Vec::new();
        let mut total_events=0usize;
        for (from,node) in nodes.iter().enumerate() {
            for &to in &node.successors {
                let mut events=Vec::new();
                let mut creates=node.defines.iter().filter(|id|origins.contains_key(id))
                    .copied().collect::<Vec<_>>();
                creates.sort_unstable_by_key(|id|id.0);
                for loan in creates {
                    events.push(LoanEdgeEvent{loan,kind:LoanEdgeEventKind::Create});
                    events.push(LoanEdgeEvent{loan,kind:LoanEdgeEventKind::Activate});
                }
                //Only a loan visible at the source (or created here) can die on this edge. Do not emit a quadratic list
                //of unrelated invalidations on every branch in a large function
                let mut kills=point_live[from].iter().chain(node.defines.iter())
                    .filter(|&&id|origins.contains_key(&id) && !point_live[to].contains(&id))
                    .copied().collect::<Vec<_>>();
                kills.sort_unstable_by_key(|id|id.0);
                kills.dedup();
                for loan in kills {
                    events.push(LoanEdgeEvent{loan,kind:LoanEdgeEventKind::Invalidate});
                }
                total_events=total_events.checked_add(events.len())?;
                if total_events>EDGE_EVENT_LIMIT {return None;}
                edges.push(LoanEdge{from:CfgPointId(from as u32),
                    to:CfgPointId(to as u32),events});
            }
        }
        let mut active_in=vec![HashSet::new();nodes.len()];
        let mut reachable=vec![false;nodes.len()];
        let mut pending=VecDeque::new();
        pending.push_back(entry);
        let mut queued=vec![false;nodes.len()];
        queued[entry]=true;
        reachable[entry]=true;
        let mut iterations=0;
        let mut outgoing=vec![Vec::new();nodes.len()];
        for (i,e) in edges.iter().enumerate(){outgoing[e.from.0 as usize].push(i);}
        while let Some(from)=pending.pop_front() {
            queued[from]=false;
            iterations+=1;
            if iterations>WORK_LIMIT{return None;}
            for &e in &outgoing[from] {
                let edge=&edges[e];
                let to=edge.to.0 as usize;
                let mut state=active_in[from].clone();
                for event in &edge.events {
                    match event.kind {
                        LoanEdgeEventKind::Create=>{},
                        LoanEdgeEventKind::Activate=>{state.insert(event.loan);},
                        LoanEdgeEventKind::Invalidate=>{state.remove(&event.loan);},
                    }
                }
                let was_reached=reachable[to];
                reachable[to]=true;
                let old=active_in[to].len();
                active_in[to].extend(state);
                if (!was_reached||old!=active_in[to].len())&&!queued[to] {
                    pending.push_back(to);queued[to]=true;
                }
            }
        }
        Some(Self{edges,active_in,reachable,iterations})
    }
    pub fn maybe_active_at(&self,point:CfgPointId,loan:SymbolId)->Option<bool>{
        let i=point.0 as usize;
        if !*self.reachable.get(i)? {return None;}
        Some(self.active_in.get(i)?.contains(&loan))
    }
    #[allow(dead_code)]
    pub fn outgoing(&self,point:CfgPointId)->impl Iterator<Item=&LoanEdge>{
        self.edges.iter().filter(move |edge|edge.from==point)
    }
}

#[derive(Debug)]
enum Shape {
    Plain(Range<usize>),
    If { arms: Vec<(Option<Range<usize>>, Range<usize>)>, end: usize },
    Match { head: Range<usize>, arms: Vec<Range<usize>>, end: usize },
    Loop { header: Range<usize>, body: Range<usize>, end: usize, conditional: bool },
}
impl Shape {
    fn end(&self)->usize {match self { Self::Plain(r)=>r.end,
        Self::If{end,..}|Self::Match{end,..}|Self::Loop{end,..}=>*end}}
}
#[derive(Clone,Copy)]
struct LoopTargets { break_to: usize, continue_to: usize }
struct Builder<'t,'a> {
    tokens: &'t [Token<'a>], nodes: Vec<Node>,
    after: HashMap<usize,usize>,
    bindings: Bindings,
    pattern_entry_points: HashMap<usize,usize>,
}
impl<'t,'a> Builder<'t,'a> {
    fn kind(&self,i:usize)->Option<K<'a>> {self.tokens.get(i).map(|t|t.kind)}
    fn brace_end(&self,open:usize,limit:usize)->Option<usize>{
        if self.kind(open)!=Some(K::LBrace){return None;}
        let mut nesting=0usize;
        for i in open..limit {
            match self.kind(i)? {
                K::LBrace => nesting+=1,
                K::RBrace => {nesting-=1;if nesting==0{return Some(i);}},
                _=>(),
            }
        }
        None
    }
    fn body_open(&self,start:usize,end:usize)->Option<usize>{
        let mut parens=0usize;
        for i in start..end {
            match self.kind(i)? {
                K::LParen=>parens+=1,
                K::RParen=>parens=parens.saturating_sub(1),
                K::LBrace if parens==0=>return Some(i),
                _=>(),
            }
        }
        None
    }
    fn parse_if(&self,start:usize,limit:usize)->Option<Shape>{
        let mut i=start;let mut arms=Vec::new();
        loop {
            if self.kind(i)!=Some(K::Ident("if")){return None;}
            let open=self.body_open(i+1,limit)?;
            let close=self.brace_end(open,limit)?;
            arms.push((Some(i..open),open+1..close));
            i=close+1;
            if self.kind(i)!=Some(K::Ident("else")){break;}
            if self.kind(i+1)==Some(K::Ident("if")){i+=1;continue;}
            let close=self.brace_end(i+1,limit)?;
            arms.push((None,i+2..close));
            i=close+1;break;
        }
        Some(Shape::If{arms,end:i})
    }
    fn parse_match(&self,start:usize,limit:usize)->Option<Shape>{
        let open=self.body_open(start+1,limit)?;
        let close=self.brace_end(open,limit)?;
        let mut i=open+1;let mut arms=Vec::new();
        while i<close {
            let mut arrow=None;
            for j in i..close {if self.kind(j)==Some(K::FatArrow){arrow=Some(j);break;}}
            let begin=arrow?+1;
            let end=self.brace_end(begin,close)?;
            arms.push(begin+1..end);
            i=end+1;
            if self.kind(i)==Some(K::Comma){i+=1;}
        }
        Some(Shape::Match{head:start..open,arms,end:close+1})
    }
    fn parse_loop(&self,start:usize,limit:usize)->Option<Shape>{
        let conditional=self.kind(start)!=Some(K::Ident("loop"));
        let open=if conditional{self.body_open(start+1,limit)?}else{start+1};
        let close=self.brace_end(open,limit)?;
        Some(Shape::Loop{header:start..open,body:open+1..close,end:close+1,conditional})
    }
    fn parse_plain(&self,start:usize,limit:usize)->Option<Shape>{
        let (mut parens,mut braces)=(0usize,0usize);
        for i in start..limit {
            match self.kind(i)? {
                K::LParen=>parens+=1,
                K::RParen=>parens=parens.checked_sub(1)?,
                K::LBrace=>braces+=1,
                K::RBrace=>braces=braces.checked_sub(1)?,
                K::Semi if parens==0&&braces==0=>return Some(Shape::Plain(start..i+1)),
                _=>(),
            }
        }
        if parens==0&&braces==0 {Some(Shape::Plain(start..limit))}else{None}
    }
    fn parse_sequence(&self,r:Range<usize>)->Option<Vec<Shape>>{
        let mut i=r.start;let mut shapes=Vec::new();
        while i<r.end {
            let shape=match self.kind(i)? {
                K::Ident("if")=>self.parse_if(i,r.end)?,
                K::Ident("match")=>self.parse_match(i,r.end)?,
                K::Ident("while"|"for"|"loop")=>self.parse_loop(i,r.end)?,
                _=>self.parse_plain(i,r.end)?,
            };
            let end=shape.end();
            if end<=i||end>r.end{return None;}
            shapes.push(shape);
            if shapes.len()+self.nodes.len()>NODE_LIMIT{return None;}
            i=end;
        }
        Some(shapes)
    }
    fn node(&mut self,span:Range<usize>,successors:Vec<usize>)->Option<usize>{
        if self.nodes.len()>=NODE_LIMIT{return None;}
        let uses=(span.start..span.end).filter_map(|index|
            self.bindings.uses.get(&index).copied()).collect();
        let defines=(span.start..span.end).filter_map(|index|
            self.bindings.declarations.get(&index).copied()).collect();
        let id=self.nodes.len();
        self.nodes.push(Node{span,uses,defines,successors,live_in:HashSet::new()});
        Some(id)
    }
    fn sequence(&mut self,range:Range<usize>,follow:usize,loop_ctx:Option<LoopTargets>,depth:usize)->Option<usize>{
        if depth>DEPTH_LIMIT{return None;}
        let statements=self.parse_sequence(range.clone())?;
        self.after.insert(range.end,follow);
        let mut successor=follow;
        for statement in statements.into_iter().rev(){
            self.after.insert(statement.end(),successor);
            successor=match statement {
                Shape::Plain(span)=> {
                    let target=match self.kind(span.start) {
                        Some(K::Ident("return"))=>0,
                        Some(K::Ident("break"))=>loop_ctx?.break_to,
                        Some(K::Ident("continue"))=>loop_ctx?.continue_to,
                        _=>successor,
                    };
                    self.node(span,vec![target])?
                }
                Shape::If{arms,..}=>{
                    let mut other=successor;
                    for (test,body) in arms.into_iter().rev(){
                        let branch=self.sequence(body,successor,loop_ctx,depth+1)?;
                        other=if let Some(test)=test{self.node(test,vec![branch,other])?}else{branch};
                    }
                    other
                }
                Shape::Match{head,arms,..}=>{
                    let mut options=Vec::with_capacity(arms.len()+1);
                    for arm in arms {
                        let body=self.sequence(arm.clone(),successor,loop_ctx,depth+1)?;
                        if let Some(ids)=self.bindings.arm_bindings.get(&arm.start).cloned() {
                            let entry=self.node(arm.start..arm.start,vec![body])?;
                            self.nodes[entry].defines.extend(ids);
                            self.pattern_entry_points.insert(arm.start-1,entry);
                            options.push(entry);
                        }else{options.push(body);}
                    }
                    options.push(successor); //Conservative unmatched arm; semantic pass checks exhaustiveness
                    self.node(head,options)?
                }
                Shape::Loop{header,body,conditional,..}=>{
                    let entry=self.node(header,Vec::new())?;
                    let branch=self.sequence(body.clone(),entry,
                        Some(LoopTargets{break_to:successor,continue_to:entry}),depth+1)?;
                    self.nodes[entry].successors=if conditional{vec![branch,successor]}else{vec![branch]};
                    self.after.insert(body.start,branch);
                    entry
                }
            };
        }
        self.after.insert(range.start,successor);
        Some(successor)
    }
    fn fixed_point(&mut self)->Option<()> {
        let len=self.nodes.len();
        let mut predecessors=vec![Vec::<usize>::new();len];
        for (i,node) in self.nodes.iter().enumerate(){
            for &next in &node.successors {predecessors.get_mut(next)?.push(i);}
        }
        let mut pending=VecDeque::from_iter(0..len);
        let mut queued=vec![true;len];
        let mut steps=0usize;
        while let Some(i)=pending.pop_front(){
            queued[i]=false;
            steps+=1;if steps>WORK_LIMIT{return None;}
            let mut next=self.nodes[i].uses.clone();
            for &successor in &self.nodes[i].successors {
                for name in &self.nodes[successor].live_in {
                    if !self.nodes[i].defines.contains(name){next.insert(name.clone());}
                }
            }
            if next!=self.nodes[i].live_in {
                self.nodes[i].live_in=next;
                for &before in &predecessors[i] {
                    if !queued[before] {pending.push_back(before);queued[before]=true;}
                }
            }
        }
        Some(())
    }
}

#[derive(Debug)]
pub struct FlowPlan {
    pub range: Range<usize>,
    pub scope_base: usize,
    live_at: Option<HashMap<usize,HashSet<SymbolId>>>,
    points_at: HashMap<usize,CfgPointId>,
    token_points: Vec<Option<CfgPointId>>,
    #[allow(dead_code)] //Retained for regression tests and region-profile counters
    place_accesses: Vec<PlaceEdgeAccess>,
    typed_loans: HashMap<SymbolId,TypedPlace>,
    //Deep pattern loans are verified with exact TypeId/FieldId chains Ordinary one-field references never
    //allocate this sidecar
    deep_typed_loans: HashMap<SymbolId,TypedPlacePath>,
    typed_accesses: Vec<TypedPlaceAccess>,
    move_paths: MovePathForest,
    move_path_events: Vec<MovePathEvent>,
    borrow_graph: Option<crate::cfg_borrow::Graph>,
    borrow_graph_error: Option<String>,
    verified_borrow_paths: HashMap<SymbolId,crate::cfg_borrow::Path>,
    #[allow(dead_code)]
    binding_names: HashMap<SymbolId,String>,
    origins: HashMap<SymbolId,SymbolId>,
    loan_kinds: HashMap<SymbolId,crate::region_infer::LoanKind>,
    root_only_loans: HashSet<SymbolId>,
    binding_at_token: HashMap<usize,SymbolId>,
    local_ids: HashSet<SymbolId>,
    pattern_loan_ids: HashSet<SymbolId>,
    inferred: Option<LocalRegionInference>,
    inferred_ids: HashMap<SymbolId,RegionId>,
    edge_loans: Option<EdgeLoanAnalysis>,
}
impl FlowPlan {
    pub fn new<'a>(tokens:&[Token<'a>],range:Range<usize>,needed:bool,scope_base:usize,
        parameters:&[(String,SymbolId)])->Self {
        let mut live_at=None;
        let mut points_at=HashMap::new();
        let mut token_points=Vec::new();
        let mut place_accesses=Vec::new();
        let mut binding_names=HashMap::new();
        let mut origins=HashMap::new();
        let mut loan_kinds=HashMap::new();
        let mut root_only_loans=HashSet::new();
        let mut binding_at_token=HashMap::new();
        let mut local_ids=HashSet::new();
        let mut pattern_loan_ids=HashSet::new();
        let mut raw_cfg=None;
        let mut cfg_entry=None;
        let observing=region_profile_enabled();
        let mut measurement=RegionProfile{plans:1,..RegionProfile::default()};
        if needed {
            let timer=observing.then(Instant::now);
            let bindings_result=Bindings::new(tokens,range.clone(),parameters);
            measurement.binding+=observed_elapsed(timer);
            if let Some(bindings)=bindings_result {
                let mut builder=Builder{tokens,nodes:Vec::new(),after:HashMap::new(),
                    pattern_entry_points:HashMap::new(),bindings};
                let exit=builder.node(range.end..range.end,Vec::new());
                debug_assert_eq!(exit,Some(0));
                let timer=observing.then(Instant::now);
                let built=builder.sequence(range.clone(),0,None,0).is_some();
                measurement.cfg_build+=observed_elapsed(timer);
                let timer=observing.then(Instant::now);
                let solved=built && builder.fixed_point().is_some();
                if built {measurement.backward_liveness+=observed_elapsed(timer);}
                binding_names=std::mem::take(&mut builder.bindings.name_by_id);
                origins=std::mem::take(&mut builder.bindings.origins);
                loan_kinds=std::mem::take(&mut builder.bindings.loan_kinds);
                root_only_loans=std::mem::take(&mut builder.bindings.root_only_loans);
                binding_at_token=std::mem::take(&mut builder.bindings.uses);
                local_ids=builder.bindings.declarations.values().copied().collect();
                pattern_loan_ids=std::mem::take(&mut builder.bindings.pattern_loan_ids);
                if solved {
                    measurement.successful_cfg+=1;
                    measurement.nodes+=builder.nodes.len();
                    token_points=vec![None;range.end.saturating_sub(range.start)];
                    for (node_id,node) in builder.nodes.iter().enumerate() {
                        for at in node.span.clone() {
                            if let Some(cell)=token_points.get_mut(at-range.start) {
                                *cell=Some(CfgPointId(node_id as u32));
                            }
                        }
                    }
                    for (&boundary,&next) in &builder.after {
                        points_at.insert(boundary,CfgPointId(next as u32));
                    }
                    for (&open,&entry) in &builder.pattern_entry_points {
                        if let Some(cell)=token_points.get_mut(open-range.start) {
                            *cell=Some(CfgPointId(entry as u32));
                        }
                    }
                    if !origins.is_empty() {
                        for at in range.clone() {
                            let Some(&point)=token_points.get(at-range.start)
                                .and_then(|p|p.as_ref()) else {continue;};
                            let Some(&owner)=binding_at_token.get(&at) else {continue;};
                            let prev=at.checked_sub(1).and_then(|i|tokens.get(i)).map(|t|t.kind);
                            let next=tokens.get(at+1).map(|t|t.kind);
                            let kind=if next==Some(K::Equal)
                                && prev!=Some(K::Dot) {
                                Some(PlaceAccessKind::Write)
                            } else if prev==Some(K::Equal)
                                && next==Some(K::Semi) {
                                Some(PlaceAccessKind::Move)
                            } else {None};
                            if let Some(kind)=kind {
                                place_accesses.push(PlaceEdgeAccess{point,token:at,owner,kind});
                            }
                        }
                    }
                    cfg_entry=builder.after.get(&range.start).copied();
                    live_at=Some(builder.after.into_iter().map(|(boundary,next)|
                        (boundary,builder.nodes[next].live_in.clone())).collect());
                    raw_cfg=Some(builder.nodes);
                }
            }
        }
        measurement.place_accesses+=place_accesses.len();
        let borrow_graph=raw_cfg.as_ref().and_then(|nodes|cfg_entry.and_then(|entry|
            crate::cfg_borrow::Graph::new(entry,nodes.iter().map(|n|n.successors.clone()).collect()).ok()));
        let mut plan=Self{range,scope_base,live_at,points_at,token_points,place_accesses,typed_loans:HashMap::new(),deep_typed_loans:HashMap::new(),typed_accesses:Vec::new(),move_paths:MovePathForest::default(),move_path_events:Vec::new(),borrow_graph,borrow_graph_error:None,verified_borrow_paths:HashMap::new(),binding_names,origins,loan_kinds,root_only_loans,
            binding_at_token,local_ids,pattern_loan_ids,
            inferred:None,inferred_ids:HashMap::new(),edge_loans:None};
        if plan.live_at.is_some() {
            let timer=observing.then(Instant::now);
            let mut inference=LocalRegionInference::default();
            for &binding in plan.origins.keys() {
                if let Some(region)=plan.local_region(binding,Place::Root){
                    let kind=plan.loan_kinds.get(&binding).copied()
                        .unwrap_or(crate::region_infer::LoanKind::Shared);
                    plan.inferred_ids.insert(binding,inference.add_loan(region,kind));
                }
            }
            for (&child,&parent) in &plan.origins {
                if let (Some(&long),Some(&short))=
                    (plan.inferred_ids.get(&parent),plan.inferred_ids.get(&child)) {
                    inference.require_outlives(long,short);
                }
            }
            if inference.solve().is_ok(){plan.inferred=Some(inference);}
            measurement.region_solve+=observed_elapsed(timer);
        }
        measurement.loans+=plan.origins.len();
        if !plan.origins.is_empty() {
            if let (Some(nodes),Some(entry))=(raw_cfg,cfg_entry) {
                let timer=observing.then(Instant::now);
                plan.edge_loans=EdgeLoanAnalysis::build(&nodes,entry,&plan.origins,
                    plan.inferred.as_ref(),&plan.inferred_ids);
                measurement.edge_events_and_forward+=observed_elapsed(timer);
                if let Some(edge)=&plan.edge_loans {
                    measurement.edges+=edge.edges.len();
                    measurement.events+=edge.edges.iter().map(|edge|edge.events.len()).sum::<usize>();
                    measurement.edge_worklist_steps+=edge.iterations;
                }
            }
        }
        if observing {commit_region_profile(measurement);}
        plan
    }
    pub fn contains(&self,body:&Range<usize>)->bool {
        self.range.start<=body.start && body.end<=self.range.end
    }
    pub fn live_at(&self,token_position:usize)->Option<&HashSet<SymbolId>>{
        self.live_at.as_ref()?.get(&token_position)
    }
    pub fn point_at(&self,token_position:usize)->Option<CfgPointId>{
        self.points_at.get(&token_position).copied()
    }
    pub fn point_containing(&self,token_position:usize)->Option<CfgPointId>{
        self.token_points.get(token_position.checked_sub(self.range.start)?)
            .copied().flatten()
    }
    pub fn register_typed_loan(&mut self,binding:SymbolId,place:TypedPlace)->bool {
        if !self.origins.contains_key(&binding){return false;}
        //An owner must be a lexical root, not a forged unrelated SymbolId
        if self.root_owner(binding)!=Some(place.owner){return false;}
        self.typed_loans.insert(binding,place);
        if let (Some(engine),Some(&region))=
            (self.inferred.as_mut(),self.inferred_ids.get(&binding)) {
            engine.refine_place(region,place.owner,place.raw_place());
        }
        true
    }
    //Query a precise typed access, using the activated loan on the CFG path and its solved lifetime
    pub fn conflicting_typed_access(&self,token_position:usize,access:TypedPlace,
        kind:PlaceAccessKind)->Option<Vec<SymbolId>> {
        let point=self.point_containing(token_position)?;
        let edge=self.edge_loans.as_ref()?;
        let mut conflicting=Vec::new();
        for (&loan,&origin) in &self.origins {
            let loan_kind=*self.loan_kinds.get(&loan)?;
            if !kind.conflicts_with(loan_kind){continue;}
            let overlap=if let Some(&actual)=self.typed_loans.get(&loan) {
                actual.overlaps(access)
            }else if let Some(deep)=self.deep_typed_loans.get(&loan) {
                //Match a root/single-field access against the exact deep provenance; distinct verified siblings do not
                //alias An unrecognized field TypeId fails closed on overlap
                let access_path=TypedPlacePath{owner:access.owner,
                    fields:access.field.into_iter().collect()};
                deep.overlaps(&access_path)
            }else{
                self.root_only_loans.contains(&loan) &&
                    self.root_owner(origin)==Some(access.owner)
            };
            if !overlap {continue;}
            if edge.maybe_active_at(point,loan)==Some(true)
                && self.loan_live_at_point(point,loan) {conflicting.push(loan);}
        }
        conflicting.sort_unstable_by_key(|id|id.0);
        Some(conflicting)
    }
    #[cfg(test)]
    pub fn conflicting_access(&self,token_position:usize,owner:SymbolId,
        place:Place,access:PlaceAccessKind)->Option<Vec<SymbolId>> {
        //Untyped fields must never be given arbitrary numeric FieldIds
        let typed=TypedPlace::new(owner,None,place)?;
        self.conflicting_typed_access(token_position,typed,access)
    }
    pub fn record_typed_access(&mut self,token_position:usize,place:TypedPlace,
        kind:PlaceAccessKind)->Option<Vec<SymbolId>> {
        let point=self.point_containing(token_position)?;
        if self.typed_accesses.len()>=TYPED_ACCESS_LIMIT{return None;}
        let conflicts=self.conflicting_typed_access(token_position,place,kind)?;
        self.typed_accesses.push(TypedPlaceAccess{point,token:token_position,place,kind});
        if let Some(path)=self.move_paths.intern(place) {
            let change=match kind {
                PlaceAccessKind::Move=>Some(MovePathEventKind::Move),
                PlaceAccessKind::Write=>Some(MovePathEventKind::Initialize),
                _=>None,
            };
            if let Some(kind)=change {self.move_path_events.push(MovePathEvent{path,point,kind});}
        }
        Some(conflicts)
    }
    //Register a type-checked access. The parent path and MovePathId are interned by the forward checker; no
    //string-based alias guessing
    pub fn record_verified_path(&mut self,token:usize,path:crate::cfg_borrow::Path,
        kind:PlaceAccessKind){
        let Some(point)=self.point_containing(token)else{return;};
        let op=match kind {
            PlaceAccessKind::Read=>crate::cfg_borrow::Access::Read,
            PlaceAccessKind::Move=>crate::cfg_borrow::Access::Move,
            PlaceAccessKind::Write=>crate::cfg_borrow::Access::Write,
            PlaceAccessKind::BorrowShared|PlaceAccessKind::BorrowExclusive=>return,
        };
        if let Some(graph)=self.borrow_graph.as_mut(){
            if let Err(e)=graph.event(point.0 as usize,crate::cfg_borrow::Event{
                op,path,loan:None,parent:None,token}) {self.borrow_graph_error=Some(e);}
        }
    }
    pub fn record_verified_loan(&mut self,binding:SymbolId,token:usize,
        path:crate::cfg_borrow::Path,exclusive:bool,parent:Option<SymbolId>) {
        let Some(point)=self.point_containing(token)else{return;};
        if self.pattern_loan_ids.contains(&binding) && path.fields.len()>1 &&
            self.root_owner(binding)==Some(path.owner) {
            if let Some(typed)=TypedPlacePath::from_verified(&path){
                self.deep_typed_loans.insert(binding,typed);
            }
        }
        self.verified_borrow_paths.insert(binding,path.clone());
        if let Some(graph)=self.borrow_graph.as_mut(){
            if let Err(e)=graph.event(point.0 as usize,crate::cfg_borrow::Event{
                op:if exclusive{crate::cfg_borrow::Access::BorrowMut}
                    else{crate::cfg_borrow::Access::BorrowShared},
                path,loan:Some(binding),parent,token}) {self.borrow_graph_error=Some(e);}
        }
    }
    #[allow(dead_code)]
    pub fn record_verified_mut_reservation(&mut self,binding:SymbolId,token:usize,
        path:crate::cfg_borrow::Path){
        let Some(point)=self.point_containing(token) else {
            self.borrow_graph_error=Some("missing CFG point for mutable reservation".into());
            return;
        };
        self.verified_borrow_paths.insert(binding,path.clone());
        if let Some(graph)=self.borrow_graph.as_mut(){
            if let Err(e)=graph.event(point.0 as usize,crate::cfg_borrow::Event{
                op:crate::cfg_borrow::Access::ReserveMut,path,
                loan:Some(binding),parent:None,token}){
                self.borrow_graph_error=Some(e);
            }
        }else{self.borrow_graph_error=Some("borrow CFG unavailable for reservation".into());}
    }
    //Activating a reserved loan is a separate executable program point Missing origin or token mapping is
    //never treated as successful proof
    #[allow(dead_code)] //Legacy FlowPlan compatibility: MIR now activates directly
    pub fn record_verified_mut_activation(&mut self,binding:SymbolId,token:usize){
        let Some(point)=self.point_containing(token) else {
            self.borrow_graph_error=Some("missing CFG point for mutable activation".into());
            return;
        };
        let Some(path)=self.verified_borrow_paths.get(&binding).cloned() else {
            self.borrow_graph_error=Some("activating unknown reserved loan".into());
            return;
        };
        if let Some(graph)=self.borrow_graph.as_mut(){
            if let Err(e)=graph.event(point.0 as usize,crate::cfg_borrow::Event{
                op:crate::cfg_borrow::Access::ActivateMut,path,
                loan:Some(binding),parent:None,token}){
                self.borrow_graph_error=Some(e);
            }
        }else{self.borrow_graph_error=Some("borrow CFG unavailable for activation".into());}
    }
    pub fn record_verified_loan_end(&mut self,binding:SymbolId,token:usize){
        let Some(point)=self.point_containing(token)else{return;};
        let Some(path)=self.verified_borrow_paths.remove(&binding)else{return;};
        if let Some(graph)=self.borrow_graph.as_mut(){
            if let Err(e)=graph.event(point.0 as usize,crate::cfg_borrow::Event{
                op:crate::cfg_borrow::Access::EndLoan,
                path,loan:Some(binding),parent:None,token}) {self.borrow_graph_error=Some(e);}
        }
    }
    #[allow(dead_code)] //Direct MIR edge events supersede this optional bridge
    pub fn record_verified_loan_end_on_edge(&mut self,binding:SymbolId,
        from:CfgPointId,to:CfgPointId,token:usize){
        let Some(path)=self.verified_borrow_paths.get(&binding).cloned()else{return;};
        if let Some(graph)=self.borrow_graph.as_mut(){
            if let Err(e)=graph.event_on_edge(from.0 as usize,to.0 as usize,
                crate::cfg_borrow::Event{
                    op:crate::cfg_borrow::Access::EndLoan,
                    path,loan:Some(binding),parent:None,token}){
                self.borrow_graph_error=Some(e);
            }
        }
    }
    //Validation never returns an empty success if instrumentation overflowed The old RefLease checks remain
    //in force independently
    #[allow(dead_code)] //Compatibility API; new MIR invokes Graph::check itself
    pub fn verify_borrow_graph(&self)->Result<Vec<crate::cfg_borrow::Conflict>,String>{
        if let Some(error)=&self.borrow_graph_error{return Err(error.clone());}
        self.borrow_graph.as_ref().ok_or("borrow CFG not available".to_string())?.check()
    }
    #[cfg(test)]
    pub fn move_path_events(&self)->&[MovePathEvent]{&self.move_path_events}
    #[cfg(test)]
    pub fn typed_accesses(&self)->&[TypedPlaceAccess] {&self.typed_accesses}
    #[cfg(test)]
    pub fn typed_loan(&self,binding:SymbolId)->Option<TypedPlace>{
        self.typed_loans.get(&binding).copied()
    }
    fn loan_live_at_point(&self,point:CfgPointId,loan:SymbolId)->bool {
        self.inferred.as_ref().and_then(|engine|self.inferred_ids.get(&loan)
            .and_then(|id|engine.live_at(*id,point))).unwrap_or(false)
            || self.edge_loans.as_ref().and_then(|e|e.maybe_active_at(point,loan))==Some(true)
    }
    #[cfg(test)]
    pub fn place_accesses(&self)->&[PlaceEdgeAccess]{&self.place_accesses}
    #[cfg(test)]
    pub fn edge_access_conflicts(&self)->Vec<PlaceEdgeConflict> {
        let mut out=Vec::new();
        for &access in &self.place_accesses {
            if let Some(loans)=self.conflicting_access(access.token,access.owner,
                Place::Root,access.kind) {
                for loan in loans {out.push(PlaceEdgeConflict{access,loan});}
            }
        }
        out
    }
    pub fn binding_at_token(&self,token_position:usize)->Option<SymbolId>{
        self.binding_at_token.get(&token_position).copied()
    }
    pub fn origin(&self,binding:SymbolId)->Option<SymbolId>{
        self.origins.get(&binding).copied()
    }
    //Follow a reborrow chain to its original lexical owner. An invalid cycle or an overlong chain is never
    //treated as a valid region proof
    pub fn root_owner(&self,binding:SymbolId)->Option<SymbolId>{
        let mut current=binding;
        for _ in 0..=self.origins.len() {
            match self.origins.get(&current) {
                None=>return Some(current),
                Some(&next) if next!=current=>current=next,
                Some(_)=>return None,
            }
        }
        None
    }
    pub fn loan_live_at(&self,token_position:usize,binding:SymbolId)->Option<bool>{
        let backward=self.live_at(token_position)?.contains(&binding);
        let additional=self.inferred.as_ref()
            .and_then(|engine|self.inferred_ids.get(&binding)
                .and_then(|&id|self.point_at(token_position)
                    .and_then(|point|engine.live_at(id,point))))
            .unwrap_or(false);
        let edge_active=self.edge_loans.as_ref()
            .and_then(|edges|self.point_at(token_position)
                .and_then(|point|edges.maybe_active_at(point,binding)))
            .unwrap_or(false);
        Some(backward||additional||edge_active)
    }
    //Events on outgoing edges of the statement at a known token boundary None means no sound edge analysis
    //is available, never "loan is dead"
    #[allow(dead_code)]
    pub fn loan_events_after(&self,token_position:usize)->Option<Vec<LoanEdge>>{
        let point=self.point_at(token_position)?;
        Some(self.edge_loans.as_ref()?.outgoing(point).cloned().collect())
    }
    #[allow(dead_code)]
    pub fn edge_analysis(&self)->Option<&EdgeLoanAnalysis>{self.edge_loans.as_ref()}

    #[cfg(test)]
    pub fn conflicting_loans_at(&self,token_position:usize)->Option<Vec<(SymbolId,SymbolId)>>{
        let engine=self.inferred.as_ref()?;
        let point=self.point_at(token_position)?;
        let mut bindings=self.inferred_ids.iter().collect::<Vec<_>>();
        bindings.sort_unstable_by_key(|pair|pair.0.0);
        let mut conflicts=Vec::new();
        for (i,&(&a,&region_a)) in bindings.iter().enumerate(){
            for &(&b,&region_b) in bindings.iter().skip(i+1){
                if self.is_ancestor(a,b)||self.is_ancestor(b,a){continue;}
                if engine.loans_conflict_at(region_a,region_b,point)==Some(true) {
                    conflicts.push((a,b));
                }
            }
        }
        Some(conflicts)
    }
    #[cfg(test)]
    fn is_ancestor(&self,ancestor:SymbolId,mut child:SymbolId)->bool{
        for _ in 0..self.origins.len(){
            let Some(&parent)=self.origins.get(&child) else{return false;};
            if parent==ancestor{return true;}
            if parent==child{return false;}
            child=parent;
        }
        false
    }
    pub fn is_local(&self,binding:SymbolId)->bool{self.local_ids.contains(&binding)}
    //Proof that a borrowed enum-pattern binding has a CFG declaration, source owner, and solved liveness
    //rather than an unknown lifetime
    pub fn tracks_pattern_loan(&self,binding:SymbolId)->bool{
        self.live_at.is_some() && self.inferred.is_some()
            && self.edge_loans.is_some() && self.borrow_graph.is_some()
            && self.borrow_graph_error.is_none()
            && self.pattern_loan_ids.contains(&binding)
            && self.inferred_ids.contains_key(&binding)
    }
    pub fn verified_pattern_loan(&self,binding:SymbolId)->bool{
        self.tracks_pattern_loan(binding)
            && self.verified_borrow_paths.contains_key(&binding)
            && self.verified_borrow_paths.get(&binding).is_some_and(|path|
                self.root_owner(binding)==Some(path.owner)
                && path.fields.first().is_some_and(|f|f.field.0 & 0x8000_0000 != 0)
                && (path.fields.len()==1 || self.deep_typed_loans.get(&binding)
                    .is_some_and(|typed|typed.matches_verified(path))))
    }
    #[allow(dead_code)]
    pub fn inferred_local_region(&self,binding:SymbolId)->Option<&LocalRegion>{
        self.inferred.as_ref()?.get(*self.inferred_ids.get(&binding)?)
    }
    #[allow(dead_code)]
    pub fn live_symbol_at(&self,token_position:usize,symbol:SymbolId)->Option<bool>{
        Some(self.live_at(token_position)?.contains(&symbol))
    }
    pub fn local_region(&self,binding:SymbolId,place:Place)->Option<LocalRegion>{
        let owner=self.root_owner(binding)?;
        let points=self.live_at.as_ref()?.iter().filter_map(|(boundary,live)|
            live.contains(&binding).then(||self.point_at(*boundary)).flatten()).collect();
        Some(LocalRegion{binding,owner,place,points})
    }
    #[cfg(test)]
    fn is_live(&self,token_position:usize,name:&str)->bool{
        self.live_at(token_position).is_some_and(|live|live.iter().any(|id|
            self.binding_names.get(id).is_some_and(|n|n==name)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn get<'a>(tokens:&'a [Token<'a>])->FlowPlan {FlowPlan::new(tokens,0..tokens.len(),true,0,&[])}
    fn entry(source:&str,name:&str)->bool {
        let tokens=crate::syntax::lex(source).unwrap();
        let p=get(&tokens);
        p.is_live(0,name)
    }
    #[test]fn if_join_keeps_only_continuation_borrows(){
        let src="let r=&n; if check { use_ref(r); } else { other(); } mutate();";
        let t=crate::syntax::lex(src).unwrap();let p=get(&t);
        let i=t.iter().position(|v|v.kind==K::Ident("mutate")).unwrap();
        assert!(!p.is_live(i,"r"));
    }
    #[test]fn disjoint_if_branch_has_distinct_entry_liveness(){
        let src="let r=&n; if yes { read(r); } else { n=7; }";
        let t=crate::syntax::lex(src).unwrap();let p=get(&t);
        let i=t.iter().position(|v|v.kind==K::Ident("else")).unwrap()+2;
        assert!(!p.is_live(i,"r"));
    }
    #[test]fn disjoint_match_arm_has_distinct_entry_liveness(){
        let src="let r=&n; match e { E::A => { read(r); }, E::B => { n=7; } }";
        let t=crate::syntax::lex(src).unwrap();let p=get(&t);
        let b=t.iter().position(|v|v.kind==K::Ident("B")).unwrap();
        assert!(!p.is_live(b+3,"r"));
    }
    #[test]fn match_join_and_future_use(){
        let src="let r=&n; match state { E::A => { f(r); }, _ => { g(); } } h(r);";
        let t=crate::syntax::lex(src).unwrap();let p=get(&t);
        let h=t.iter().position(|v|v.kind==K::Ident("h")).unwrap();
        assert!(p.is_live(h,"r"));
    }
    #[test]fn while_back_edge_requires_a_fixed_point(){
        let src="let r=&x; while again { read(r); step(); } x=9;";
        let t=crate::syntax::lex(src).unwrap();let p=get(&t);
        let step=t.iter().position(|v|v.kind==K::Ident("step")).unwrap();
        let x=t.iter().rposition(|v|v.kind==K::Ident("x")).unwrap();
        assert!(p.is_live(step,"r"));
        assert!(!p.is_live(x,"r"));
    }
    #[test]fn continue_edge_reaches_next_iteration(){
        let src="let r=&x; while again { if skip { continue; } read(r); } x=1;";
        let t=crate::syntax::lex(src).unwrap();let p=get(&t);
        let cont=t.iter().position(|v|v.kind==K::Ident("continue")).unwrap();
        assert!(p.is_live(cont,"r"));
        let x=t.iter().rposition(|v|v.kind==K::Ident("x")).unwrap();
        assert!(!p.is_live(x,"r"));
    }
    #[test]fn break_edge_skips_body_and_uses_after_loop(){
        let src="let r=&x; while again { if stop { break; } read(r); } x=1;";
        let t=crate::syntax::lex(src).unwrap();let p=get(&t);
        let br=t.iter().position(|v|v.kind==K::Ident("break")).unwrap();
        assert!(!p.is_live(br,"r"));
    }
    #[test]fn nested_for_while_and_return_converge(){
        let src="let r=&x; for i in 0..3 { while again { if stop { break; } if leave { return; } use_ref(r); continue; } } done();";
        let t=crate::syntax::lex(src).unwrap();let p=get(&t);
        assert!(p.live_at(0).is_some());
        assert!(entry(src,"x"));
        let early=t.iter().position(|v|v.kind==K::Ident("return")).unwrap();
        assert!(!p.is_live(early,"r"));
    }
    #[test]fn unsupported_break_is_conservative(){
        let t=crate::syntax::lex("let a=&x; break; x=2;").unwrap();
        let p=get(&t);
        assert!(p.live_at(0).is_none());
    }
}

#[cfg(test)]
mod symbolic_point_tests {
    use super::*;
    #[test] fn shadowed_names_have_distinct_ids_and_only_the_later_one_is_live(){
        let src="let x=1; let r=&x; if yes { let x=2; let r=&x; read(r); } read(r);";
        let tokens=crate::syntax::lex(src).unwrap();
        let flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let decls:Vec<_>=tokens.iter().enumerate().filter_map(|(i,t)|
            (t.kind==K::Ident("r") && i>0 && tokens[i-1].kind==K::Ident("let"))
                .then_some(SymbolId((i+1) as u32))).collect();
        assert_eq!(decls.len(),2);
        assert_ne!(decls[0],decls[1]);
        let i=tokens.iter().rposition(|t|t.kind==K::Ident("read")).unwrap();
        assert_eq!(flow.live_symbol_at(i,decls[0]),Some(true));
        assert_eq!(flow.live_symbol_at(i,decls[1]),Some(false));
        let local=flow.local_region(decls[0],Place::Root).unwrap();
        assert!(!local.points.is_empty());
        assert!(flow.point_at(i).is_some());
        assert!(flow.inferred_local_region(decls[0]).is_some());
    }
    #[test] fn reference_to_outer_binding_is_not_confused_by_inner_shadow(){
        let src="let x=1; let r=&x; if yes { let x=2; modify(x); } read(r);";
        let tokens=crate::syntax::lex(src).unwrap();
        let flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let r=tokens.iter().position(|t|t.kind==K::Ident("r")).unwrap();
        let x=tokens.iter().position(|t|t.kind==K::Ident("x")).unwrap();
        let region=flow.local_region(SymbolId((r+1) as u32),Place::Root).unwrap();
        assert_eq!(region.owner,SymbolId((x+1) as u32));
    }
}

#[cfg(test)]
mod solved_region_tests_062 {
    use super::*;
    fn token_pos(tokens:&[Token<'_>],name:&str)->usize{
        tokens.iter().position(|t|matches!(t.kind,K::Ident(n) if n==name)).unwrap()
    }
    #[test]
    fn reborrow_chain_reaches_original_owner_and_extends_parent_region() {
        let src="let x=1;let r=&x;let t=&*r;read(t);done();";
        let tokens=crate::syntax::lex(src).unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let x=SymbolId((token_pos(&tokens,"x")+1) as u32);
        let r=SymbolId((token_pos(&tokens,"r")+1) as u32);
        let t=SymbolId((token_pos(&tokens,"t")+1) as u32);
        let read=token_pos(&tokens,"read");
        assert_eq!(p.origin(t),Some(r));
        assert_eq!(p.root_owner(t),Some(x));
        assert_eq!(p.live_symbol_at(read,r),Some(false));
        assert_eq!(p.loan_live_at(read,r),Some(true));
        assert_eq!(p.loan_live_at(read,t),Some(true));
    }
    #[test]
    fn exclusive_and_shared_direct_borrows_are_conflict_candidates() {
        let src="let mut x=1;let a=&x;let b=&mut x;read(a);read(b);";
        let tokens=crate::syntax::lex(src).unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let a=SymbolId((token_pos(&tokens,"a")+1) as u32);
        let b=SymbolId((token_pos(&tokens,"b")+1) as u32);
        let first_read=token_pos(&tokens,"read");
        assert!(p.conflicting_loans_at(first_read).unwrap().contains(&(a,b)));
    }
    #[test]
    fn loans_in_disjoint_if_arms_do_not_conflict_at_arm_points() {
        let src="let mut x=1;if yes {let a=&mut x;read_a(a);} else {let b=&mut x;read_b(b);}";
        let tokens=crate::syntax::lex(src).unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let a_read=token_pos(&tokens,"read_a");
        let b_read=token_pos(&tokens,"read_b");
        assert_eq!(p.conflicting_loans_at(a_read),Some(Vec::new()));
        assert_eq!(p.conflicting_loans_at(b_read),Some(Vec::new()));
    }
    #[test]
    fn loan_region_stops_after_last_lease_use() {
        let src="let x=1;let r=&x;read(r);later();";
        let tokens=crate::syntax::lex(src).unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let r=SymbolId((token_pos(&tokens,"r")+1) as u32);
        let later=token_pos(&tokens,"later");
        assert_eq!(p.loan_live_at(later,r),Some(false));
    }
    #[test]
    fn reborrow_parent_is_not_a_conflicting_independent_loan() {
        let src="let mut x=1;let r=&mut x;let t=&*r;read(t);";
        let tokens=crate::syntax::lex(src).unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let read=token_pos(&tokens,"read");
        assert_eq!(p.conflicting_loans_at(read),Some(Vec::new()));
    }
}

#[cfg(test)]
mod edge_loan_tests_063 {
    use super::*;

    #[test]
    fn creation_and_activation_follow_the_declaration_edge() {
        let tokens=crate::syntax::lex("let r=&n; read(r); done();").unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let loan=*p.origins.keys().next().unwrap();
        let edges=p.loan_events_after(0).unwrap();
        assert!(edges.iter().any(|edge|edge.events.windows(2).any(|pair|
            pair[0].loan==loan && pair[0].kind==LoanEdgeEventKind::Create &&
            pair[1].loan==loan && pair[1].kind==LoanEdgeEventKind::Activate)));
        let read=tokens.iter().position(|t|t.kind==K::Ident("read")).unwrap();
        assert_eq!(p.loan_live_at(read,loan),Some(true));
    }

    #[test]
    fn loan_is_invalidated_after_its_last_read() {
        let tokens=crate::syntax::lex("let r=&n; read(r); done();").unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let loan=*p.origins.keys().next().unwrap();
        let read=tokens.iter().position(|t|t.kind==K::Ident("read")).unwrap();
        let done=tokens.iter().position(|t|t.kind==K::Ident("done")).unwrap();
        assert!(p.loan_events_after(read).unwrap().iter().any(|e|
            e.events.contains(&LoanEdgeEvent{loan,kind:LoanEdgeEventKind::Invalidate})));
        assert_eq!(p.loan_live_at(done,loan),Some(false));
    }

    #[test]
    fn unused_loan_is_created_activated_and_invalidated_on_one_edge() {
        let tokens=crate::syntax::lex("let r=&n; done();").unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let loan=*p.origins.keys().next().unwrap();
        let edges=p.loan_events_after(0).unwrap();
        let kinds=edges[0].events.iter().filter(|e|e.loan==loan)
            .map(|e|e.kind).collect::<Vec<_>>();
        assert_eq!(kinds,vec![LoanEdgeEventKind::Create,
            LoanEdgeEventKind::Activate,LoanEdgeEventKind::Invalidate]);
    }

    #[test]
    fn mutually_exclusive_branch_local_loans_do_not_leak_at_join() {
        let tokens=crate::syntax::lex(
            "if yes { let r=&n; read(r); } else { let r=&m; read(r); } done();").unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        assert_eq!(p.origins.len(),2);
        let done=tokens.iter().position(|t|t.kind==K::Ident("done")).unwrap();
        for &loan in p.origins.keys() {
            assert_eq!(p.loan_live_at(done,loan),Some(false));
        }
        let mut ids=p.origins.keys().copied().collect::<Vec<_>>();
        ids.sort_unstable_by_key(|id|id.0);
        assert_ne!(ids[0],ids[1]);
    }

    #[test]
    fn loop_backedge_retains_loan_until_the_loop_exits() {
        let tokens=crate::syntax::lex("let r=&n; while again { read(r); continue; } done();").unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let loan=*p.origins.keys().next().unwrap();
        let cont=tokens.iter().position(|t|t.kind==K::Ident("continue")).unwrap();
        let done=tokens.iter().position(|t|t.kind==K::Ident("done")).unwrap();
        assert_eq!(p.loan_live_at(cont,loan),Some(true));
        assert_eq!(p.loan_live_at(done,loan),Some(false));
        assert!(p.edge_analysis().unwrap().iterations>0);
    }

    #[test]
    fn child_reborrow_extends_parent_activation() {
        let tokens=crate::syntax::lex("let r=&n; let t=&*r; read(t); done();").unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let (&child,&parent)=p.origins.iter().find(|(_,owner)|p.origins.contains_key(*owner)).unwrap();
        let read=tokens.iter().position(|t|t.kind==K::Ident("read")).unwrap();
        assert_eq!(p.loan_live_at(read,parent),Some(true));
        assert_eq!(p.loan_live_at(read,child),Some(true));
        assert!(p.edge_analysis().is_some());
    }

    #[test]
    fn unavailable_analysis_never_proves_that_a_borrow_is_dead() {
        let tokens=crate::syntax::lex("let r=&n; use_ref(r);").unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),false,0,&[]);
        assert!(p.edge_analysis().is_none());
        assert_eq!(p.loan_live_at(0,SymbolId(1)),None);
    }
}

#[cfg(test)]
mod region_profile_tests_064 {
    use super::*;
    #[test]
    fn recorded_region_stages_have_real_cfg_and_loan_counts() {
        let tokens=crate::syntax::lex("let n=10;let r=&n;read(r);").unwrap();
        begin_region_profile();
        let plan=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let report=finish_region_profile();
        assert!(plan.edge_analysis().is_some());
        assert_eq!(report.plans,1);
        assert_eq!(report.successful_cfg,1);
        assert!(report.nodes>0);
        assert_eq!(report.loans,1);
        assert!(report.edges>0);
        assert!(report.events>=2);
    }
    #[test]
    fn profiling_can_be_disabled_after_finish_and_no_cfg_is_counted() {
        let tokens=crate::syntax::lex("let n=10;").unwrap();
        begin_region_profile();
        let _plan=FlowPlan::new(&tokens,0..tokens.len(),false,0,&[]);
        let report=finish_region_profile();
        assert_eq!(report.plans,1);
        assert_eq!(report.successful_cfg,0);
        assert_eq!(report.nodes,0);
        assert_eq!(report.loans,0);
        assert_eq!(finish_region_profile().plans,0);
    }
}

#[cfg(test)]
mod cfg_access_tests_065 {
    use super::*;
    fn plan(src:&str)->(Vec<Token<'_>>, FlowPlan) {
        let tokens=crate::syntax::lex(src).unwrap();
        let flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        (tokens,flow)
    }
    #[test]
    fn lexical_shadow_restore_resolves_original_symbol() {
        let src="let x=1; let a=&x; {let x=2; let b=&x; read(b);} read(a);";
        let (tokens,p)=plan(src);
        let at=tokens.iter().rposition(|t|t.kind==K::Ident("a")).unwrap();
        let a=tokens.iter().position(|t|t.kind==K::Ident("a")).unwrap();
        assert_eq!(p.binding_at_token(at),Some(SymbolId((a+1) as u32)));
        let r=tokens.iter().position(|t|t.kind==K::Ident("read")).unwrap();
        assert!(p.point_containing(r).is_some());
    }
    #[test]
    fn direct_root_borrow_reports_write_and_move_access_candidates() {
        let src="let mut x=1;let r=&x; x=2; read(r);";
        let (tokens,p)=plan(src);
        let owner=tokens.iter().position(|t|t.kind==K::Ident("x")).unwrap();
        let at=tokens.iter().enumerate().find(|(i,t)|*i>owner && t.kind==K::Ident("x")
            && tokens.get(*i+1).is_some_and(|t|t.kind==K::Equal)).unwrap().0;
        let owner=SymbolId((owner+1) as u32);
        assert_eq!(p.conflicting_access(at,owner,Place::Root,PlaceAccessKind::Write)
            .unwrap().len(),1);
        assert_eq!(p.conflicting_access(at,owner,Place::Root,PlaceAccessKind::Move)
            .unwrap().len(),1);
    }
    #[test]
    fn dead_loans_do_not_block_later_writes() {
        let src="let mut x=1;let r=&x;read(r);x=2;";
        let (tokens,p)=plan(src);
        let x=tokens.iter().position(|t|t.kind==K::Ident("x")).unwrap();
        let at=tokens.iter().enumerate().find(|(i,t)|*i>x && t.kind==K::Ident("x")
            && tokens.get(*i+1).is_some_and(|t|t.kind==K::Equal)).unwrap().0;
        assert_eq!(p.conflicting_access(at,SymbolId((x+1) as u32),Place::Root,
            PlaceAccessKind::Write),Some(Vec::new()));
    }
    #[test]
    fn unrelated_owner_is_never_blocked() {
        let src="let mut x=1;let mut y=2;let r=&x;y=3;read(r);";
        let (tokens,p)=plan(src);
        let y=tokens.iter().position(|t|t.kind==K::Ident("y")).unwrap();
        let at=tokens.iter().enumerate().find(|(i,t)|*i>y && t.kind==K::Ident("y")
            && tokens.get(*i+1).is_some_and(|t|t.kind==K::Equal)).unwrap().0;
        assert_eq!(p.conflicting_access(at,SymbolId((y+1) as u32),Place::Root,
            PlaceAccessKind::Write),Some(Vec::new()));
    }
    #[test]
    fn write_is_recorded_at_its_executable_cfg_node() {
        let src="let mut x=1;let r=&x;x=2;read(r);";
        let (_,p)=plan(src);
        assert!(p.place_accesses().iter().any(|a|a.kind==PlaceAccessKind::Write));
        assert!(p.edge_access_conflicts().iter().any(|a|a.access.kind==PlaceAccessKind::Write));
    }
    #[test]
    fn simple_initializer_move_is_only_a_candidate() {
        let src="let x=1;let r=&x;let y=x;read(r);";
        let (_,p)=plan(src);
        assert!(p.place_accesses().iter().any(|a|a.kind==PlaceAccessKind::Move));
        assert!(p.edge_access_conflicts().iter().any(|a|a.access.kind==PlaceAccessKind::Move));
    }
    #[test]
    fn unknown_cfg_point_fails_closed() {
        let tokens=crate::syntax::lex("let r=&x; read(r);").unwrap();
        let p=FlowPlan::new(&tokens,0..tokens.len(),false,0,&[]);
        assert!(p.conflicting_access(0,SymbolId(1),Place::Root,PlaceAccessKind::Move).is_none());
    }
}

#[cfg(test)]
mod typed_places_tests_066 {
    use super::*;
    fn example()->(Vec<Token<'static>>,FlowPlan,SymbolId,SymbolId,SymbolId) {
        let src="let mut p=0;let a=&mut p.x;let b=&mut p.y;read(a);read(b);";
        let t=crate::syntax::lex(src).unwrap();
        let p=SymbolId((t.iter().position(|t|t.kind==K::Ident("p")).unwrap()+1) as u32);
        let a=SymbolId((t.iter().position(|t|t.kind==K::Ident("a")).unwrap()+1) as u32);
        let b=SymbolId((t.iter().position(|t|t.kind==K::Ident("b")).unwrap()+1) as u32);
        let plan=FlowPlan::new(&t,0..t.len(),true,0,&[]);
        (t,plan,p,a,b)
    }
    #[test] fn same_numeric_field_id_is_distinct_across_types() {
        let a=TypedFieldId{aggregate:TypeId(1),field:FieldId(0)};
        let b=TypedFieldId{aggregate:TypeId(2),field:FieldId(0)};
        assert_ne!(a,b);
        let root=SymbolId(4);
        let pa=TypedPlace{owner:root,field:Some(a)};
        let pb=TypedPlace{owner:root,field:Some(b)};
        assert!(pa.overlaps(pb));
    }
    #[test] fn fields_are_disjoint_but_root_and_same_field_overlap() {
        let owner=SymbolId(12);
        let x=TypedPlace::new(owner,Some(TypeId(8)),Place::Field(FieldId(0))).unwrap();
        let y=TypedPlace::new(owner,Some(TypeId(8)),Place::Field(FieldId(1))).unwrap();
        let root=TypedPlace::new(owner,None,Place::Root).unwrap();
        assert!(!x.overlaps(y));
        assert!(x.overlaps(root));assert!(x.overlaps(x));
        assert!(!x.overlaps(TypedPlace::new(SymbolId(13),Some(TypeId(8)),Place::Field(FieldId(0))).unwrap()));
        assert!(TypedPlace::new(owner,None,Place::Field(FieldId(0))).is_none());
    }
    #[test] fn registering_verified_field_loans_makes_access_precise() {
        let (tokens,mut flow,owner,a,b)=example();
        let ax=TypedPlace::new(owner,Some(TypeId(7)),Place::Field(FieldId(0))).unwrap();
        let by=TypedPlace::new(owner,Some(TypeId(7)),Place::Field(FieldId(1))).unwrap();
        assert!(flow.register_typed_loan(a,ax));assert!(flow.register_typed_loan(b,by));
        assert_eq!(flow.typed_loan(a),Some(ax));
        assert_eq!(flow.inferred_local_region(a).unwrap().place,Place::Field(FieldId(0)));
        let pos=tokens.iter().position(|t|t.kind==K::Ident("read")).unwrap();
        assert!(!flow.conflicting_typed_access(pos,ax,PlaceAccessKind::Write).unwrap().is_empty());
        assert!(flow.conflicting_typed_access(pos,by,PlaceAccessKind::Read).unwrap().iter().all(|id|*id!=a));
        assert!(!flow.register_typed_loan(a,TypedPlace::new(SymbolId(999),None,Place::Root).unwrap()));
    }
    #[test] fn typed_accesses_are_recorded_at_exact_cfg_points() {
        let (tokens,mut flow,owner,a,_)=example();
        let place=TypedPlace::new(owner,Some(TypeId(7)),Place::Field(FieldId(0))).unwrap();
        assert!(flow.register_typed_loan(a,place));
        let read=tokens.iter().position(|t|t.kind==K::Ident("read")).unwrap();
        let _=flow.record_typed_access(read,place,PlaceAccessKind::Read).unwrap();
        assert_eq!(flow.typed_accesses().len(),1);
        assert_eq!(flow.typed_accesses()[0].point,flow.point_containing(read).unwrap());
        assert_eq!(flow.typed_accesses()[0].kind,PlaceAccessKind::Read);
        assert!(flow.record_typed_access(tokens.len()+10,place,PlaceAccessKind::Move).is_none());
        assert_eq!(flow.typed_accesses().len(),1);
    }
    #[test] fn only_the_typed_frontend_can_confirm_copy_vs_move() {
        let (tokens,mut flow,owner,_,_)=example();
        let place=TypedPlace::new(owner,None,Place::Root).unwrap();
        let token=tokens.iter().position(|t|t.kind==K::Ident("read")).unwrap();
        assert!(flow.record_typed_access(token,place,PlaceAccessKind::Read).is_some());
        assert!(flow.record_typed_access(token,place,PlaceAccessKind::Move).is_some());
        let recorded=flow.typed_accesses();
        assert_eq!(recorded.iter().map(|a|a.kind).collect::<Vec<_>>(),
            vec![PlaceAccessKind::Read,PlaceAccessKind::Move]);
    }
}

#[cfg(test)]
mod move_path_forest_tests_067 {
    use super::*;
    use crate::ir::MovePathId;

    #[test]
    fn roots_and_fields_get_stable_ids_with_parent_relationships() {
        let mut paths=MovePathForest::default();
        let owner=SymbolId(7);
        let a=TypedPlace::new(owner,Some(TypeId(2)),Place::Field(FieldId(0))).unwrap();
        let b=TypedPlace::new(owner,Some(TypeId(2)),Place::Field(FieldId(1))).unwrap();
        let a_id=paths.intern(a).unwrap();
        let b_id=paths.intern(b).unwrap();
        assert_ne!(a_id,b_id);
        assert_eq!(paths.intern(a),Some(a_id));
        let root=paths.get(TypedPlace{owner,field:None}).unwrap();
        assert_eq!(paths.nodes()[a_id.0 as usize].parent,Some(root));
        assert_eq!(paths.nodes()[b_id.0 as usize].parent,Some(root));
        assert_eq!(paths.nodes()[root.0 as usize].parent,None);
        assert_eq!(paths.nodes().len(),3);
        assert_eq!(root,MovePathId(0));
    }

    #[test]
    fn different_struct_types_and_owners_never_share_field_paths() {
        let mut paths=MovePathForest::default();
        let left=TypedPlace::new(SymbolId(1),Some(TypeId(1)),Place::Field(FieldId(0))).unwrap();
        let other_type=TypedPlace::new(SymbolId(1),Some(TypeId(2)),Place::Field(FieldId(0))).unwrap();
        let other_owner=TypedPlace::new(SymbolId(2),Some(TypeId(1)),Place::Field(FieldId(0))).unwrap();
        let id_a=paths.intern(left).unwrap();
        assert_ne!(id_a,paths.intern(other_type).unwrap());
        assert_ne!(id_a,paths.intern(other_owner).unwrap());
    }

    #[test]
    fn checked_move_and_reinitialization_emit_events_in_cfg_order() {
        let tokens=crate::syntax::lex("let p=3; p=4; let r=&p; read(r);").unwrap();
        let mut plan=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let declaration=tokens.iter().position(|t|t.kind==K::Ident("p")).unwrap();
        let owner=SymbolId((declaration+1) as u32);
        let write=tokens.iter().enumerate().find(|(i,t)|*i>declaration&&t.kind==K::Ident("p")).unwrap().0;
        let place=TypedPlace::new(owner,Some(TypeId(4)),Place::Field(FieldId(0))).unwrap();
        assert!(plan.record_typed_access(write,place,PlaceAccessKind::Move).is_some());
        assert!(plan.record_typed_access(write,place,PlaceAccessKind::Write).is_some());
        let events=plan.move_path_events();
        assert_eq!(events.len(),2);
        assert_eq!(events[0].kind,MovePathEventKind::Move);
        assert_eq!(events[1].kind,MovePathEventKind::Initialize);
        assert_eq!(events[0].path,events[1].path);
        assert_eq!(events[0].point,events[1].point);
    }
}

#[cfg(test)]
mod nll_bridge_tests_069 {
    use super::*;
    #[test]
    fn checked_loan_and_write_use_executable_cfg_points() {
        let source="let mut x=0;let r=&x;x=1;read(r);";
        let tokens=crate::syntax::lex(source).unwrap();
        let mut flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let first_x=tokens.iter().position(|t|t.kind==K::Ident("x")).unwrap();
        let r=tokens.iter().position(|t|t.kind==K::Ident("r")).unwrap();
        let second_x=tokens.iter().enumerate().find(|(i,t)|
            *i>r && t.kind==K::Ident("x") &&
            tokens.get(*i+1).is_some_and(|t|t.kind==K::Equal)).unwrap().0;
        let owner=SymbolId((first_x+1) as u32);
        let loan=SymbolId((r+1) as u32);
        let path=crate::cfg_borrow::Path::root(owner);
        flow.record_verified_loan(loan,r,path.clone(),false,None);
        flow.record_verified_path(second_x,path,PlaceAccessKind::Write);
        let conflicts=flow.verify_borrow_graph().unwrap();
        assert!(conflicts.iter().any(|conflict|conflict.token==second_x),
            "the independent CFG checker must find the verified write/loan conflict");
    }
}

#[cfg(test)]
mod compact_root_paths_0622_tests {
    use super::*;
    #[test]
    fn move_path_root_keys_are_symbol_ids_only() {
        let mut forest=MovePathForest::default();
        for owner in 0..512u32 {
            let root=TypedPlace{owner:SymbolId(owner),field:None};
            let id=forest.intern(root).unwrap();
            assert_eq!(id.0,owner);
            assert_eq!(forest.get(root),Some(id));
        }
        assert_eq!(forest.by_root.len(),512);
        assert!(forest.by_place.is_empty());
        let child=TypedPlace{owner:SymbolId(4),field:Some(TypedFieldId{
            aggregate:TypeId(8),field:FieldId(2),
        })};
        let child_id=forest.intern(child).unwrap();
        assert_eq!(forest.get(child),Some(child_id));
        assert_eq!(forest.nodes[child_id.0 as usize].parent,Some(crate::ir::MovePathId(4)));
    }
}

#[cfg(test)]
mod enum_pattern_cfg_nll_0642_tests {
    use super::*;

    fn nth(tokens:&[Token<'_>],name:&str,occurrence:usize)->usize {
        tokens.iter().enumerate().filter(|(_,t)|t.kind==K::Ident(name))
            .nth(occurrence).map(|(index,_)|index).expect("token exists")
    }

    #[test]
    fn mutable_pattern_binding_is_defined_on_its_own_arm_edge() {
        let source="let mut e=0;match &mut e {E::V(ref mut x)=>{use_x(x);after();},E::N=>{}}done();";
        let tokens=crate::syntax::lex(source).unwrap();
        let flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let id=SymbolId((nth(&tokens,"x",0)+1) as u32);
        let owner=SymbolId((nth(&tokens,"e",0)+1) as u32);
        assert_eq!(flow.origin(id),Some(owner));
        assert!(flow.tracks_pattern_loan(id));
        assert_eq!(flow.binding_at_token(nth(&tokens,"x",1)),Some(id));
        assert_eq!(flow.loan_live_at(nth(&tokens,"use_x",0),id),Some(true));
        assert_eq!(flow.loan_live_at(nth(&tokens,"after",0),id),Some(false));
        assert_eq!(flow.loan_live_at(nth(&tokens,"done",0),id),Some(false));
        let events=flow.loan_events_after(nth(&tokens,"use_x",0))
            .expect("CFG edge events available");
        assert!(events.iter().any(|edge|edge.events.iter().any(|event|
            event.loan==id && event.kind==LoanEdgeEventKind::Invalidate)));
    }

    #[test]
    fn same_spelling_in_different_match_arms_has_distinct_regions() {
        let source="let mut e=0;match &mut e {E::A(ref mut x)=>{read_a(x);},E::B(ref mut x)=>{read_b(x);}}done();";
        let tokens=crate::syntax::lex(source).unwrap();
        let flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let a=SymbolId((nth(&tokens,"x",0)+1) as u32);
        let b=SymbolId((nth(&tokens,"x",2)+1) as u32);
        assert_ne!(a,b);
        assert!(flow.tracks_pattern_loan(a));
        assert!(flow.tracks_pattern_loan(b));
        assert_eq!(flow.binding_at_token(nth(&tokens,"x",1)),Some(a));
        assert_eq!(flow.binding_at_token(nth(&tokens,"x",3)),Some(b));
        assert_eq!(flow.loan_live_at(nth(&tokens,"read_a",0),a),Some(true));
        assert_eq!(flow.loan_live_at(nth(&tokens,"read_a",0),b),Some(false));
        assert_eq!(flow.loan_live_at(nth(&tokens,"read_b",0),a),Some(false));
        assert_eq!(flow.loan_live_at(nth(&tokens,"read_b",0),b),Some(true));
    }

    #[test]
    fn nested_reborrow_extends_pattern_parent_only_until_child_dies() {
        let source="let mut e=0;match &mut e {E::V(ref mut x)=>{let child=&mut *x;read(child);later();}}";
        let tokens=crate::syntax::lex(source).unwrap();
        let flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let parent=SymbolId((nth(&tokens,"x",0)+1) as u32);
        let child=SymbolId((nth(&tokens,"child",0)+1) as u32);
        assert_eq!(flow.origin(child),Some(parent));
        assert!(flow.tracks_pattern_loan(parent));
        assert_eq!(flow.loan_live_at(nth(&tokens,"read",0),parent),Some(true));
        assert_eq!(flow.loan_live_at(nth(&tokens,"later",0),parent),Some(false));
    }

    #[test]
    fn incomplete_pattern_analysis_never_certifies_early_release() {
        let source="let mut e=0;match &mut e {E::V((ref mut x))=>{read(x);}}";
        let tokens=crate::syntax::lex(source).unwrap();
        let flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let id=SymbolId((nth(&tokens,"x",0)+1) as u32);
        assert!(!flow.tracks_pattern_loan(id));
    }

    #[test]
    fn owned_pattern_local_is_not_mistaken_for_an_enum_borrow() {
        let source="let e=0;match e {E::V(value)=>{use_value(value);}}done();";
        let tokens=crate::syntax::lex(source).unwrap();
        let flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let id=SymbolId((nth(&tokens,"value",0)+1) as u32);
        assert_eq!(flow.binding_at_token(nth(&tokens,"value",1)),Some(id));
        assert!(!flow.tracks_pattern_loan(id));
    }
}

#[cfg(test)]
mod nested_pattern_bindings_0644_tests {
    use super::*;
    #[test]
    fn nested_binders_resolve_to_their_own_arm(){
        let src="match &e{E::V(Inner::Pair(P{n:ref x},_))=>{use_ref(x);},_=>{}}";
        let tokens=crate::syntax::lex(src).unwrap();
        let result=match_pattern_arms(&tokens,0,tokens.len()).unwrap();
        assert_eq!(result.2.len(),2);
        assert_eq!(result.2[0].1.len(),1);
        assert_eq!(result.2[0].1[0].1,"x");
        assert!(result.2[0].1[0].2);
    }
}

#[cfg(test)]
mod enum_pattern_last_use_0644_fix1_tests {
    use super::*;

    fn pattern_flow(source:&str)->(Vec<Token<'_>>,usize,usize) {
        let tokens=crate::syntax::lex(source).expect("valid lexical input");
        let owner=tokens.iter().position(|t|t.kind==K::Ident("e")).unwrap();
        let binding=tokens.iter().position(|t|t.kind==K::Ident("x")).unwrap();
        (tokens,owner,binding)
    }

    #[test]
    fn flat_enum_pattern_can_end_after_last_use_with_verified_variant_path() {
        let (tokens,owner,binding)=pattern_flow(
            "let mut e=0;match &mut e{E::V(ref mut x)=>{use_x(x);later();}}");
        let mut flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let id=SymbolId((binding+1) as u32);
        let owner=SymbolId((owner+1) as u32);
        assert!(flow.tracks_pattern_loan(id));
        assert!(!flow.verified_pattern_loan(id),"a lexical name alone is not proof");
        flow.verified_borrow_paths.insert(id,crate::cfg_borrow::Path::root(owner));
        assert!(!flow.verified_pattern_loan(id),"root-only proof is not a variant loan");
        flow.verified_borrow_paths.insert(id,
            crate::cfg_borrow::Path::root(owner).child(crate::cfg_borrow::FieldKey{
                aggregate:TypeId(3),field:FieldId(0x8000_0000),
            }));
        assert!(flow.verified_pattern_loan(id),
            "the verified direct variant path must enable 0.6.42 NLL last-use");
        flow.verified_borrow_paths.insert(id,
            crate::cfg_borrow::Path::root(SymbolId(owner.0+123))
                .child(crate::cfg_borrow::FieldKey{
                    aggregate:TypeId(3),field:FieldId(0x8000_0000),
                }));
        assert!(!flow.verified_pattern_loan(id),
            "a variant projection must belong to the pattern's original owner");
    }

    #[test]
    fn nested_enum_pattern_does_not_claim_unproven_deep_last_use() {
        let (tokens,owner,binding)=pattern_flow(
            "let mut e=0;match &mut e{E::V(I::W(ref mut x))=>{use_x(x);later();}}");
        let mut flow=FlowPlan::new(&tokens,0..tokens.len(),true,0,&[]);
        let id=SymbolId((binding+1) as u32);
        let owner=SymbolId((owner+1) as u32);
        assert!(flow.tracks_pattern_loan(id));
        let path=crate::cfg_borrow::Path::root(owner)
            .child(crate::cfg_borrow::FieldKey{aggregate:TypeId(3),field:FieldId(0x8000_0000)})
            .child(crate::cfg_borrow::FieldKey{aggregate:TypeId(4),field:FieldId(0)});
        flow.verified_borrow_paths.insert(id,path);
        assert!(!flow.verified_pattern_loan(id),
            "deep projections still retain RefLease until the arm exits");
    }
}

#[cfg(test)]
mod deep_typed_pattern_nll_0645_tests {
    use super::*;
    use crate::cfg_borrow::{FieldKey,Path};

    fn path(owner:SymbolId,a:u32,b:u32,c:u32)->Path{
        Path{owner,fields:vec![
            FieldKey{aggregate:TypeId(2),field:FieldId(0x8000_0000|a)},
            FieldKey{aggregate:TypeId(3),field:FieldId(0x8000_0000|b)},
            FieldKey{aggregate:TypeId(4),field:FieldId(c)},
        ]}
    }
    #[test]
    fn verified_deep_places_have_exact_ancestors_and_disjoint_siblings(){
        let owner=SymbolId(17);
        let a=TypedPlacePath::from_verified(&path(owner,0,0,0)).unwrap();
        let b=TypedPlacePath::from_verified(&path(owner,0,0,1)).unwrap();
        let prefix=a.parent().unwrap();
        assert!(prefix.ancestor_of(&a));
        assert!(prefix.overlaps(&b));
        assert!(!a.overlaps(&b));
        assert_eq!(a.raw_place().unwrap().indices().len(),3);
        assert!(!a.overlaps(&TypedPlacePath::from_verified(&path(SymbolId(18),0,0,0)).unwrap()));
    }
    #[test]
    fn forged_aggregate_chain_is_never_identical_to_verified_provenance(){
        let a=path(SymbolId(21),1,2,0);
        let mut b=a.clone();b.fields[1].aggregate=TypeId(999);
        let place=TypedPlacePath::from_verified(&a).unwrap();
        assert!(place.matches_verified(&a));
        assert!(!place.matches_verified(&b));
        let other=TypedPlacePath::from_verified(&b).unwrap();
        assert!(place.overlaps(&other),"untrusted aggregate mismatch must overlap");
    }
    #[test]
    fn nested_variant_paths_do_not_alias_sibling_variants(){
        let a=TypedPlacePath::from_verified(&path(SymbolId(5),0,0,0)).unwrap();
        let b=TypedPlacePath::from_verified(&path(SymbolId(5),16,0,0)).unwrap();
        assert!(!a.overlaps(&b));
    }
}
