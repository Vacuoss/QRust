//Compact typed Quantum IR
use crate::ids::{BitId, QubitId};
use std::{cell::{Cell, RefCell}, rc::Rc};
use crate::sema::GateId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpCode { Gate(GateId), Measure, MeasureInto, Reset, Barrier, IfBit, Else, EndIf, WhileBit, EndWhile }

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct FieldId(pub u32);
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct VariantId(pub u32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstType { I64, U64, Bool, Named(String), Generic(String), Resolved(TypeId),
    Ref(Box<ConstType>), RefMut(Box<ConstType>), Unit }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstValue {
    I64(i64), U64(u64), Bool(bool),
    Struct(TypeId, Vec<ConstValue>),
    Enum(TypeId, VariantId),
    EnumData(TypeId, VariantId, Vec<ConstValue>),
    Ref(RefValue), Unit,
}
impl ConstValue {
    pub fn ty(&self)->ConstType {match self {Self::I64(_)=>ConstType::I64,
        Self::U64(_)=>ConstType::U64,Self::Bool(_)=>ConstType::Bool,
        Self::Struct(id,_)|Self::Enum(id,_)|Self::EnumData(id,_,_)=>ConstType::Resolved(*id),
        Self::Ref(reference)=>if reference.0.mutable {ConstType::RefMut(Box::new(reference.0.item_type.clone()))}
            else{ConstType::Ref(Box::new(reference.0.item_type.clone()))},
        Self::Unit=>ConstType::Unit}}
    pub fn matches(&self, ty:&ConstType)->bool {
        match (self,ty) {
            (Self::I64(_),ConstType::I64)|(Self::U64(_),ConstType::U64)
                |(Self::Bool(_),ConstType::Bool)=>true,
            (Self::Struct(id,_)|Self::Enum(id,_)|Self::EnumData(id,_,_),ConstType::Resolved(expected))=>id==expected,
            (Self::Ref(_), ConstType::Ref(_)|ConstType::RefMut(_))=>&self.ty()==ty,
            (Self::Unit,ConstType::Unit)=>true,
            _=>false,
        }
    }
    pub fn is_copy(&self)->bool {matches!(self,Self::I64(_)|Self::U64(_)|Self::Bool(_)) ||
        matches!(self,Self::Ref(reference) if !reference.0.mutable)}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DeepPath {pub len:u8, pub fields:[FieldId;64]}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Place { Root, Field(FieldId), Deep(DeepPath) }
impl Place {
    pub fn from_field(field: Option<FieldId>) -> Self {
        match field { Some(index) => Self::Field(index), None => Self::Root }
    }
    pub fn from_fields(fields:&[FieldId])->Option<Self>{
        match fields {
            []=>Some(Self::Root),[field]=>Some(Self::Field(*field)),
            _ if fields.len()<=64=>{
                let mut out=[FieldId(0);64];out[..fields.len()].copy_from_slice(fields);
                Some(Self::Deep(DeepPath{len:fields.len() as u8,fields:out}))
            },
            _=>None,
        }
    }
    pub fn indices(&self)->&[FieldId]{
        match self {Self::Root=>&[],Self::Field(id)=>std::slice::from_ref(id),
            Self::Deep(deep)=>&deep.fields[..deep.len as usize]}
    }
    pub fn field(self) -> Option<FieldId> {
        match self {Self::Root|Self::Deep(_)=>None, Self::Field(index) => Some(index)}
    }
    pub fn overlaps(self,other:Self)->bool {
        let a=self.indices();let b=other.indices();
        a.iter().zip(b).all(|(l,r)|l==r)
    }
}

//Compilation-local identity for a root or typed field move path. Never a QPU ID
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct MovePathId(pub u32);

#[derive(Debug, Default)]
pub struct MovePathState { moved_paths: Vec<Vec<FieldId>> }
impl MovePathState {
    pub fn whole_initialized(&self)->bool {self.moved_paths.is_empty()}
    pub fn field_initialized(&self,field:FieldId)->bool {self.path_initialized(&[field])}
    pub fn path_initialized(&self,path:&[FieldId])->bool {
        !self.moved_paths.iter().any(|m|
            m.starts_with(path) || path.starts_with(m))
    }
    pub fn ancestors_present(&self,path:&[FieldId])->bool {
        !self.moved_paths.iter().any(|m|m.len()<path.len() && path.starts_with(m))
    }
    pub fn mark_moved(&mut self,field:FieldId)->bool {self.mark_path_moved(&[field])}
    pub fn mark_path_moved(&mut self,path:&[FieldId])->bool {
        if path.is_empty() || !self.path_initialized(path){return false;}
        self.moved_paths.push(path.to_vec());true
    }
    pub fn mark_initialized(&mut self,field:FieldId){self.mark_path_initialized(&[field]);}
    pub fn mark_path_initialized(&mut self,path:&[FieldId]) {
        self.moved_paths.retain(|m|!m.starts_with(path));
    }
    pub fn initialize_whole(&mut self){self.moved_paths.clear();}
}

#[derive(Debug)]
pub struct RefSlot {
    pub val: Option<ConstValue>, pub mutable: bool, pub alive: bool,
    pub loans: Vec<(u64, bool, Place)>, pub next_loan: u64,
    pub move_paths: MovePathState,
}

#[derive(Debug)]
pub struct ReturnOriginGuard {
    pub owner: Rc<RefCell<RefSlot>>,
    pub key: u64,
}

//One logical borrow. Clones of an immutable reference share this lease; the exclusivity lock is
//released only when its final handle is dropped
#[derive(Debug)]
pub struct RefLease {
    pub owner: Rc<RefCell<RefSlot>>, pub place: Place,
    pub mutable: bool, pub item_type: ConstType, pub key: u64,
    //Derived shared field references retain their parent loan
    pub parent: Option<Rc<RefLease>>, pub registered: bool,
    pub active_children: Cell<u32>,
    pub active_exclusive_child: Cell<bool>,
    pub return_origin_guards: RefCell<Vec<ReturnOriginGuard>>,
}
impl RefLease {
    pub fn owns_return_origin_guard(&self, owner:&Rc<RefCell<RefSlot>>, key:u64)->bool {
        let mut current=Some(self);
        while let Some(lease)=current {
            if lease.return_origin_guards.borrow().iter().any(|guard|
                guard.key==key && Rc::ptr_eq(&guard.owner,owner)) {
                return true;
            }
            current=lease.parent.as_deref();
        }
        false
    }
}
impl Drop for RefLease {
    fn drop(&mut self) {
        for guard in self.return_origin_guards.get_mut().drain(..) {
            guard.owner.borrow_mut().loans.retain(|(key,_,_)| *key != guard.key);
        }
        if let Some(parent)=self.parent.as_ref(){
            if parent.mutable {
                debug_assert!(parent.active_children.get()>0);
                parent.active_children.set(parent.active_children.get()-1);
                if self.mutable {parent.active_exclusive_child.set(false);}
            }
        }
        if self.registered {
            self.owner.borrow_mut().loans.retain(|(key,_,_)| *key != self.key);
        }
    }
}
#[derive(Clone, Debug)]
pub struct RefValue(pub Rc<RefLease>);
impl PartialEq for RefValue {
    fn eq(&self, other: &Self) -> bool { Rc::ptr_eq(&self.0,&other.0) }
}
impl Eq for RefValue {}

#[derive(Clone, Copy, Debug)]
pub struct Instruction {
    pub opcode: OpCode,
    pub qubits: [QubitId; 3],
    pub bit: BitId,
    pub offset: u32,
    pub count: u32,
}

#[derive(Debug)]
pub struct Program {
    pub qubits: usize,
    pub bits: usize,
    pub instructions: Vec<Instruction>,
    pub angles: Vec<f64>,
    pub barrier_qubits: Vec<QubitId>,
}
impl Program {
    pub fn with_capacity(n: usize) -> Self {
        Self { qubits: 0, bits: 0, instructions: Vec::with_capacity(n),
            angles: Vec::new(), barrier_qubits: Vec::new() }
    }
    pub fn gate(&mut self, id: GateId, operands: [QubitId; 3], values: &[f64]) {
        let offset = u32::try_from(self.angles.len()).expect("angle pool exceeds u32");
        self.angles.extend_from_slice(values);
        self.instructions.push(Instruction { opcode: OpCode::Gate(id), qubits: operands,
            bit: BitId(0), offset, count: values.len() as u32 });
    }
    pub fn gate_prechecked(&mut self, id: GateId, operands: [QubitId; 3], values: &[f64]) {
        debug_assert!(values.len() <= 4);
        let offset = u32::try_from(self.angles.len()).expect("angle pool exceeds u32");
        match values {
            [] => (),
            [value] => self.angles.push(*value),
            _ => self.angles.extend_from_slice(values),
        }
        self.instructions.push(Instruction { opcode: OpCode::Gate(id), qubits: operands,
            bit: BitId(0), offset, count: values.len() as u32 });
    }
    pub fn measure(&mut self, qubit: QubitId) -> BitId {
        let bit = BitId(u32::try_from(self.bits).expect("bit count exceeds u32"));
        self.bits += 1;
        self.instructions.push(Instruction { opcode: OpCode::Measure,
            qubits: [qubit, QubitId(0), QubitId(0)], bit, offset: 0, count: 0 });
        bit
    }
    pub fn measure_into(&mut self, bit: BitId, qubit: QubitId) {
        self.instructions.push(Instruction { opcode: OpCode::MeasureInto,
            qubits: [qubit, QubitId(0), QubitId(0)], bit, offset: 0, count: 0 });
    }
    pub fn reset(&mut self, qubit: QubitId) {
        self.instructions.push(Instruction { opcode: OpCode::Reset,
            qubits: [qubit, QubitId(0), QubitId(0)], bit: BitId(0), offset: 0, count: 0 });
    }
    pub fn barrier(&mut self, operands: &[QubitId]) {
        let offset = u32::try_from(self.barrier_qubits.len()).expect("barrier pool exceeds u32");
        self.barrier_qubits.extend_from_slice(operands);
        self.instructions.push(Instruction { opcode: OpCode::Barrier,
            qubits: [QubitId(0); 3], bit: BitId(0), offset, count: operands.len() as u32 });
    }
    pub fn begin_if(&mut self, bit: BitId, expected: bool) {
        self.instructions.push(Instruction { opcode: OpCode::IfBit,
            qubits: [QubitId(0); 3], bit, offset: 0, count: u32::from(expected) });
    }
    pub fn else_branch(&mut self) {
        self.instructions.push(Instruction { opcode: OpCode::Else,
            qubits: [QubitId(0); 3], bit: BitId(0), offset: 0, count: 0 });
    }
    pub fn end_if(&mut self) {
        self.instructions.push(Instruction { opcode: OpCode::EndIf,
            qubits: [QubitId(0); 3], bit: BitId(0), offset: 0, count: 0 });
    }
    pub fn begin_while(&mut self, bit: BitId, expected: bool) {
        self.instructions.push(Instruction { opcode: OpCode::WhileBit,
            qubits: [QubitId(0); 3], bit, offset: 0, count: u32::from(expected) });
    }
    pub fn end_while(&mut self) {
        self.instructions.push(Instruction { opcode: OpCode::EndWhile,
            qubits: [QubitId(0); 3], bit: BitId(0), offset: 0, count: 0 });
    }
    pub fn repeat_recent_gates(&mut self, start: usize, angle_start: usize, times: usize) {
        debug_assert!(times >= 2);
        let template = self.instructions[start..].to_vec();
        debug_assert!(!template.is_empty());
        debug_assert!(template.iter().all(|op| matches!(op.opcode, OpCode::Gate(_))));
        let angles = self.angles[angle_start..].to_vec();
        let more = template.len().checked_mul(times - 1).expect("too many repeated gates");
        self.instructions.reserve(more);
        self.angles.reserve(angles.len().checked_mul(times - 1).expect("too many angles"));
        for _ in 1..times {
            let base = u32::try_from(self.angles.len()).expect("angle pool exceeds u32");
            for original in &template {
                let mut instruction = *original;
                instruction.offset = base.checked_add(original.offset - angle_start as u32)
                    .expect("angle pool exceeds u32");
                self.instructions.push(instruction);
            }
            self.angles.extend_from_slice(&angles);
        }
    }

    pub fn estimated_storage_bytes(&self) -> usize {
        self.instructions.capacity() * std::mem::size_of::<Instruction>() +
        self.angles.capacity() * std::mem::size_of::<f64>() +
        self.barrier_qubits.capacity() * std::mem::size_of::<QubitId>()
    }
}

#[cfg(test)]
mod move_path_state_tests_067 {
    use super::*;
    #[test]
    fn moving_one_field_keeps_sibling_initialized_and_reinitializes_whole_root() {
        let mut s=MovePathState::default();
        assert!(s.whole_initialized());
        assert!(s.mark_moved(FieldId(0)));
        assert!(!s.mark_moved(FieldId(0)));
        assert!(!s.whole_initialized());
        assert!(!s.field_initialized(FieldId(0)));
        assert!(s.field_initialized(FieldId(1)));
        s.mark_initialized(FieldId(0));
        assert!(s.whole_initialized());
        assert!(s.mark_moved(FieldId(1)));
        s.initialize_whole();
        assert!(s.whole_initialized());
    }
}

#[cfg(test)]
mod nested_move_path_state_tests_068 {
    use super::*;
    #[test]fn arbitrary_depth_paths_preserve_disjoint_siblings(){
        let mut s=MovePathState::default();
        let moved=[FieldId(0),FieldId(1),FieldId(2),FieldId(3),FieldId(4)];
        assert!(s.mark_path_moved(&moved));
        assert!(!s.whole_initialized());
        assert!(!s.path_initialized(&moved[..3]));
        assert!(!s.path_initialized(&moved));
        assert!(s.path_initialized(&[FieldId(0),FieldId(1),FieldId(8)]));
        assert!(s.ancestors_present(&[FieldId(0),FieldId(1),FieldId(8)]));
        s.mark_path_initialized(&moved);
        assert!(s.whole_initialized());
    }
}
