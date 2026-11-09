//Backend ABI for the bounded hybrid runtime
use crate::{local_sim::LiveQuantum,sema::GateId};

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum BackendKind { Local, Qpc }
impl BackendKind {
    pub fn parse(s:&str)->Result<Self,String>{match s{
        "local"|"sim"=>Ok(Self::Local),
        "qpc"=>Ok(Self::Qpc),
        _=>Err(format!("unknown backend '{s}' (expected local or qpc)")),
    }}
}

pub trait QuantumBackend {
    fn allocate(&mut self)->Result<usize,String>;
    fn apply(&mut self,gate:GateId,qubits:&[usize],params:&[f64])->Result<(),String>;
    fn measure(&mut self,qubit:usize)->Result<bool,String>;
    fn measure_and_release(&mut self,qubit:usize)->Result<bool,String>;
    fn reset(&mut self,qubit:usize)->Result<(),String>;
}
impl QuantumBackend for LiveQuantum {
    fn allocate(&mut self)->Result<usize,String>{LiveQuantum::allocate(self)}
    fn apply(&mut self,gate:GateId,qubits:&[usize],params:&[f64])->Result<(),String>{LiveQuantum::apply(self,gate,qubits,params)}
    fn measure(&mut self,qubit:usize)->Result<bool,String>{LiveQuantum::measure(self,qubit)}
    fn measure_and_release(&mut self,qubit:usize)->Result<bool,String>{LiveQuantum::measure_and_release(self,qubit)}
    fn reset(&mut self,qubit:usize)->Result<(),String>{LiveQuantum::reset(self,qubit)}
}

pub fn create(kind:BackendKind,seed:u64)->Result<Box<dyn QuantumBackend>,String>{
    match kind {
        BackendKind::Local=>Ok(Box::new(LiveQuantum::new(seed))),
        BackendKind::Qpc=>Err("QPC hardware backend unavailable: no validated hardware adapter installed (simulation not substituted)".into()),
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn qpc_selection_fails_closed(){
        assert!(create(BackendKind::Qpc,1).err().unwrap().contains("unavailable"));
    }
    #[test] fn local_backend_is_usable(){
        let mut q=create(BackendKind::Local,42).unwrap();
        let id=q.allocate().unwrap();q.apply(GateId::X,&[id],&[]).unwrap();
        assert!(q.measure_and_release(id).unwrap());
    }
}
