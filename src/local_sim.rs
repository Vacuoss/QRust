//Bounded, dependency-free state-vector executor for checked QRust quantum IR
use std::collections::BTreeMap;
use std::ops::{Add, Mul, Neg, Sub};
use crate::ir::{OpCode, Program};
use crate::sema::GateId;

const MAX_QUBITS: usize = 16;
const MAX_SHOTS: usize = 10_000;
const MAX_EXECUTED_STEPS: u64 = 10_000_000;

#[derive(Clone, Copy, Debug, Default)]
struct C { r: f64, i: f64 }
impl C {
    const ZERO: Self = Self {r: 0., i: 0.};
    const ONE: Self = Self {r: 1., i: 0.};
    const fn new(r:f64,i:f64)->Self {Self{r,i}}
    fn phase(theta:f64)->Self {Self::new(theta.cos(),theta.sin())}
    fn scale(self,x:f64)->Self {Self::new(self.r*x,self.i*x)}
    fn norm(self)->f64 {self.r*self.r+self.i*self.i}
}
impl Add for C { type Output=Self; fn add(self,b:Self)->Self{Self::new(self.r+b.r,self.i+b.i)} }
impl Sub for C { type Output=Self; fn sub(self,b:Self)->Self{Self::new(self.r-b.r,self.i-b.i)} }
impl Neg for C { type Output=Self; fn neg(self)->Self{Self::new(-self.r,-self.i)} }
impl Mul for C { type Output=Self; fn mul(self,b:Self)->Self{Self::new(self.r*b.r-self.i*b.i,self.r*b.i+self.i*b.r)} }

type Matrix = [C;4];
fn unitary(theta:f64,phi:f64,lambda:f64)->Matrix{
    let c=theta.mul_add(0.5,0.).cos();
    let s=(theta*0.5).sin();
    [C::new(c,0.),-C::phase(lambda).scale(s),C::phase(phi).scale(s),C::phase(phi+lambda).scale(c)]
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Counts { pub histogram:BTreeMap<String,u64>, pub shots:usize }

struct Machine { amplitudes:Vec<C>, bits:Vec<bool>, rng:u64 }
impl Machine {
    fn new(qubits:usize,bits:usize,seed:u64)->Self {
        let mut amplitudes=vec![C::ZERO;1usize<<qubits];
        amplitudes[0]=C::ONE;
        Self{amplitudes,bits:vec![false;bits],rng:if seed==0{0x9E3779B97F4A7C15}else{seed}}
    }
    fn random(&mut self)->f64 {
        let mut x=self.rng;
        x^=x>>12;x^=x<<25;x^=x>>27;self.rng=x;
        let n=x.wrapping_mul(0x2545F4914F6CDD1D);
        ((n>>11) as f64)*(1./9007199254740992.)
    }
    fn transform(&mut self,target:usize,control:usize,m:Matrix) {
        let mask=1usize<<target;
        let ctl=if control==usize::MAX{0}else{1usize<<control};
        for idx in 0..self.amplitudes.len() {
            if idx&mask!=0 || (ctl!=0 && idx&ctl==0){continue;}
            let other=idx|mask;
            let a=self.amplitudes[idx];let b=self.amplitudes[other];
            self.amplitudes[idx]=m[0]*a+m[1]*b;
            self.amplitudes[other]=m[2]*a+m[3]*b;
        }
    }
    fn swap(&mut self,a:usize,b:usize,control:usize) {
        let a=1usize<<a;let b=1usize<<b;
        let ctl=if control==usize::MAX{0}else{1usize<<control};
        for idx in 0..self.amplitudes.len() {
            if idx&a==0 && idx&b!=0 && (ctl==0 || idx&ctl!=0) {
                self.amplitudes.swap(idx,idx^a^b);
            }
        }
    }
    fn phase_if(&mut self,mask:usize,phase:C) {
        for (idx,amp) in self.amplitudes.iter_mut().enumerate(){if idx&mask==mask{*amp=*amp*phase;}}
    }
    fn zz(&mut self,a:usize,b:usize,theta:f64) {
        let a=1usize<<a;let b=1usize<<b;
        let plus=C::phase(theta*0.5);let minus=C::phase(-theta*0.5);
        for (idx,amp) in self.amplitudes.iter_mut().enumerate(){*amp=*amp*if (idx&a==0)==(idx&b==0){minus}else{plus};}
    }
    fn xx_yy(&mut self,a:usize,b:usize,theta:f64,yy:bool) {
        let a=1usize<<a;let b=1usize<<b;
        let mask=a|b;let c=(theta*0.5).cos();let neg_i=C::new(0.,-(theta*0.5).sin());
        for idx in 0..self.amplitudes.len(){
            let other=idx^mask;
            if idx>=other{continue;}
            let sign=if yy && ((idx&a==0)==(idx&b==0)){-1.}else{1.};
            let v=self.amplitudes[idx];let w=self.amplitudes[other];
            self.amplitudes[idx]=v.scale(c)+neg_i.scale(sign)*w;
            self.amplitudes[other]=w.scale(c)+neg_i.scale(sign)*v;
        }
    }
    fn measure(&mut self,qubit:usize)->bool {
        let mask=1usize<<qubit;
        let p1:f64=self.amplitudes.iter().enumerate().filter(|(i,_)|*i&mask!=0).map(|(_,c)|c.norm()).sum();
        let outcome=self.random()<p1.clamp(0.,1.);
        let probability=if outcome{p1}else{1.-p1};
        //Reject no state: p1=0 and zero probability outcomes cannot be sampled
        let inv=if probability>0.{1./probability.sqrt()}else{0.};
        for (i,amp) in self.amplitudes.iter_mut().enumerate(){
            if (i&mask!=0)==outcome{*amp=amp.scale(inv);}else{*amp=C::ZERO;}
        }
        outcome
    }
}

fn gate(m:&mut Machine, id:GateId, qubits:[usize;3], a:&[f64])->Result<(),String> {
    use GateId::*;
    let q=qubits[0];let t=qubits[1];let c=qubits[2];
    let one=C::ONE;let z=C::ZERO;let i=C::new(0.,1.);
    let isqrt=std::f64::consts::FRAC_1_SQRT_2;
    let matrix=match id {
        ID=>Some([one,z,z,one]),
        H=>Some([C::new(isqrt,0.),C::new(isqrt,0.),C::new(isqrt,0.),C::new(-isqrt,0.)]),
        X=>Some([z,one,one,z]),
        Y=>Some([z,-i,i,z]),
        Z=>Some([one,z,z,-one]),
        S=>Some([one,z,z,i]),
        SDG=>Some([one,z,z,-i]),
        T=>Some([one,z,z,C::phase(std::f64::consts::FRAC_PI_4)]),
        TDG=>Some([one,z,z,C::phase(-std::f64::consts::FRAC_PI_4)]),
        SX=>Some([(one+i).scale(0.5),(one-i).scale(0.5),(one-i).scale(0.5),(one+i).scale(0.5)]),
        P=>Some([one,z,z,C::phase(a[0])]),
        RX=>{let co=(a[0]*0.5).cos();let off=C::new(0.,-(a[0]*0.5).sin());Some([C::new(co,0.),off,off,C::new(co,0.)])},
        RY=>{let co=(a[0]*0.5).cos();let si=(a[0]*0.5).sin();Some([C::new(co,0.),C::new(-si,0.),C::new(si,0.),C::new(co,0.)])},
        RZ=>Some([C::phase(-a[0]*0.5),z,z,C::phase(a[0]*0.5)]),
        U|U3=>Some(unitary(a[0],a[1],a[2])),
        U2=>Some(unitary(std::f64::consts::FRAC_PI_2,a[0],a[1])),
        CX|CY|CZ|CH|SWAP|CP|CRX|CRY|CRZ|CU|CCX|CSWAP|GPHASE|RXX|RYY|RZZ|LEGACY_CX=>None,
    };
    if let Some(matrix)=matrix{m.transform(q,usize::MAX,matrix);return Ok(());}
    match id {
        CX=>m.transform(t,q,[z,one,one,z]),
        CY=>m.transform(t,q,[z,-i,i,z]),
        CZ=>m.phase_if((1<<q)|(1<<t),-one),
        CH=>m.transform(t,q,[C::new(isqrt,0.),C::new(isqrt,0.),C::new(isqrt,0.),C::new(-isqrt,0.)]),
        SWAP=>m.swap(q,t,usize::MAX),
        CP=>m.phase_if((1<<q)|(1<<t),C::phase(a[0])),
        CRX=>{let co=(a[0]*0.5).cos();let off=C::new(0.,-(a[0]*0.5).sin());m.transform(t,q,[C::new(co,0.),off,off,C::new(co,0.)]);},
        CRY=>{let co=(a[0]*0.5).cos();let si=(a[0]*0.5).sin();m.transform(t,q,[C::new(co,0.),C::new(-si,0.),C::new(si,0.),C::new(co,0.)]);},
        CRZ=>m.transform(t,q,[C::phase(-a[0]*0.5),z,z,C::phase(a[0]*0.5)]),
        CU=>{
            let mut matrix=unitary(a[0],a[1],a[2]);
            let phase=C::phase(a[3]);
            for item in &mut matrix{*item=*item*phase;}
            m.transform(t,q,matrix);
        },
        CCX=>{
            let bit_q=1<<q;let bit_t=1<<t;let bit_c=1<<c;
            for idx in 0..m.amplitudes.len(){
                if idx&bit_q!=0 && idx&bit_t!=0 && idx&bit_c==0 {
                    m.amplitudes.swap(idx,idx|bit_c);
                }
            }
        },
        CSWAP=>m.swap(t,c,q),
        GPHASE=>{let phase=C::phase(a[0]);for value in &mut m.amplitudes{*value=*value*phase;}},
        RZZ=>m.zz(q,t,a[0]),
        RXX=>m.xx_yy(q,t,a[0],false),
        RYY=>m.xx_yy(q,t,a[0],true),
        //Legacy CX is kept distinct in QRust's IR and emitter Do not silently assert it has exactly the
        //standard CX unitary
        LEGACY_CX=>return Err("local simulator does not implement legacy phase-sensitive CX; use QASM backend".into()),
        _=>unreachable!("single-qubit gate dispatched above"),
    }
    Ok(())
}

pub(crate) struct LiveQuantum {
    machine: Machine,
    qubits: usize,
    free:Vec<usize>,
}
impl LiveQuantum {
    pub(crate) fn new(seed: u64) -> Self { Self {machine:Machine::new(0,0,seed),qubits:0,free:Vec::new()} }
    pub(crate) fn allocate(&mut self) -> Result<usize,String> {
        if let Some(reusable)=self.free.pop(){return Ok(reusable);}
        if self.qubits >= MAX_QUBITS {return Err(format!("hybrid runtime supports at most {MAX_QUBITS} simultaneous allocated qubits"));}
        let id=self.qubits;
        self.qubits += 1;
        let len=self.machine.amplitudes.len();
        self.machine.amplitudes.resize(len*2,C::ZERO);
        Ok(id)
    }
    pub(crate) fn apply(&mut self,id:GateId, qubits:&[usize], params:&[f64]) -> Result<(),String> {
        let spec=crate::sema::gate_spec(id);
        if qubits.len()!=spec.qubits || params.len()!=spec.parameters {return Err("gate argument count mismatch".into());}
        if qubits.iter().any(|&q|q>=self.qubits) {return Err("unallocated quantum operand".into());}
        let mut ids=[0usize;3];
        for (dest,source) in ids.iter_mut().zip(qubits){*dest=*source;}
        if qubits.len()>1 && (0..qubits.len()).any(|i|(i+1..qubits.len()).any(|j|qubits[i]==qubits[j])) {
            return Err("duplicate quantum resource in multi-qubit gate".into());
        }
        gate(&mut self.machine,id,ids,params)
    }
    pub(crate) fn measure(&mut self,q:usize)->Result<bool,String> {
        if q>=self.qubits {return Err("unallocated quantum operand".into());}
        Ok(self.machine.measure(q))
    }
    pub(crate) fn measure_and_release(&mut self,q:usize)->Result<bool,String>{
        let bit=self.measure(q)?;
        if bit{self.apply(GateId::X,&[q],&[])?;}
        self.free.push(q);
        Ok(bit)
    }
    pub(crate) fn reset(&mut self,q:usize)->Result<(),String> {
        if self.measure(q)? {self.apply(GateId::X,&[q],&[])?;}
        Ok(())
    }
}

//Branch jump target = the first instruction after a branch we must skip
fn jumps(program:&Program)->Result<Vec<usize>,String>{
    enum Frame {If{start:usize,els:Option<usize>},While{start:usize}}
    let mut stack=Vec::new();
    let mut jumps=vec![0;program.instructions.len()];
    for (index,ins) in program.instructions.iter().enumerate(){
        match ins.opcode {
            OpCode::IfBit=>stack.push(Frame::If{start:index,els:None}),
            OpCode::WhileBit=>stack.push(Frame::While{start:index}),
            OpCode::Else=>match stack.last_mut() {
                Some(Frame::If{els,..}) if els.is_none()=>*els=Some(index),
                _=>return Err("malformed runtime else".into()),
            },
            OpCode::EndIf=>match stack.pop(){
                Some(Frame::If{start,els})=>{
                    jumps[start]=els.map_or(index+1,|e|e+1);
                    if let Some(e)=els{jumps[e]=index+1;}
                },
                _=>return Err("malformed runtime endif".into()),
            },
            OpCode::EndWhile=>match stack.pop(){
                Some(Frame::While{start})=>{jumps[start]=index+1;jumps[index]=start;},
                _=>return Err("malformed runtime endwhile".into()),
            },
            _=>(),
        }
    }
    if !stack.is_empty(){return Err("unterminated runtime control block".into());}
    Ok(jumps)
}

fn bitstring(bits:&[bool])->String {
    if bits.is_empty(){return String::from("(no classical bits)");}
    bits.iter().rev().map(|b|if *b{'1'}else{'0'}).collect()
}

pub fn simulate(program:&Program,shots:usize,seed:u64)->Result<Counts,String>{
    if !(1..=MAX_SHOTS).contains(&shots){return Err(format!("shots must be 1..={MAX_SHOTS}"));}
    if program.qubits>MAX_QUBITS{return Err(format!("local simulator supports at most {MAX_QUBITS} qubits; use QASM for larger circuits"));}
    let control=jumps(program)?;
    let mut steps=0u64;
    let mut histogram=BTreeMap::new();
    let mut run_seed=seed;
    for _ in 0..shots {
        run_seed=run_seed.wrapping_add(0x9E3779B97F4A7C15);
        let mut machine=Machine::new(program.qubits,program.bits,run_seed);
        let mut pc=0;
        while pc<program.instructions.len() {
            steps+=1;
            if steps>MAX_EXECUTED_STEPS{return Err("local simulation step limit exceeded (possible unbounded runtime feedback)".into());}
            let ins=program.instructions[pc];
            let q=[ins.qubits[0].0 as usize,ins.qubits[1].0 as usize,ins.qubits[2].0 as usize];
            match ins.opcode {
                OpCode::Gate(g)=>{
                    let beg=ins.offset as usize;
                    let end=beg.checked_add(ins.count as usize).ok_or("angle offset overflow")?;
                    let params=program.angles.get(beg..end).ok_or("angle pool out of bounds")?;
                    let spec=crate::sema::gate_spec(g);
                    if params.len()!=spec.parameters{return Err("gate parameter mismatch".into());}
                    for &idx in &q[..spec.qubits]{if idx>=program.qubits{return Err("qubit ID out of bounds".into());}}
                    gate(&mut machine,g,q,params)?;
                },
                OpCode::Measure|OpCode::MeasureInto=>{
                    if q[0]>=program.qubits || ins.bit.0 as usize>=program.bits {return Err("measurement ID out of bounds".into());}
                    let result=machine.measure(q[0]);machine.bits[ins.bit.0 as usize]=result;
                },
                OpCode::Reset=>{
                    if q[0]>=program.qubits{return Err("reset qubit out of bounds".into());}
                    if machine.measure(q[0]){gate(&mut machine,GateId::X,q,&[])?;}
                },
                OpCode::Barrier=>(), //no state-vector effect
                OpCode::IfBit|OpCode::WhileBit=>{
                    let bit=machine.bits.get(ins.bit.0 as usize).ok_or("branch bit out of bounds")?;
                    if *bit != (ins.count!=0) {pc=control[pc];continue;}
                },
                OpCode::Else|OpCode::EndWhile=>{pc=control[pc];continue;},
                OpCode::EndIf=>(),
            }
            pc+=1;
        }
        *histogram.entry(bitstring(&machine.bits)).or_insert(0)+=1;
    }
    Ok(Counts{histogram,shots})
}

#[cfg(test)]
mod tests {
    use super::*;
    fn simulate_source(src:&str,shots:usize)->Counts {
        let p=crate::compile(src).unwrap();simulate(&p,shots,19).unwrap()
    }
    #[test] fn basic_x_measurement_is_deterministic(){
        assert_eq!(simulate_source("let q=qubit();x(q);let b=measure(q);",16).histogram.get("1"),Some(&16));
    }
    #[test] fn bell_pair_always_correlated(){
        let got=simulate_source(include_str!("../examples/bell.qr"),256);
        assert_eq!(got.histogram.values().sum::<u64>(),256);
        assert!(got.histogram.keys().all(|key| key=="00"||key=="11"));
        assert_eq!(got.histogram.len(),2);
    }
    #[test] fn hadamard_is_reproducible(){
        let p=crate::compile("let q=qubit();h(q);let b=measure(q);").unwrap();
        assert_eq!(simulate(&p,200,123).unwrap(),simulate(&p,200,123).unwrap());
    }
    #[test] fn reset_erases_one(){
        let got=simulate_source("let q=qubit();x(q);reset(q);let b=measure(q);",32);
        assert_eq!(got.histogram.get("0"),Some(&32));
    }
    #[test] fn both_qcu_and_qr_execute_identically(){
        let p=crate::compile(include_str!("../examples/bell.qr")).unwrap();
        let qcu=crate::qcu::encode(&p).unwrap();
        let decoded=crate::qcu::decode(&qcu).unwrap();
        assert_eq!(simulate(&p,128,99).unwrap(),simulate(&decoded,128,99).unwrap());
    }
    #[test] fn feedback_if_uses_measured_bit(){
        let got=simulate_source("let q=qubit();x(q);let b=measure_keep(q);if b {x(q);}let c=measure(q);",10);
        assert_eq!(got.histogram.get("01"),Some(&10));
    }
    #[test] fn feedback_while_terminates(){
        let got=simulate_source("let q=qubit();x(q);let mut b=measure_keep(q);while b {x(q);measure_into(b,q);}",10);
        assert_eq!(got.histogram.get("0"),Some(&10));
    }
    #[test] fn rejects_large_quantum_register(){
        let mut p=Program::with_capacity(0);p.qubits=MAX_QUBITS+1;
        assert!(simulate(&p,1,1).unwrap_err().contains("at most"));
    }
    #[test] fn rejects_invalid_shot_counts(){
        let p=Program::with_capacity(0);
        assert!(simulate(&p,0,1).is_err());
        assert!(simulate(&p,MAX_SHOTS+1,1).is_err());
    }
    #[test] fn zero_qubit_program_can_run(){
        let got=simulate_source("let a: i64 = 3+4;",1);
        assert_eq!(got.histogram.get("(no classical bits)"),Some(&1));
    }
    #[test] fn legacy_cx_is_not_silently_misinterpreted(){
        let p=crate::compile("let a=qubit();let b=qubit();CX(a,b);").unwrap();
        assert!(simulate(&p,1,1).unwrap_err().contains("legacy"));
    }
    #[test] fn h_twice_returns_zero(){
        let got=simulate_source("let q=qubit();h(q);h(q);let b=measure(q);",200);
        assert_eq!(got.histogram.get("0"),Some(&200));
    }
    #[test] fn controlled_x_fires_only_for_one(){
        let got=simulate_source("let a=qubit();let b=qubit();x(a);cx(a,b);let c=measure(a);let d=measure(b);",24);
        assert_eq!(got.histogram.get("11"),Some(&24));
    }
    #[test] fn z_after_h_does_not_change_measurement_distribution(){
        let got=simulate_source("let q=qubit();h(q);z(q);h(q);let b=measure(q);",24);
        assert_eq!(got.histogram.get("1"),Some(&24));
    }
    #[test] fn x_after_ry_pi_is_deterministic(){
        let got=simulate_source("let q=qubit();ry(pi,q);x(q);let b=measure(q);",24);
        assert_eq!(got.histogram.get("0"),Some(&24));
    }
    #[test] fn qcu_corruption_is_detected_before_execution(){
        let program=crate::compile("let q=qubit();x(q);").unwrap();
        let mut blob=crate::qcu::encode(&program).unwrap();
        let last=blob.len()-1;blob[last]^=1;
        assert!(crate::qcu::decode(&blob).is_err());
    }

}
