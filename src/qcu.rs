//QRust QCU interchange v1
use crate::ids::{BitId, QubitId};
use crate::ir::{Instruction, OpCode, Program};
use crate::sema::{self, GateId};

pub const MAGIC: &[u8; 8] = b"QRQCU001";
const HEADER: usize = 36;
const RECORD: usize = 28;
const VERSION: u16 = 1;
const MAX_INSTRUCTIONS: usize = 1_000_000;

fn put_u16(out: &mut Vec<u8>, value: u16) { out.extend_from_slice(&value.to_le_bytes()); }
fn put_u32(out: &mut Vec<u8>, value: u32) { out.extend_from_slice(&value.to_le_bytes()); }
fn as_u32(value: usize, description: &str) -> Result<u32, String> {
    u32::try_from(value).map_err(|_| format!("QCU {description} exceeds u32"))
}
fn u16_at(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().expect("checked header"))
}
fn u32_at(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().expect("checked packet"))
}
fn fnv32(bytes: &[u8]) -> u32 {
    let mut hash = 0x811c9dc5u32;
    for byte in bytes { hash = (hash ^ u32::from(*byte)).wrapping_mul(0x01000193); }
    hash
}

fn opcode_parts(opcode: OpCode) -> (u8, u8, u8) {
    match opcode {
        OpCode::Gate(id) => (0, id as u8, 0),
        OpCode::Measure => (1, 0, 0),
        OpCode::MeasureInto => (2, 0, 0),
        OpCode::Reset => (3, 0, 0),
        OpCode::Barrier => (4, 0, 0),
        OpCode::IfBit => (5, 0, 0),
        OpCode::Else => (6, 0, 0),
        OpCode::EndIf => (7, 0, 0),
        OpCode::WhileBit => (8, 0, 0),
        OpCode::EndWhile => (9, 0, 0),
    }
}

pub fn encode(program: &Program) -> Result<Vec<u8>, String> {
    let inst_count = program.instructions.len();
    let angle_count = program.angles.len();
    let barrier_count = program.barrier_qubits.len();
    if inst_count > MAX_INSTRUCTIONS { return Err("QCU instruction count exceeds safety limit".into()); }
    let capacity = HEADER
        .checked_add(inst_count.checked_mul(RECORD).ok_or("QCU size overflow")?)
        .and_then(|x| x.checked_add(angle_count.checked_mul(8)?))
        .and_then(|x| x.checked_add(barrier_count.checked_mul(4)?))
        .ok_or("QCU payload size overflow")?;
    let mut out = Vec::with_capacity(capacity);
    out.extend_from_slice(MAGIC);
    put_u16(&mut out, VERSION);
    put_u16(&mut out, 0); //no flags defined in v1
    put_u32(&mut out, as_u32(program.qubits, "qubit count")?);
    put_u32(&mut out, as_u32(program.bits, "bit count")?);
    put_u32(&mut out, as_u32(inst_count, "instruction count")?);
    put_u32(&mut out, as_u32(angle_count, "angle count")?);
    put_u32(&mut out, as_u32(barrier_count, "barrier count")?);
    put_u32(&mut out, 0); //filled with checksum after writing payload
    for instr in &program.instructions {
        let (tag, gate, _) = opcode_parts(instr.opcode);
        let condition = match instr.opcode {
            OpCode::IfBit | OpCode::WhileBit => u8::try_from(instr.count)
                .map_err(|_| "invalid runtime condition".to_string())?,
            _ => 0,
        };
        out.extend_from_slice(&[tag, gate, condition, 0]);
        for id in instr.qubits { put_u32(&mut out, id.0); }
        put_u32(&mut out, instr.bit.0);
        put_u32(&mut out, instr.offset);
        put_u32(&mut out, if matches!(instr.opcode, OpCode::IfBit | OpCode::WhileBit) {
            0
        } else { instr.count });
    }
    for angle in &program.angles { out.extend_from_slice(&angle.to_bits().to_le_bytes()); }
    for id in &program.barrier_qubits { put_u32(&mut out, id.0); }
    let checksum = fnv32(&out[HEADER..]);
    out[32..36].copy_from_slice(&checksum.to_le_bytes());
    decode(&out)?;
    Ok(out)
}

#[derive(Clone, Copy)]
enum ControlFrame { If(bool), While }

//Decode and validate all IDs, pool bounds, gates, branch nesting and bytes Never execute instructions
//originating from the wire without this step
pub fn decode(bytes: &[u8]) -> Result<Program, String> {
    if bytes.len() < HEADER { return Err("truncated QCU header".into()); }
    if &bytes[..8] != MAGIC { return Err("unrecognized QCU magic".into()); }
    if u16_at(bytes, 8) != VERSION { return Err("unsupported QCU format version".into()); }
    if u16_at(bytes, 10) != 0 { return Err("unsupported QCU feature flags".into()); }
    let qubits = u32_at(bytes, 12) as usize;
    let bits = u32_at(bytes, 16) as usize;
    let inst_count = u32_at(bytes, 20) as usize;
    let angle_count = u32_at(bytes, 24) as usize;
    let barrier_count = u32_at(bytes, 28) as usize;
    if inst_count > MAX_INSTRUCTIONS { return Err("QCU instruction count exceeds safety limit".into()); }
    let expected = HEADER.checked_add(inst_count.checked_mul(RECORD)
            .ok_or("QCU instruction section overflow")?)
        .and_then(|x| x.checked_add(angle_count.checked_mul(8)?))
        .and_then(|x| x.checked_add(barrier_count.checked_mul(4)?))
        .ok_or("QCU packet size overflow")?;
    if bytes.len() != expected { return Err("QCU payload length mismatch".into()); }
    if fnv32(&bytes[HEADER..]) != u32_at(bytes, 32) {
        return Err("QCU payload checksum mismatch".into());
    }
    let mut program = Program::with_capacity(inst_count);
    program.qubits = qubits;
    program.bits = bits;
    let angles_start = HEADER + inst_count * RECORD;
    let barriers_start = angles_start + angle_count * 8;
    for index in 0..angle_count {
        let at = angles_start + index * 8;
        let raw = u64::from_le_bytes(bytes[at..at + 8].try_into().expect("checked QCU packet"));
        let value = f64::from_bits(raw);
        if !value.is_finite() { return Err(format!("QCU non-finite angle at {index}")); }
        program.angles.push(value);
    }
    for index in 0..barrier_count {
        let id = QubitId(u32_at(bytes, barriers_start + index * 4));
        if id.0 as usize >= qubits { return Err("QCU barrier qubit out of range".into()); }
        program.barrier_qubits.push(id);
    }
    let mut control = Vec::new();
    for index in 0..inst_count {
        let at = HEADER + index * RECORD;
        let tag = bytes[at];
        let raw_gate = bytes[at + 1];
        let condition = bytes[at + 2];
        if bytes[at + 3] != 0 { return Err("QCU nonzero reserved instruction bits".into()); }
        let operands = [QubitId(u32_at(bytes, at + 4)), QubitId(u32_at(bytes, at + 8)),
            QubitId(u32_at(bytes, at + 12))];
        let bit = BitId(u32_at(bytes, at + 16));
        let offset = u32_at(bytes, at + 20);
        let count = u32_at(bytes, at + 24);
        if tag != 0 && raw_gate != 0 { return Err("QCU stray gate ID".into()); }
        if !matches!(tag, 5 | 8) && condition != 0 { return Err("QCU stray branch condition".into()); }
        let opcode = match tag {
            0 => {
                let gate: GateId = sema::gate_id_from_raw(raw_gate)
                    .ok_or_else(|| format!("QCU unknown gate ID {raw_gate}"))?;
                OpCode::Gate(gate)
            }
            1 => OpCode::Measure,
            2 => OpCode::MeasureInto,
            3 => OpCode::Reset,
            4 => OpCode::Barrier,
            5 => OpCode::IfBit,
            6 => OpCode::Else,
            7 => OpCode::EndIf,
            8 => OpCode::WhileBit,
            9 => OpCode::EndWhile,
            _ => return Err(format!("QCU unknown operation {tag}")),
        };
        match opcode {
            OpCode::Gate(id) => {
                let spec = sema::gate_spec(id);
                if count as usize != spec.parameters { return Err("QCU gate angle arity mismatch".into()); }
                if (offset as usize).checked_add(count as usize).is_none_or(|n| n > angle_count) {
                    return Err("QCU angle pool offset out of bounds".into());
                }
                for (i, q) in operands.iter().enumerate() {
                    if i < spec.qubits && q.0 as usize >= qubits { return Err("QCU gate qubit out of range".into()); }
                    if i >= spec.qubits && q.0 != 0 { return Err("QCU unused qubit operand not zero".into()); }
                }
                for i in 0..spec.qubits {
                    for j in 0..i { if operands[i] == operands[j] { return Err("QCU aliased gate operands".into()); } }
                }
                if bit.0 != 0 { return Err("QCU gate carries unexpected classical bit".into()); }
            }
            OpCode::Barrier => {
                if (offset as usize).checked_add(count as usize).is_none_or(|n| n > barrier_count) {
                    return Err("QCU barrier pool offset out of bounds".into());
                }
            }
            _ => {
                if offset != 0 || count != 0 { return Err("QCU unexpected operand pool offset".into()); }
                match opcode {
                    OpCode::Measure | OpCode::MeasureInto => {
                        if operands[0].0 as usize >= qubits || bit.0 as usize >= bits {
                            return Err("QCU measurement operand out of range".into());
                        }
                    }
                    OpCode::Reset => {
                        if operands[0].0 as usize >= qubits { return Err("QCU reset operand out of range".into()); }
                    }
                    OpCode::IfBit | OpCode::WhileBit => {
                        if bit.0 as usize >= bits || condition > 1 {
                            return Err("QCU branch condition invalid".into());
                        }
                    }
                    _ => (),
                }
            }
        }
        if !matches!(opcode, OpCode::Gate(_) | OpCode::Measure | OpCode::MeasureInto | OpCode::Reset)
            && operands.iter().any(|q| q.0 != 0) {
            return Err("QCU unexpected qubit operands".into());
        }
        if !matches!(opcode, OpCode::IfBit | OpCode::WhileBit |
                OpCode::Measure | OpCode::MeasureInto) && bit.0 != 0 {
            return Err("QCU unexpected bit operand".into());
        }
        if matches!(opcode, OpCode::Measure | OpCode::MeasureInto | OpCode::Reset)
            && (operands[1].0 != 0 || operands[2].0 != 0) {
            return Err("QCU unexpected extra qubit".into());
        }
        match opcode {
            OpCode::IfBit => control.push(ControlFrame::If(false)),
            OpCode::WhileBit => control.push(ControlFrame::While),
            OpCode::Else => match control.last_mut() {
                Some(ControlFrame::If(seen)) if !*seen => *seen = true,
                _ => return Err("QCU else without matching if".into()),
            },
            OpCode::EndIf => match control.pop() {
                Some(ControlFrame::If(_)) => (),
                _ => return Err("QCU endif without matching if".into()),
            },
            OpCode::EndWhile => match control.pop() {
                Some(ControlFrame::While) => (),
                _ => return Err("QCU endwhile without matching while".into()),
            },
            _ => (),
        }
        program.instructions.push(Instruction {
            opcode, qubits: operands, bit, offset,
            count: if matches!(opcode, OpCode::IfBit | OpCode::WhileBit) {
                u32::from(condition)
            } else { count },
        });
    }
    if !control.is_empty() { return Err("QCU unterminated runtime control block".into()); }
    Ok(program)
}

pub fn describe(program: &Program) -> String {
    let mut description = format!("QCU logical packet v{VERSION}: {} qubits, {} bits, {} instructions, {} angles, {} barrier operands\n",
        program.qubits, program.bits, program.instructions.len(), program.angles.len(), program.barrier_qubits.len());
    for (i, op) in program.instructions.iter().enumerate().take(20) {
        let name = match op.opcode {
            OpCode::Gate(gate) => sema::gate_spec(gate).name,
            OpCode::Measure => "measure", OpCode::MeasureInto => "measure_into",
            OpCode::Reset => "reset", OpCode::Barrier => "barrier",
            OpCode::IfBit => "if_bit", OpCode::Else => "else",
            OpCode::EndIf => "endif", OpCode::WhileBit => "while_bit",
            OpCode::EndWhile => "endwhile",
        };
        description.push_str(&format!("  {i:>5}: {name} q[{}] q[{}] q[{}] bit={} pool={} count={}\n",
            op.qubits[0].0, op.qubits[1].0, op.qubits[2].0,
            op.bit.0, op.offset, op.count));
    }
    if program.instructions.len() > 20 { description.push_str("  ... (first 20 instructions shown)\n"); }
    description
}

#[cfg(test)]
mod tests {
    use super::*;
    fn roundtrip(source: &str) -> Program {
        let original = crate::compile(source).unwrap();
        let bytes = encode(&original).unwrap();
        let restored = decode(&bytes).unwrap();
        assert_eq!(sema::emit_qasm(&original), sema::emit_qasm(&restored));
        assert_eq!(bytes, encode(&restored).unwrap());
        restored
    }
    #[test]
    fn bell_roundtrip_preserves_measurement() {
        let p = roundtrip("let a=qubit();let b=qubit();h(a);cx(a,b);let x=measure(a);let y=measure(b);");
        assert_eq!(p.instructions.len(), 4);
        assert_eq!(p.bits, 2);
    }
    #[test]
    fn every_gate_id_roundtrips() {
        let mut src = String::from("let a=qubit();let b=qubit();let c=qubit();");
        for gate in sema::STANDARD_GATES.iter().chain(sema::EXTENDED_GATES.iter()) {
            let mut args = vec!["0.125"; gate.parameters];
            args.extend_from_slice(&["a", "b", "c"][..gate.qubits]);
            src.push_str(&format!("{}({});", gate.name, args.join(",")));
        }
        roundtrip(&src);
    }
    #[test]
    fn runtime_if_and_while_roundtrip() {
        roundtrip("let q=qubit();let mut b=measure_keep(q);while b{reset(q);h(q);measure_into(b,q);}x(q);");
        roundtrip("fn main(){let q=qubit();let b=measure_keep(q);if b{x(q);}else{z(q);}}");
    }
    #[test]
    fn index_angles_preserve_negative_zero_and_bits() {
        let original = crate::compile("let q=qubit(); for i in 0..16{rz(i*pi/32,q);} rx(-0.0,q);").unwrap();
        let back = decode(&encode(&original).unwrap()).unwrap();
        assert_eq!(original.angles.iter().map(|x|x.to_bits()).collect::<Vec<_>>(),
                   back.angles.iter().map(|x|x.to_bits()).collect::<Vec<_>>());
    }
    #[test]
    fn truncated_and_corrupt_packets_rejected() {
        let p = crate::compile("let q=qubit();h(q);").unwrap();
        let bytes = encode(&p).unwrap();
        for n in [0, 5, 35, 36, bytes.len()-1] { assert!(decode(&bytes[..n]).is_err()); }
        let mut corrupt = bytes.clone();
        corrupt[HEADER] ^= 0xff;
        assert!(decode(&corrupt).unwrap_err().contains("checksum"));
        let mut version = bytes.clone(); version[8] = 7;
        assert!(decode(&version).unwrap_err().contains("version"));
    }
    #[test]
    fn forged_out_of_bounds_qubit_and_opcode_rejected() {
        let p = crate::compile("let q=qubit();h(q);").unwrap();
        let mut bytes = encode(&p).unwrap();
        bytes[HEADER + 4..HEADER + 8].copy_from_slice(&13u32.to_le_bytes());
        let checksum = fnv32(&bytes[HEADER..]);
        bytes[32..36].copy_from_slice(&checksum.to_le_bytes());
        assert!(decode(&bytes).unwrap_err().contains("qubit out of range"));
        bytes[HEADER] = 250;
        bytes[HEADER + 1] = 0;
        let checksum = fnv32(&bytes[HEADER..]);
        bytes[32..36].copy_from_slice(&checksum.to_le_bytes());
        assert!(decode(&bytes).unwrap_err().contains("unknown operation"));
    }
    #[test]
    fn format_header_is_stable_and_little_endian() {
        let p = crate::compile("let q=qubit();h(q);").unwrap();
        let bytes = encode(&p).unwrap();
        assert_eq!(&bytes[..8], MAGIC);
        assert_eq!(&bytes[8..12], &[1,0,0,0]);
        assert_eq!(u32_at(&bytes, 20), 1);
        assert_eq!(bytes.len(), HEADER + RECORD);
    }
}
