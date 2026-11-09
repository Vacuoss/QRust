//Experimental *host-side* async planning IR, NOT a QPU scheduler
#![allow(dead_code)] //Preparatory IR is not wired into source lowering yet
use std::collections::HashSet;

pub const ASYNC_UNSUPPORTED: &str = "async/await execution is not supported yet; host future lowering and QPU job scheduling are planned (see async-ir-preview)";
pub const AWAIT_UNSUPPORTED: &str = ".await requires a host Future state machine and borrow analysis; QRust does not support suspension yet";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Domain { Host, QuantumKernel }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaptureKind {
    CopyScalar,
    OwnedQubit,
    MutableQubitBorrow,
    ClassicalBit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Capture { pub id: u32, pub kind: CaptureKind }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    ComputeHost,
    SubmitQuantum { job_id: u32 },
    AwaitQuantum { job_id: u32 },
    Complete,
}

#[derive(Clone, Debug)]
pub struct FuturePlan {
    pub domain: Domain,
    pub captures: Vec<Capture>,
    pub steps: Vec<Step>,
}

impl FuturePlan {
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.steps.is_empty() || !matches!(self.steps.last(), Some(Step::Complete)) {
            return Err("future plan must terminate with Complete");
        }
        let mut ids = HashSet::new();
        for capture in &self.captures {
            if !ids.insert(capture.id) { return Err("duplicate captured resource id"); }
        }
        let mut submitted = HashSet::new();
        for (index, step) in self.steps.iter().enumerate() {
            match step {
                Step::ComputeHost if self.domain == Domain::QuantumKernel =>
                    return Err("host computation cannot run inside a quantum kernel"),
                Step::SubmitQuantum { job_id } => {
                    if self.domain != Domain::Host {
                        return Err("QPU kernel cannot submit another quantum job");
                    }
                    if !submitted.insert(*job_id) {
                        return Err("duplicate outstanding quantum job id");
                    }
                }
                Step::AwaitQuantum { job_id } => {
                    if self.domain != Domain::Host {
                        return Err("QPU kernel cannot await a host future");
                    }
                    if self.captures.iter().any(|c| c.kind == CaptureKind::MutableQubitBorrow) {
                        return Err("mutable Qubit borrow cannot cross a suspension point");
                    }
                    if !submitted.remove(job_id) {
                        return Err("await has no matching outstanding submission");
                    }
                }
                Step::Complete if index + 1 != self.steps.len() =>
                    return Err("future plan has steps after completion"),
                _ => {}
            }
        }
        if !submitted.is_empty() { return Err("future completes with outstanding quantum jobs"); }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn host(steps: Vec<Step>, captures: Vec<Capture>) -> FuturePlan {
        FuturePlan { domain: Domain::Host, captures, steps }
    }
    #[test]
    fn host_future_can_submit_and_await_one_quantum_job() {
        host(vec![Step::ComputeHost, Step::SubmitQuantum {job_id: 4},
            Step::AwaitQuantum {job_id: 4}, Step::Complete],
            vec![Capture {id: 0, kind: CaptureKind::OwnedQubit}]).validate().unwrap();
    }
    #[test]
    fn mutable_qubit_borrow_cannot_cross_suspension() {
        let issue = host(vec![Step::SubmitQuantum {job_id: 1},
            Step::AwaitQuantum {job_id: 1}, Step::Complete],
            vec![Capture {id: 7, kind: CaptureKind::MutableQubitBorrow}]);
        assert!(issue.validate().unwrap_err().contains("borrow"));
    }
    #[test]
    fn quantum_kernel_cannot_become_a_host_executor() {
        let issue = FuturePlan { domain: Domain::QuantumKernel, captures: vec![],
            steps: vec![Step::AwaitQuantum {job_id: 0}, Step::Complete] };
        assert!(issue.validate().unwrap_err().contains("QPU"));
    }
    #[test]
    fn future_cannot_await_a_job_that_was_not_submitted() {
        let issue = host(vec![Step::AwaitQuantum {job_id: 4}, Step::Complete], vec![]);
        assert!(issue.validate().unwrap_err().contains("submission"));
    }
    #[test]
    fn future_cannot_duplicate_captured_resources() {
        let issue = host(vec![Step::Complete], vec![
            Capture {id: 0, kind: CaptureKind::OwnedQubit},
            Capture {id: 0, kind: CaptureKind::ClassicalBit}]);
        assert!(issue.validate().unwrap_err().contains("duplicate"));
    }
    #[test]
    fn future_must_complete_without_pending_jobs() {
        let issue = host(vec![Step::SubmitQuantum {job_id: 42}, Step::Complete], vec![]);
        assert!(issue.validate().unwrap_err().contains("outstanding"));
        assert!(host(vec![], vec![]).validate().is_err());
        assert!(host(vec![Step::Complete, Step::ComputeHost, Step::Complete], vec![]).validate().is_err());
    }
}
