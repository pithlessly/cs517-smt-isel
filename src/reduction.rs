// correctness means:
// - arity (implied by types)
// - causality
// - latency
// - modeling
// - roots

use crate::{ir::Ir, parse_input::Latency, sorts::SolverSorts};

mod dt {
    use z3::ast::{BV, Datatype};
    pub type IrNodeId = Datatype; // of sort `sorts.ir_node_id`
    pub type MachineNodeId = BV; // of sort `sorts.machine_node_id`
    pub type MachineNode = Datatype; // of sort `sorts.machine_node.sort`
}

#[derive(Debug)]
pub struct OutputSlot {
    pub instr: dt::MachineNode, // M[i]
    pub model: dt::IrNodeId,    // m[i]
}

impl OutputSlot {
    pub fn new(sorts: &SolverSorts, idx: u32) -> Self {
        Self {
            instr: dt::MachineNode::new_const(format!("M_{idx}"), &sorts.machine_node.sort),
            model: dt::IrNodeId::new_const(format!("m_{idx}"), &sorts.ir_node_id.sort),
        }
    }
}

#[derive(Debug)]
pub struct Variables {
    pub output_program: Box<[OutputSlot]>,
    pub root_witnesses: Box<[dt::MachineNodeId]>, // ρ[i]
}

impl Variables {
    pub fn new(ir: &Ir, machine_program_len: u32, sorts: &SolverSorts) -> Self {
        let output_program = (0..machine_program_len)
            .map(|i| OutputSlot::new(&sorts, i))
            .collect();
        let root_witnesses = (0..ir.program.roots.len())
            .map(|i| dt::MachineNodeId::new_const(format!("ρ_{i}"), sorts.machine_node_id_bitcount))
            .collect();

        Self {
            output_program,
            root_witnesses,
        }
    }
}
