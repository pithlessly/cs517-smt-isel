// correctness means:
// - arity (implied by types)
// - causality
// - latency
// - modeling
// - roots

use z3::ast::{BV, Datatype};

use crate::{ir::Ir, parse_input::Latency, sorts::SolverSorts};

#[derive(Debug)]
pub struct OutputSlot {
    pub instr: Datatype, // M (t_machine_node)
    pub model: Datatype, // m (t_ir_node_id)
}

impl OutputSlot {
    pub fn new(sorts: &SolverSorts, idx: u32) -> Self {
        Self {
            instr: Datatype::new_const(format!("M_{idx}"), &sorts.machine_node),
            model: Datatype::new_const(format!("m_{idx}"), &sorts.ir_node_id),
        }
    }
}

#[derive(Debug)]
pub struct Variables {
    pub output_program: Box<[OutputSlot]>,
    pub root_witnesses: Box<[BV]>,
}

impl Variables {
    pub fn new(ir: &Ir, machine_program_len: u32, sorts: &SolverSorts) -> Self {
        let output_program = (0..machine_program_len)
            .map(|i| OutputSlot::new(&sorts, i))
            .collect();
        let root_witnesses = (0..ir.program.roots.len())
            .map(|i| BV::new_const(format!("ρ_{i}"), sorts.machine_node_id_bitcount))
            .collect();

        Self {
            output_program,
            root_witnesses,
        }
    }
}
