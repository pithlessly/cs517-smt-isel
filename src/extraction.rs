use crate::ir::{self, DagNode, Ir};
use crate::reduction::{OutputSlot, Variables, dt};
use crate::sorts::SolverSorts;

pub type SolvedIrNodeId = ir::DagNodeId;
pub type SolvedMachineNodeId = ir::DagNodeId;
pub type SolvedMachineProgram = ir::Dag;

fn extract_machine_node_id(
    machine_node_id: &dt::MachineNodeId,
    model: &z3::Model,
) -> SolvedMachineNodeId {
    // .expect("accessor should return a BV")
    // .as_u64()
    // .expect("accessor should return a BV that is a literal u64 value")
    // .try_into()
    // .expect("accessor should return a literal BV value that fits in a u32")

    let Some(machine_node_id) = model.get_const_interp(machine_node_id) else {
        return 0; // FIXME
        // panic!("model did not provide a value for {machine_node_id}")
    };

    machine_node_id
        .as_u64()
        .expect("MachineNodeId should be a literal u64 value")
        .try_into()
        .expect("accessor should return a literal u64 value that fits in a u32")
}

fn extract_machine_insn(
    instr: &dt::MachineNode,
    ir: &Ir,
    sorts: &SolverSorts,
    model: &z3::Model,
) -> DagNode {
    let Some(instr) = model.get_const_interp(instr) else {
        panic!("model did not provide a value for {instr}")
    };

    // NOTE "model_completion"
    // =======================
    // The docs say:
    // > When `model_completion` is true, `model.eval()` will assign an interpretation
    // > for constants and functions that do not have an interpretation in the model.
    // This either means that totally unconstrained variables get arbitrary values, or that
    // non-model-related constants like `variant.tester` are assigned the values they should have.
    // Either way, we want it enabled.
    let model_completion = true;
    let (i, variant) = sorts
        .machine_node
        .variants
        .iter()
        .enumerate()
        .find(|&(_, variant)| {
            model
                .eval(&variant.tester.apply(&[&instr]), model_completion)
                .expect("tester can be applied to a MachineNode")
                .as_bool()
                .expect("tester should return a Bool")
                .as_bool()
                .expect("tester should return a literal Bool value")
        })
        .expect("can't figure out which variant this MachineNode is");

    let children = variant
        .accessors
        .iter()
        .map(|accessor| {
            model
                .eval(&accessor.apply(&[&instr]), model_completion)
                .expect("accessor can be applied to a MachineNode")
                .as_bv()
                .expect("accessor should return a BV")
                .as_u64()
                .expect("accessor should return a BV that is a literal u64 value")
                .try_into()
                .expect("accessor should return a literal BV value that fits in a u32")
        })
        .collect();

    DagNode {
        label: ir.machine.definitions[i].name.to_owned(),
        children,
    }
}

fn extract_ir_node_id(
    ir_node_id: &dt::IrNodeId,
    ir: &Ir,
    sorts: &SolverSorts,
    model: &z3::Model,
) -> SolvedIrNodeId {
    let Some(modeled_ir_node) = model.get_const_interp(ir_node_id) else {
        return 0; // FIXME
        // panic!("model did not provide a value for {ir_node_id}")
    };

    let model_completion = true; // See NOTE "model_completion"
    let i = sorts
        .ir_node_id
        .variants
        .iter()
        .position(|variant| {
            model
                .eval(&variant.tester.apply(&[&modeled_ir_node]), model_completion)
                .expect("tester can be applied to an IrNodeId")
                .as_bool()
                .expect("tester should return a Bool")
                .as_bool()
                .expect("tester should return a literal Bool value")
        })
        .expect("can't figure out which variant this MachineNode is");

    assert!(i < ir.program.len());
    i as SolvedIrNodeId
}

fn extract_output_slot(
    slot: &OutputSlot,
    ir: &Ir,
    sorts: &SolverSorts,
    model: &z3::Model,
) -> (DagNode, SolvedIrNodeId) {
    let instr = extract_machine_insn(&slot.instr, ir, sorts, model);
    let modeled_ir_node = extract_ir_node_id(&slot.model, ir, sorts, model);
    (instr, modeled_ir_node)
}

impl Variables {
    pub fn extract(&self, ir: &Ir, sorts: &SolverSorts, model: &z3::Model) -> SolvedMachineProgram {
        let (solved_machine_insns, corresponding_ir_nodes): (Vec<DagNode>, Vec<SolvedIrNodeId>) =
            self.output_program
                .iter()
                .map(|slot| extract_output_slot(slot, ir, sorts, model))
                .collect();
        let solved_root_witnesses: Vec<SolvedMachineNodeId> = self
            .root_witnesses
            .iter()
            .map(|root| extract_machine_node_id(root, model))
            .collect();
        for (&root_witness, &root) in solved_root_witnesses.iter().zip(&ir.program.roots) {
            // FIXME
            // assert_eq!(corresponding_ir_nodes[root_witness as usize], root);
        }
        ir::Dag {
            nodes: solved_machine_insns,
            roots: solved_root_witnesses,
        }
    }
}
