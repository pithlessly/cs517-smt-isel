// correctness means:
// [✓] arity (implied by types)
// [✓] causality
// [ ] latency
// [ ] modeling
// [ ] roots

use z3::ast::Ast;

use crate::ir::Ir;
use crate::sorts::SolverSorts;

pub mod dt {
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

#[derive(Debug)]
pub struct Variables {
    pub output_program: Box<[OutputSlot]>,
    pub root_witnesses: Box<[dt::MachineNodeId]>, // ρ[i]
}

impl OutputSlot {
    pub fn new(sorts: &SolverSorts, idx: u32) -> Self {
        Self {
            instr: dt::MachineNode::new_const(format!("M_{idx}"), &sorts.machine_node.sort),
            model: dt::IrNodeId::new_const(format!("m_{idx}"), &sorts.ir_node_id.sort),
        }
    }
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

/// Generate code that implements a match-expression that looks like:
/// ```
/// (match <scrutinee>
///   (OP0 r0 r1)    => <f(0, [r0, r1])>
///   (OP1)          => <f(1, [])>
///   (OP2 r0 r1 r2) => <f(1, [r0, r1, r2])>
///   ...)
/// ```
pub fn pattern_match_machine_node<R: Ast>(
    sorts: &SolverSorts,
    scrutinee: &dt::MachineNode,
    mut branch: impl FnMut(usize, &[dt::MachineNodeId]) -> R,
) -> R {
    // we implement this as a chain of if-statements
    sorts
        .machine_node
        .variants
        .iter()
        .enumerate()
        .fold(None, |remaining_cases: Option<R>, (idx, variant)| {
            // we need to implement the current branch:
            //   (OP[idx] ...) => <f(idx, [...])>

            // corresponds to [r1, r2, ...]
            let fields: Box<[dt::MachineNodeId]> = variant
                .accessors
                .iter()
                .map(|accessor| accessor.apply(&[scrutinee]).as_bv().unwrap())
                .collect();
            // corresponds to <f(idx, [r1, r2, ...])>
            let case_body: R = branch(idx, &fields);

            // guard the case body behind an 'if', unless there are no other possible cases
            Some(match remaining_cases {
                None => case_body,
                Some(remaining_cases) => {
                    // corresponds to (matches? <scrutinee> (OP[idx] ...))
                    let matches = variant.tester.apply(&[scrutinee]).as_bool().unwrap();
                    // corresponds to (if (matches? ...)
                    //                 then <f(idx, [...])>
                    //                 else <remaining_cases>)
                    matches.ite(&case_body, &remaining_cases)
                }
            })
        })
        .expect("need at least one case")
}

fn assert_causality(sorts: &SolverSorts, variables: &Variables, solver: &z3::Solver) {
    for (i, slot) in variables.output_program.iter().enumerate() {
        let i = dt::MachineNodeId::from_u64(i as _, sorts.machine_node_id_bitcount);
        solver.assert(pattern_match_machine_node(sorts, &slot.instr, |_, args| {
            let conjuncts: Box<[_]> = args.iter().map(|arg| arg.bvult(&i)).collect();
            z3::ast::Bool::and(&conjuncts)
        }));
    }
}

pub fn solve(ir: &Ir, machine_program_len: u32, sorts: &SolverSorts) {
    let variables = Variables::new(&ir, machine_program_len, &sorts);
    eprintln!("{:#?}", variables);

    let solver = z3::Solver::new();

    assert_causality(sorts, &variables, &solver);
    eprintln!("solver.check() returned: {:?}", solver.check());

    let model = solver
        .get_model()
        .expect("unable to find a satisfying model!");

    let output_program = variables.extract(ir, sorts, &model);
    eprintln!("{:#?}", output_program);
}
