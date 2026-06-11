// correctness means:
// [✓] arity (implied by types)
// [✓] causality
// [ ] latency
// [✓] modeling
// [ ] roots

use std::collections::BTreeMap;
use std::collections::HashMap;

use z3::DatatypeSort;
use z3::ast::Ast;

use crate::ir::Dag;
use crate::ir::DagNodeId;
use crate::ir::Ir;
use crate::ir::MachineInsnDef;
use crate::ir::MachineTerm;
use crate::sorts;
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
    pub model_array: z3::ast::Array,
    pub output_program: Box<[OutputSlot]>,
    pub root_witnesses: Box<[dt::MachineNodeId]>, // ρ[i]
}

impl OutputSlot {
    pub fn new(sorts: &SolverSorts, model_array: &z3::ast::Array, idx: u32) -> Self {
        Self {
            instr: dt::MachineNode::new_const(format!("M_{idx}"), &sorts.machine_node.sort),
            model: model_array
                .select(&z3::ast::BV::from_u64(
                    idx as u64,
                    sorts.machine_node_id_bitcount,
                ))
                .as_datatype()
                .unwrap(),
        }
    }
}

impl Variables {
    pub fn new(ir: &Ir, machine_program_len: u32, sorts: &SolverSorts) -> Self {
        let model_array =
            z3::ast::Array::new_const("m", &sorts.machine_node_id, &sorts.ir_node_id.sort);
        let output_program = (0..machine_program_len)
            .map(|i| OutputSlot::new(&sorts, &model_array, i))
            .collect();
        let root_witnesses = (0..ir.program.roots.len())
            .map(|i| dt::MachineNodeId::new_const(format!("ρ_{i}"), sorts.machine_node_id_bitcount))
            .collect();

        Self {
            model_array,
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
                .map(|accessor| accessor.apply(&[scrutinee]).try_into().unwrap())
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

fn unify(term: &MachineInsnDef, node: DagNodeId, dag: &Dag) -> Option<Box<[DagNodeId]>> {
    let mut solved: BTreeMap<usize, DagNodeId> = BTreeMap::new();

    unify_inner(&term.def, node, dag, &mut solved)?;

    // all variables are in the range 0..n so if we have n of them the keys of the BTreeMap must be
    // exactly the set 0..n in order :3
    if solved.len() == term.arity as usize {
        Some(solved.values().copied().collect())
    } else {
        None
    }
}

fn unify_inner(
    term: &MachineTerm,
    node: DagNodeId,
    dag: &Dag,
    solved: &mut BTreeMap<usize, DagNodeId>,
) -> Option<()> {
    match *term {
        MachineTerm::Param(var) => {
            if let Some(&prev) = solved.get(&var) {
                (prev == node).then(|| ())
            } else {
                solved.insert(var, node);
                Some(())
            }
        }
        MachineTerm::Op(name, ref machine_terms) => {
            let cur = &dag.nodes[node as usize];

            if name != cur.label {
                return None;
            }

            if machine_terms.len() != cur.children.len() {
                return None;
            }

            for (subterm, &child) in machine_terms.iter().zip(&cur.children) {
                unify_inner(subterm, child, dag, solved)?;
            }

            Some(())
        }
    }
}

fn is_ir_node(dag_node: DagNodeId, ir_node: &dt::IrNodeId, sorts: &SolverSorts) -> z3::ast::Bool {
    sorts.ir_node_id.variants[dag_node as usize]
        .tester
        .apply(&[ir_node])
        .as_bool()
        .unwrap()
}

fn assert_modeling(ir: &Ir, sorts: &SolverSorts, variables: &Variables, solver: &z3::Solver) {
    let index: Box<[HashMap<DagNodeId, Box<[DagNodeId]>>]> = ir
        .machine
        .definitions
        .iter()
        .map(|def| {
            (0..ir.program.len() as u32)
                .filter_map(|node| unify(def, node, &ir.program).map(|u| (node, u)))
                .collect()
        })
        .collect();

    for slot in &variables.output_program {
        solver.assert(pattern_match_machine_node(
            &sorts,
            &slot.instr,
            |kind, args| {
                let candidate_insns = &index[kind];

                let disjuncts: Box<[_]> = candidate_insns
                    .iter()
                    .map(|(parent, children)| {
                        let correct_parent = is_ir_node(*parent, &slot.model, sorts);

                        let correct_children = children.iter().zip(args).map(|(child, arg)| {
                            is_ir_node(
                                *child,
                                &variables.model_array.select(arg).as_datatype().unwrap(),
                                sorts,
                            )
                        });

                        let mut conjucts: Vec<_> = correct_children.collect();
                        conjucts.push(correct_parent);

                        z3::ast::Bool::and(&conjucts)
                    })
                    .collect();

                z3::ast::Bool::or(&disjuncts)
            },
        ));
    }
}

fn assert_roots(ir: &Ir, sorts: &SolverSorts, variables: &Variables, solver: &z3::Solver) {
    for root in &ir.program.roots {
        let disjuncts: Box<[_]> = variables
            .output_program
            .iter()
            .map(|slot| is_ir_node(*root, &slot.model, sorts))
            .collect();
        solver.assert(z3::ast::Bool::or(&disjuncts));
    }
}

pub fn solve(ir: &Ir) -> Option<Dag> {
    for machine_program_len in 1..=ir.program.len() as u32 {
        eprintln!("trying w/ length {machine_program_len}");

        let sorts = sorts::SolverSorts::new(&ir, machine_program_len);
        // eprintln!("{:#?}", sorts);

        let variables = Variables::new(&ir, machine_program_len, &sorts);
        // eprintln!("{:#?}", variables);

        let solver = z3::Solver::new();

        assert_causality(&sorts, &variables, &solver);
        assert_modeling(ir, &sorts, &variables, &solver);
        assert_roots(ir, &sorts, &variables, &solver);

        // eprintln!("{:#?}", solver.get_assertions());

        match solver.check() {
            z3::SatResult::Unsat => continue,
            z3::SatResult::Unknown => return None,
            z3::SatResult::Sat => {
                let model = solver
                    .get_model()
                    .expect("unable to find a satisfying model!");

                return Some(variables.extract(ir, &sorts, &model));
            }
        }
    }

    return None;
}
