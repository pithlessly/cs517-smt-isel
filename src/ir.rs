use anyhow::{Result, anyhow};

use std::collections::HashMap;

use crate::parse_input as ast;
use crate::{Arity, Latency};

pub type DagNodeId = u32;

pub struct Dag {
    nodes: Vec<DagNode>,
    roots: Vec<DagNodeId>,
}

impl std::fmt::Debug for Dag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Dag")
            .field(
                "nodes",
                &std::fmt::from_fn(|f| {
                    f.debug_map()
                        .entries(self.nodes.iter().enumerate())
                        .finish()
                }),
            )
            .field("roots", &self.roots)
            .finish()
    }
}

impl Dag {
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
}

type ArityMap = HashMap<String, Arity>;

fn record_arity(arities: &mut ArityMap, label: &str, arity: Arity) -> Result<()> {
    if let Some(&existing_arity) = arities.get(label) {
        if arity != existing_arity {
            Err(anyhow!(
                "arity mismatch in program: {label}/{existing_arity} vs. {label}/{arity}"
            ))
        } else {
            Ok(())
        }
    } else {
        arities.insert(label.to_owned(), arity);
        Ok(())
    }
}

impl Dag {
    fn translate_term(
        arities: &mut ArityMap,
        nodes: &mut Vec<DagNode>,
        labels: &HashMap<String, DagNodeId>,
        tm: &ast::Term,
    ) -> Result<DagNodeId> {
        let label = tm.label;
        match &tm.children {
            None => labels
                .get(label)
                .copied()
                .ok_or_else(|| anyhow!("unknown variable: {label}")),
            Some(children) => {
                record_arity(arities, label, tm.arity())?;
                let child_ids = children
                    .iter()
                    .map(|child| Self::translate_term(arities, nodes, labels, child))
                    .collect::<Result<_>>()?;
                let id = u32::try_from(nodes.len()).unwrap();
                nodes.push(DagNode {
                    label: label.to_owned(),
                    children: child_ids,
                });
                Ok(id)
            }
        }
    }

    fn from_ast_program(program: &[ast::ProgramLine]) -> Result<(Self, ArityMap)> {
        let mut arities = ArityMap::new();
        let mut nodes = Vec::new();
        let mut labels = HashMap::new();
        let mut last_line = None;
        for line in program {
            if labels.contains_key(line.label) {
                return Err(anyhow!("label is already defined: {}", line.label));
            }
            let rhs = Self::translate_term(&mut arities, &mut nodes, &labels, &line.def)?;
            last_line = Some(rhs);
            labels.insert(line.label.to_owned(), rhs);
        }
        let dag = Dag {
            nodes,
            roots: last_line.into_iter().collect(),
        };
        Ok((dag, arities))
    }
}

struct DagNode {
    label: String,
    children: Vec<DagNodeId>,
}

impl std::fmt::Debug for DagNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut t = f.debug_tuple(&self.label);
        for child in &self.children {
            t.field(child);
        }
        t.finish()
    }
}

pub type MachineInsnId = u32;

#[derive(Debug)]
pub struct Machine<'a> {
    pub definition_names: HashMap<&'a str, MachineInsnId>,
    pub definitions: Vec<MachineInsnDef<'a>>,
}

#[derive(Debug)]
pub struct MachineInsnDef<'a> {
    pub name: &'a str,
    pub arity: Arity,
    pub latency: Latency,
    pub def: MachineTerm<'a>,
}

#[derive(Debug)]
pub enum MachineTerm<'a> {
    Param(usize),
    Op(&'a str, Vec<MachineTerm<'a>>),
}

impl<'src> MachineTerm<'src> {
    fn from_ast_term(
        term: &ast::Term<'src>,
        params: &[&'src str],
        arity_map: &HashMap<String, Arity>,
    ) -> Result<MachineTerm<'src>> {
        let label = term.label;
        if let Some(children) = &term.children {
            let actual_arity = children.len();
            let &expected_arity = arity_map.get(label).ok_or_else(|| {
                anyhow!("machine insn refers to undefined IR insn: {label}/{actual_arity}")
            })?;
            if expected_arity as usize != actual_arity {
                return Err(anyhow!(
                    "machine insn invokes {label}/{expected_arity} with {actual_arity} parameter{}",
                    if actual_arity == 1 { "" } else { "s" }
                ));
            }
            let terms = children
                .iter()
                .map(|c| Self::from_ast_term(c, params, arity_map))
                .collect::<Result<Vec<_>>>()?;
            Ok(Self::Op(term.label, terms))
        } else {
            let idx = params
                .iter()
                .position(|&s| s == term.label)
                .ok_or_else(|| anyhow!("machine insn refers to undefined variable: {label}"))?;
            Ok(Self::Param(idx))
        }
    }
}

impl<'src> Machine<'src> {
    fn from_ast_program(
        machine: &[ast::MachineDefLine<'src>],
        ir_ops: &HashMap<String, Arity>,
    ) -> Result<Self> {
        let mut definition_names = HashMap::new();
        let mut definitions = Vec::new();

        for (i, line) in machine.iter().enumerate() {
            if definition_names.insert(line.name, i as u32).is_some() {
                return Err(anyhow!("duplicate machine insn definition: {}", line.name));
            }

            let insn = MachineInsnDef {
                name: line.name,
                arity: line.args.len() as Arity,
                latency: line.latency,
                def: MachineTerm::from_ast_term(&line.def, &line.args, ir_ops)?,
            };

            definitions.push(insn);
        }

        Ok(Self {
            definition_names,
            definitions,
        })
    }
}

#[derive(Debug)]
pub struct Ir<'a> {
    pub ir_operations: HashMap<String, Arity>,
    pub program: Dag,
    pub machine: Machine<'a>,
}

impl<'src> Ir<'src> {
    pub fn from_ast(ast: &ast::Ast<'src>) -> Result<Self> {
        let (program, ir_operations) = Dag::from_ast_program(&ast.program)?;
        let machine = Machine::from_ast_program(&ast.machine, &ir_operations)?;
        Ok(Self {
            ir_operations,
            program,
            machine,
        })
    }
}
