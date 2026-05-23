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

#[derive(Debug)]
pub struct Ir {
    pub ir_operations: HashMap<String, Arity>,
    pub program: Dag,
}

impl Ir {
    pub fn from_ast(ast: &ast::Ast) -> Result<Self> {
        let (program, ir_operations) = Dag::from_ast_program(&ast.program)?;
        Ok(Self {
            ir_operations,
            program,
        })
    }
}

struct Machine<'a> {
    definitions: HashMap<String, (Vec<String>, Latency, ast::Term<'a>)>,
}
