use anyhow::{Result, anyhow};

use std::collections::HashMap;

use crate::Latency;
use crate::parse_input as ast;

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
    fn translate_term(
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
                let child_ids = children
                    .iter()
                    .map(|child| Self::translate_term(nodes, labels, child))
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

    pub fn from_program(program: &[ast::ProgramLine]) -> Result<Self> {
        let mut nodes = Vec::new();
        let mut labels = HashMap::new();
        let mut last_line = None;
        for line in program {
            if labels.contains_key(line.label) {
                return Err(anyhow!("label is already defined: {}", line.label));
            }
            let rhs = Self::translate_term(&mut nodes, &labels, &line.def)?;
            last_line = Some(rhs);
            labels.insert(line.label.to_owned(), rhs);
        }
        Ok(Dag {
            nodes,
            roots: last_line.into_iter().collect(),
        })
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

type Arity = u32;

struct Program {
    operations: HashMap<String, Arity>,
    labels: HashMap<String, DagNode>,
}

struct Machine<'a> {
    definitions: HashMap<String, (Vec<String>, Latency, ast::Term<'a>)>,
}
