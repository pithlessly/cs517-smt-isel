use crate::Ir;

#[derive(Debug)]
pub struct SolverSorts {
    pub ir_node_id: z3::Sort,
    pub machine_node_id: z3::Sort,
    pub machine_node_id_bitcount: u32,
    pub machine_node: z3::Sort,
}

impl SolverSorts {
    pub fn new(ir: &Ir, machine_program_len: u32) -> Self {
        let ir_node_id = ir_node_id(ir).sort;
        let (machine_node_id, machine_node_id_bitcount) = machine_node_id(machine_program_len);
        let machine_node = machine_node(&machine_node_id, ir).sort;

        Self {
            ir_node_id,
            machine_node_id,
            machine_node_id_bitcount,
            machine_node,
        }
    }
}

fn ir_node_id(ir: &Ir) -> z3::DatatypeSort {
    let mut builder = z3::DatatypeBuilder::new("IrNode");
    for i in 0..ir.program.len() {
        builder = builder.variant(&format!("ir{}", i), vec![]);
    }
    builder.finish()
}

// Since we compare machine indices using `<`, these need to be a bounded integer
// (bitvector in Z3 parlance) rather than an ADT.
fn machine_node_id(machine_program_len: u32) -> (z3::Sort, u32) {
    let num_bits = if machine_program_len > 1 {
        (machine_program_len - 1).ilog2() + 1
    } else {
        1 // I think zero-length bitvectors are not allowed
    };
    (z3::Sort::bitvector(num_bits), num_bits)
}

fn machine_node(t_machine_node_id: &z3::Sort, ir: &Ir) -> z3::DatatypeSort {
    let mut builder = z3::DatatypeBuilder::new("MachineNode");
    for definition in &ir.machine.definitions {
        use z3::DatatypeAccessor::Sort;
        let field_names: Vec<String> = (0..definition.arity).map(|n| n.to_string()).collect();
        let fields = field_names
            .iter()
            .map(|name| (&**name, Sort(t_machine_node_id.clone())))
            .collect();
        builder = builder.variant(definition.name, fields)
    }
    builder.finish()
}
