use crate::Ir;

fn ir_node(ir: &Ir) -> z3::DatatypeSort {
    let mut builder = z3::DatatypeBuilder::new("IrNode");
    for i in 0..ir.program.len() {
        builder = builder.variant(&format!("ir{}", i), vec![]);
    }
    builder.finish()
}

// Since we compare machine indices using `<`, these need to be a bounded integer
// (bitvector in Z3 parlance) rather than an ADT.
fn machine_node_id(machine_program_len: u32) -> z3::Sort {
    let num_bits = if machine_program_len > 1 {
        (machine_program_len - 1).ilog2() + 1
    } else {
        1 // I think zero-length bitvectors are not allowed
    };
    z3::Sort::bitvector(num_bits)
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

pub fn z3_main(ir: &Ir) {
    let t_ir_node = ir_node(ir);
    let t_machine_node_id = machine_node_id(10);
    let t_machine_node = machine_node(&t_machine_node_id, ir);
    eprintln!("\n====== z3 ======");
    eprintln!("{:#?}", t_ir_node);
    eprintln!("{:#?}", t_machine_node_id);
    eprintln!("{:#?}", t_machine_node);
}
