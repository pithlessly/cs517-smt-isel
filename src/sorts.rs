use z3::DatatypeBuilder;

use crate::Ir;

fn ir_node(ir: &Ir) -> z3::DatatypeSort {
    let mut builder = DatatypeBuilder::new("IrNode");
    for i in 0..ir.program.len() {
        builder = builder.variant(&format!("dag{}", i), vec![]);
    }
    builder.finish()
}

pub fn z3_main(ir: &Ir) {
    let t_ir_node = ir_node(ir);
    eprintln!("\n====== z3 ======");
    eprintln!("{:#?}", t_ir_node);
}
