use anyhow::{Result, anyhow};
use chumsky::Parser as _;

mod ir;
mod parse_input;

mod reduction;
mod sorts;

use ir::Ir;
use parse_input::{Arity, Latency};

fn main() -> Result<()> {
    let content = std::fs::read_to_string("input.txt")?;
    let ast = parse_input::program()
        .parse(&content)
        .into_result()
        .map_err(|errs| anyhow!("{:?}", errs))?;
    eprintln!("{:?}", ast);
    let ir = ir::Ir::from_ast(&ast)?;
    eprintln!("{:?}", ir);

    eprintln!("{:?}", ir.program.nodes.len());

    let machine_program_len = 10;

    let sorts = sorts::SolverSorts::new(&ir, machine_program_len);
    eprintln!("{:#?}", sorts);

    let variables = reduction::Variables::new(&ir, machine_program_len, &sorts);
    eprintln!("{:#?}", variables);

    Ok(())
}
