use anyhow::{Result, anyhow};
use chumsky::Parser as _;

mod ir;
mod parse_input;

mod extraction;
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

    let ir = ir::Ir::from_ast(&ast)?;

    let machine_program_len = 10;

    let mut config = z3::Config::new();
    config.set_model_generation(true);
    z3::with_z3_config(&config, || {
        let sorts = sorts::SolverSorts::new(&ir, machine_program_len);
        eprintln!("{:#?}", sorts);

        reduction::solve(&ir, machine_program_len, &sorts);
    });

    Ok(())
}
