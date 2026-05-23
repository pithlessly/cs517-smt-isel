use anyhow::{Result, anyhow};
use chumsky::Parser as _;

mod ir;
mod parse_input;

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
    sorts::z3_main(&ir);
    Ok(())
}
