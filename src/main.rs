use anyhow::{Result, anyhow};
use chumsky::Parser as _;

mod build_dag;
mod parse_input;

use parse_input::Latency;

fn main() -> Result<()> {
    let content = std::fs::read_to_string("input.txt")?;
    let ast = parse_input::program()
        .parse(&content)
        .into_result()
        .map_err(|errs| anyhow!("{:?}", errs))?;
    eprintln!("{:?}", ast);
    let dag = build_dag::Dag::from_program(&ast.program)?;
    eprintln!("{:?}", dag);
    Ok(())
}
