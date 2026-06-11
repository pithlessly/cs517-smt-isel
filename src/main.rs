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
    // let content = std::fs::read_to_string("input.txt")?;
    let content =
        std::fs::read_to_string(std::env::args().nth(1).expect("please pass an input file"))?;

    let ast = parse_input::program()
        .parse(&content)
        .into_result()
        .map_err(|errs| anyhow!("{:?}", errs))?;

    let ir = ir::Ir::from_ast(&ast)?;

    let mut config = z3::Config::new();
    config.set_model_generation(true);
    z3::with_z3_config(&config, || {
        let Some(stock) = reduction::solve(&ir) else {
            eprintln!("No reduction exists!");
            return;
        };

        for (i, node) in stock.nodes.iter().enumerate() {
            println!("{i}: {node:?}");
        }
    });

    Ok(())
}
