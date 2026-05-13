use chumsky::Parser as _;

mod parse_input;

fn main() -> std::io::Result<()> {
    let content = std::fs::read_to_string("input.txt")?;
    eprintln!("{:?}", parse_input::program().parse(&content));
    Ok(())
}
