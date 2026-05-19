use chumsky::error::Rich;
use chumsky::prelude::{IterParser as _, Parser, end, group, just, recursive};
use chumsky::text::{digits, ident, inline_whitespace, newline, whitespace};

type Err<'src> = chumsky::extra::Err<Rich<'src, char>>;

fn newlines<'src>() -> impl Parser<'src, &'src str, (), Err<'src>> + Clone {
    newline().repeated().at_least(1)
}

#[derive(Clone)]
pub struct Term<'src> {
    pub label: &'src str,
    pub children: Option<Vec<Term<'src>>>, // terms with no children are treated like variables
}

impl<'src> std::fmt::Debug for Term<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut t = f.debug_tuple(&self.label);
        match self.children.as_deref() {
            None => {}
            Some([]) => {
                t.field(&format_args!(""));
            }
            Some(children) => {
                for child in children {
                    t.field(child);
                }
            }
        }
        t.finish()
    }
}

// `p` parses an element is assumed padded. The resulting parser is padded on the left only.
fn argument_list<'src, T>(
    p: impl Parser<'src, &'src str, T, Err<'src>> + Clone,
) -> impl Parser<'src, &'src str, Option<Vec<T>>, Err<'src>> + Clone {
    p.separated_by(just(','))
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(
            inline_whitespace().ignore_then(just('(')),
            whitespace().ignore_then(just(')')),
        )
        .or_not()
}

// Not padded.
fn term<'src>() -> impl Parser<'src, &'src str, Term<'src>, Err<'src>> {
    recursive(|term| {
        ident()
            .or(digits(10).to_slice())
            .then(argument_list(term.padded()))
            .map(|(label, children)| Term { label, children })
    })
}

#[derive(Debug)]
pub struct ProgramLine<'src> {
    pub label: &'src str,
    pub def: Term<'src>,
}

fn program_line<'src>() -> impl Parser<'src, &'src str, ProgramLine<'src>, Err<'src>> {
    ident()
        .padded()
        .then_ignore(just('=').padded())
        .then(term())
        .then_ignore(inline_whitespace())
        .then_ignore(newlines())
        .map(|(label, def)| ProgramLine { label, def })
}

pub type Latency = u32;

// Not padded.
fn latency<'src>() -> impl Parser<'src, &'src str, Latency, Err<'src>> {
    just('#')
        .repeated()
        .count()
        .try_map(|x: usize, span| u32::try_from(x).map_err(|e| Rich::custom(span, e.to_string())))
        .delimited_by(just('('), just(')'))
}

#[derive(Debug)]
pub struct MachineDefLine<'src> {
    pub name: &'src str,
    pub args: Vec<&'src str>,
    pub def: Term<'src>,
    pub latency: Latency,
}

fn machine_def_line<'src>() -> impl Parser<'src, &'src str, MachineDefLine<'src>, Err<'src>> {
    group((
        latency().padded(),
        ident(),
        argument_list(ident().padded()).map(Option::unwrap_or_default),
        just(":=").padded().ignored(),
        term(),
        inline_whitespace(),
        newlines(),
    ))
    .map(|(latency, name, args, (), def, (), ())| MachineDefLine {
        name,
        args,
        def,
        latency,
    })
}

#[derive(Debug)]
pub struct Ast<'src> {
    program: Vec<ProgramLine<'src>>,
    machine: Vec<MachineDefLine<'src>>,
}

pub fn program<'src>() -> impl Parser<'src, &'src str, Ast<'src>, Err<'src>> {
    let program_header = just("[program]")
        .padded_by(inline_whitespace())
        .then_ignore(newlines());
    let machine_header = just("[machine]")
        .padded_by(inline_whitespace())
        .then_ignore(newlines());

    let program_section = program_header.ignore_then(program_line().repeated().collect());
    let machine_section = machine_header.ignore_then(machine_def_line().repeated().collect());

    program_section
        .then(machine_section)
        .map(|(program, machine)| Ast { program, machine })
        .then_ignore(end())
}
