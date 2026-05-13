use chumsky::prelude::{IterParser as _, Parser, any, end, group, just, recursive};
use chumsky::text::Char as _;
use chumsky::text::{inline_whitespace, newline, whitespace};

fn newlines<'src>() -> impl Parser<'src, &'src str, ()> + Clone {
    newline().repeated().at_least(1)
}

#[derive(Clone)]
pub struct Term {
    pub label: String,
    pub children: Vec<Term>, // terms with no children are treated like variables
}

impl std::fmt::Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut t = f.debug_tuple(&self.label);
        for child in &self.children {
            t.field(child);
        }
        t.finish()
    }
}

// Not padded.
fn identifier<'src>() -> impl Parser<'src, &'src str, &'src str> + Clone {
    any()
        .filter(|c: &char| c.is_ident_continue())
        .repeated()
        .at_least(1)
        .to_slice()
}

// `p` parses an element is assumed padded. The resulting parser is padded on the left only.
fn argument_list<'src, T>(
    p: impl Parser<'src, &'src str, T> + Clone,
) -> impl Parser<'src, &'src str, Option<Vec<T>>> + Clone {
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
fn term<'src>() -> impl Parser<'src, &'src str, Term> {
    recursive(|term| {
        identifier()
            .map(String::from)
            .then(argument_list(term.padded()))
            .map(|(label, children)| Term {
                label,
                children: children.unwrap_or_default(),
            })
    })
}

#[derive(Debug)]
pub struct ProgramLine {
    pub label: String,
    pub def: Term,
}

fn program_line<'src>() -> impl Parser<'src, &'src str, ProgramLine> {
    identifier()
        .map(String::from)
        .padded()
        .then_ignore(just('=').padded())
        .then(term())
        .then_ignore(inline_whitespace())
        .then_ignore(newlines())
        .map(|(label, def)| ProgramLine { label, def })
}

type Latency = u32;

// Not padded.
fn latency<'src>() -> impl Parser<'src, &'src str, Latency> {
    just('#')
        .repeated()
        .count()
        .try_map(|x: usize, _| u32::try_from(x).map_err(|_| Default::default()))
        .delimited_by(just('('), just(')'))
}

#[derive(Debug)]
pub struct MachineDefLine {
    pub name: String,
    pub args: Vec<String>,
    pub def: Term,
    pub latency: Latency,
}

fn machine_def_line<'src>() -> impl Parser<'src, &'src str, MachineDefLine> {
    group((
        latency().padded(),
        identifier().map(String::from),
        argument_list(identifier().map(String::from).padded()).map(Option::unwrap_or_default),
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
pub struct Ast {
    program: Vec<ProgramLine>,
    machine: Vec<MachineDefLine>,
}

pub fn program<'src>() -> impl Parser<'src, &'src str, Ast> {
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
