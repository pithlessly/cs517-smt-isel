#let preamble(name, class, me, linkto) = {
  grid(
    columns: (60%, 40%),
    row-gutter: 8pt,
    grid.cell(rowspan: 3, text(weight: "bold", size: 2em, name)),
    align(right, text(size: 12pt, class)),
    align(right, text(size: 12pt, me)),
    align(right, text(size: 12pt, linkto)),
  )
  line(length: 100%)
}

#show link: it => underline(it)
#show heading: it => [
  #it
  #v(0.4em)
]
#set text(size: 10pt)
#set par(justify: true)

#let ir(it) = text(fill: rgb("#0069c5"), it)
#let machine(it) = text(fill: red, it)

#preamble([Instruction Selection & \ Scheduling via SMT],
          [CS517], 
          [#ir[Raine Wheary], #machine[Christine Lin]],
          link("https://github.com/pithlessly/cs517-smt-isel")[GitHub project])

We consider the problem of backend code generation in a compiler. By this point in the pipeline, we can understand the input program as having been reduced to a graph of basic operations in some intermediate representation (IR). The backend must further lower these operations into machine instructions.

For linear control flow (i.e. within a single basic block), there are three major tasks to be solved:

- *Instruction selection:*
  Modern CPU architectures often have complex macroinstructions encoding more than one basic operation. For example, the x86-64 instruction `mov rax, [rcx + 4*rdx + 28]` involves a left shift, two additions, and a load. Other examples include stack operations, multiple loads and stores (e.g. ARM's `ldp` and `stp`), and fused-multiply-add. A compiler will prefer to emit these instructions when applicable, but it can be a net loss if it means intermediate results are no longer available and need to be recomputed. In the last example, if the address value `rcx + 4*rdx + 28` was used in many places, a compiler should compute this effective address with `lea` and reuse it, rather than doing the calculation inside the `mov`.

- *Instruction scheduling:*
  Even when two machine instructions could are independent of each other, their order relative to each other can impact the performance of the generated code. We model a pipelined but not out-of-order processor, where a pipeline stall occurs if an instruction's inputs are not available.

- *Register allocation:*
  Programs in IR form use an unlimited number of virtual registers,
  but these need to be mapped to a limited number of physical registers on the machine.

Each of these tasks should be understood as a search problem. Classically, the backend is split into three phases, with instruction selection, instruction scheduling, and register allocation being performed in order @blindell2013surveyinstructionselectionextensive. However, this architecture has its limitations. When deciding whether to emit a higher-latency macroinstruction, there are situations where the optimal choice depends on register pressure or on the ability of the scheduler to avoid a pipeline stall.

Register allocation is well known to be NP-complete, and is typically solved with heuristic algorithms in practice. We will focus on an integrated algorithm for first two problems via reduction to SMT.

= Problem statement

We will adopt the convention of coloring words and variables related to the IR (the input) #ir[blue] and those related to the machine program (the output) #machine[red].

#show regex("IR (instruction|program)s?"): ir
#show regex("macroinstructions?"): machine
#show regex("machine (instruction|program)s?"): machine

== 1) The IR program

#let fv = "fv"
#let arity = "arity"
#let tree = "tree"

#let pC = $ir(C)$
#let pP = $ir(P)$
#let pR = $ir(R)$
#let pτ = $ir(τ)$
#let tt = $ir(t)$

We assume there is a fixed finite set of *IR opcodes* $pC$ and each opcode $α ∈ pC$ has an associated *arity*.

As input, we start with an *IR program*, which is a sequence $pP$ of *IR instructions*. Each IR instruction consists of an opcode and a tuple of arguments matching the opcode's arity.

$
  pP := &{ pP_1, ..., pP_N } \
  pP_i ::= &α (tt_1, ..., tt_m), #h(1cm) α ∈ pC, #h(0.5cm) m = arity(α), #h(0.5cm) 1 ≤ tt_1, ..., tt_m < i. \
$

The requirement $1 ≤ tt_1, ..., tt_m < i$ captures the idea that the input program is a DAG, because each parameter of an IR instruction is the index of some previous instruction. This also means that the first instruction must be nullary.

In addition to the sequence of instructions, a subset of program indices $pR ⊆ {1, ..., N}$ are designated as *results*. An index $i ∈ pR$ being present in the set means that the result of the instruction $pP_i$ must be materialized in the machine program,
i.e. it cannot be coalesced into an intermediate computation of a machine instruction.

#block(breakable: false)[

  For each instruction $pP_i$ in a given IR program, we can build an *expression tree* (denoted $tree(pP_i)$) by recursively replacing the indices $tt$ in the parameter list with the nodes they refer to:

  $
    tree(pP_i) := & α (tree(pP_tt_1), ..., tree(pP_tt_m))
    \ & #[*where*] pP_i = α (tt_1, ..., tt_m)
  $

]

(Expression trees cannot actually be materialized in an implementation, since they may be exponentially large without sharing, but they are useful concept in the specification of the problem.)

== 2) The machine program

#let mM = machine($M$)
#let rr = machine($r$)
#let mC = machine($C'$)

We have a finite set $mC$ of *machine opcodes* $β ∈ mC$ with associated arities. A *machine program* $mM$ has a similar structure to the input program: it consists of a sequence ${ mM_1, ..., mM_K }$ of *machine instructions*, each of which consists of an opcode and a number of previous argument references that matches the arity.

$
  mM := &{ mM_1, ..., mM_K } \
  mM_j ::= &α (rr_1, ..., rr_m), #h(1cm) β ∈ mC, #h(0.5cm) m = arity(β), #h(0.5cm) 1 ≤ rr_1, ..., rr_m < j. \
$

As a convention, we use variables $i$ and $tt$ as indexes of IR instructions and $j$ and $rr$ for machine instructions.

A machine instruction is thought of as standing in for one or more IR instructions. For example, we could imagine a machine opcode $machine("FMA")$ of arity 2, where $machine("FMA")(a, b, c)$ represents the computation $ir("add")(a, ir("mul")(b, c))$. We formalize this with the idea of a *machine definition* $D$, which associates each $n$-ary machine opcode $β$ with a definition in terms of a tree of IR instructions with $n$ free variables, written $pτ$.

$
  pτ ::= & x_k & "(free variable)" \
  | & α (pτ_1, ..., pτ_m) & α ∈ pC, #h(0.2cm) m = arity(α) \
  \
  fv(pτ) := &
    cases(
      {x_k} & "if" pτ = x_k,
      union.big_(k=1)^m fv(pτ_k) #h(0.4cm) & "if" pτ = α (pτ_1, ..., pτ_m)
    )
  & #[ (set of free variables of a tree $pτ$) ] \
  D_β ::= & ((x_1, ..., x_m), pτ) & β ∈ mC, #h(0.2cm) m = arity(β), #h(0.2cm) fv(pτ) = {x_1, ..., x_m} \
$

Given a machine definition $D_β = ((x_1, ..., x_m), pτ)$, we can apply it to a concrete $m$-tuple of trees, written as $D_β (pτ_1, ..., pτ_m)$, by substituting each $x_k$ for $pτ_k$ in the body of the definition $pτ$.

Given a machine program and a collection of machine definitions, we can define an analogous notion of *expression tree* for each instruction $mM_j$.

$
  tree(D, mM_j) := & D_β (tree(D, mM_rr_1), ..., tree(D, mM_rr_m))
  \ & #[*where*] mM_j = β (rr_1, ..., rr_m)
$

For a fixed $pC, mC, D$, we say that an instruction $mM_j$ in a machine program *models* an IR instruction $pP_i$ if $tree(pP_i) = tree(D, mM_j)$. In other words, $mM_j$ computes the same expression tree as $pP_i$.

Then we can say that a machine program $mM$ *models* an IR program $(pP, pR)$ if for each designated result $i ∈ pR$ there exists some instruction $mM_j$ that models $pP_i$. In other words, every IR instruction designated as a result is computed by some machine instruction. Also note that the modeling requirement does not forbid the machine program from containing unnecessary instructions.

Notice that if an index $i$ is not present in $pR$ then there is no requirement that the machine program materialize the value of $pP_i$. This is what allows the compiler to use instructions like $machine("FMA")(a, b, c)$ when we don't need the intermediate computation $ir("mul")(b, c)$ to ultimately be saved in a register.

#bibliography(
  "works.bib",
  title: [References],
)
