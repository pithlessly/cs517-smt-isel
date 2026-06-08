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

#let ir(it) = text(fill: blue, it)
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

#let pC = $ir(C)$
#let pP = $ir(P)$
#let pR = $ir(R)$
#let tt = $ir(t)$

We assume there is a fixed set of *IR opcodes* $pC$ and each opcode $α ∈ pC$ has an associated *arity*.

As input, we start with an *IR program*, which is a sequence $pP$ of *IR instructions*. Each IR instruction consists of an opcode and a tuple of arguments matching the opcode's arity.

$
  pP := &{ pP_1, ..., pP_N } \
  pP_i ::= &α (tt_1, ..., tt_m), #h(1cm) α ∈ pC, #h(0.5cm) m = "arity"(α), #h(0.5cm) 1 ≤ tt_1, ..., tt_m < i \
$

The requirement $1 ≤ tt_1, ..., tt_m < i$ captures the idea that the input program is a DAG, because each parameter of an IR instruction is the index of some previous instruction. This also means that the first instruction must be nullary.

In addition, a subset of program indices $pR ⊆ {1, ..., N}$ are designated as *results*.
An index $i ∈ R$ being contained in the set means that the result of the instruction $pP_i$ must be materialized in the machine program,
i.e. it cannot be coalesced into an intermediate computation of a machine instruction.

#bibliography(
  "works.bib",
  title: [References],
)
