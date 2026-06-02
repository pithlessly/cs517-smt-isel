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
#set text(size: 10pt)

#let ir(it) = text(fill: blue, it)
#let machine(it) = text(fill: red, it)

#show regex("IR (instruction|program)s?"): ir
#show regex("macroinstructions?"): machine
#show regex("machine (instruction|program)s?"): machine

#preamble([SAT Project Outline], [CS517], 
                                 [#ir[Christine Lin], #machine[Raine Wheary]],
                                 link("https://github.com/pithlessly/cs517-smt-isel")[GitHub project])

== I/O data types

#let Pr = ir($P$)
#let tt = ir($t$)

The input data structure is an *IR program*, which is a sequence of *IR instructions* of the form $(Pr_1, ..., Pr_s)$, where each instruction is of the form $Pr_i = alpha(overline(tt))$.
The opcode $alpha$ is drawn from some finite set, and $overline(tt) = tt_1, ..., tt_n$ is a sequence of indices $1 <= tt_1, ..., tt_n < i$. (This captures the idea that forward references are forbidden.) A subset of the IR instructions are designated *roots*, meaning that the output program must compute them.

#let Ma = machine($M$)
#let rr = machine($r$)

The output data structure is a *machine program*, which is similarly a sequence $(Ma_1, ..., Ma_k)$ of *machine instructions* $Ma_i = c(overline(rr))$. The opcode $c$ is drawn from some finite set (disjoint from the opcodes used by IR instructions), and $overline(rr) = rr_1, ..., rr_n$ is a sequence of indices $1 <= rr_1, ..., rr_i < i$.

It's worth noting that we usually think of the compilation process as proceeding from complex instructions to simple instructions, but here we have isolated the problem of dealing with CPU architectures that have complex macroinstructions corresponding to more than one IR instruction (e.g. `LEA(a, b, r, c) = add(add(a, shift(b, r)), c)`) and making use of these #machine[instructions] in the optimal way.

== The reduction to SMT

The output variables $Ma_1, ..., Ma_k$ are to be solved for. We also introduce another sequence of integer variables $m_1, ..., m_k in {1, ..., s}$ with the following semantics: $m_i = j$ asserts that the machine instruction $Ma_i$ is responsible for computing the value of the IR instruction $Pr_j$.

We define the latency of a machine instruction $Ma = c(overline(rr))$ as

$ "latency"(Ma) := max{ 0, "latency"(Ma_rr_1), ..., "latency"(Ma_rr_n) } + (c."latency"), $

where $c."latency"$ is the declared latency of the opcode $c$ itself.

We say an output program is _correct_ if all of the following conditions are met:

- *Well-formedness:* for each $i$, the instruction $Ma_i = c(overline(rr))$ has the correct arity for $c$, and each $rr_j$ satisfies $1 <= rr_j < i$.
- *The program meets its latency bound:* $forall i in {1, ..., k}: "latency"(Ma_i) <= L$, where $L$ is the given latency bound.
- *Faithful emulation:* For each $i$, the correctness rule for $Ma_i$ looks something like
  - #[
    #set par(spacing: 5pt)
    (match $Ma_i$ with:
    #grid(columns: 3, inset: 4pt,
    [$"LOAD_A"()$],[$=>$],[$#hide[$and$] Pr_m_i = "load_a"()$],
    [$"ADD"(rr_1, rr_2)$],[$=>$],[$#hide[$and$] Pr_m_i = "add"(tt_1, tt_2) 
                                and (m_rr_1, m_rr_2) = (tt_1, tt_2)$],
    [$"LEA"(rr_1, rr_2, rr_3)$],[$=>$],[$\
          &Pr_m_i = "add"(tt_1, tt_2)\
      and &Pr_tt_2 = "shl"(tt_3, tt_4)\
      and &(m_rr_1, m_rr_2, m_rr_3) = (tt_1, tt_2, tt_3)
    $])
    ...and so on...)
    ]
- *All roots are computed:* For each $p_rr$ designated as a root, there is some $i in {1...k}$ such that $m_i = rr$.

We can write the formula asserting correctness of the output program as

$ phi((Pr_1, ..., Pr_s), L, k \; (Ma_1, ..., Ma_k), (m_1, ..., m_k)). $

Our goal is to reduce this formula to Z3, where $(Pr_1, ..., Pr_s), L, k$ are fixed inputs and $(Ma_1, ..., Ma_k), (m_1, ..., m_k)$ are the variables solved with Z3.
