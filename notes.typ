== I/O data types

The input data structure is an *IR program*, which is a sequence of *IR instructions* of the form $(P_1...P_s)$, where each instruction is of the form $P_i = alpha(overline(t))$.
The opcode $alpha$ is drawn from some finite set, and $overline(t) = t_1, ..., t_n$ is a sequence of indices $1 <= t_1, ..., t_n < i$. (This captures the idea that forward references are forbidden.) A subset of the IR instructions are designated *roots*, meaning that the output program must compute them.

The output data structure is a *machine program*, which is similarly a sequence $(M_1...M_k)$ of *machine instructions* $M_i = c(overline(r))$. The opcode $c$ is drawn from some finite set (disjoint from the opcodes used by IR instructions), and $overline(r) = r_1, ..., r_n$ is a sequence of indices $1 <= r_1, ..., r_i < i$.

It's worth noting that we usually think of the compilation process as proceeding from complex instructions to simple instructions, but here we have isolated the problem of dealing with CPU architectures that have complex macroinstructions corresponding to more than one IR instruction (e.g. `LEA(a, b, r, c) = add(add(a, shift(b, r)), c)`) and making use of these instructions in the optimal way.

== The reduction to SMT

The output variables $M_1, ..., M_k$ are to be solved for. We also introduce another a sequence of integer variables $m_1, ..., m_k in {1, s}$ with the following semantics: $m_i = j$ asserts that the machine instruction $M_i$ is responsible for computing the value of the IR instruction $P_j$.

We define the latency of a machine instruction $M = c(overline(r_1))$ as

$ "latency"(M)) := max{ 0, "latency"(M_r_1), ..., "latency"(M_r_n) } + (c."latency"), $

where $c."latency"$ is the declared latency of the opcode $c$ itself.

We say an output program is _correct_ if all of the following conditions are met:

- *Well-formedness:* for each $i$, the instruction $M_i = c(overline(r))$ has the correct arity for $c$, and each $r_j$ satisfies $1 <= r_j < i$.
- *The program meets its latency bound:* $forall i in {1...k}: "latency"(M_i) <= L$, where $L$ is the given latency bound.
- *Faithful emulation:* For each $i$, the correctness rule for $M_i$ looks something like
  - #[
    #set par(spacing: 5pt)
    (match $M_i$ with:
    #grid(columns: 3, inset: 4pt,
    [$"  LOAD_A"()$],[$=>$],[$#hide[$and$] P_m_i = "load_a"()$],
    [$"  ADD"(r_1, r_2)$],[$=>$],[$#hide[$and$] P_m_i = "add"(t_1, t_2) 
                                and (m_r_1, m_r_2) = (t_1, t_2)$],
    [$"  LEA"(r_1, r_2, r_3)$],[$=>$],[$\
          &P_m_i = "add"(t_1, t_2)\
      and &P_t_2 = "shl"(t_3, t_4)\
      and &(m_r_1, m_r_2, m_r_3) = (t_1, t_2, t_3)
    $])
    ...and so on...)
    ]
- *All roots are computed:* For each $p_r$ designated as a root, there is some $i in {1...k}$ such that $m_i = r$.

We can write the formula asserting correctness of the output program as

$ phi((P_1, ..., P_s), L, k \; (M_1, ..., M_k), (m_1, ..., m_k)). $

Our goal is to reduce this formula to Z3, where $(P_1, ..., P_s), L, k$ are fixed inputs and $(M_1, ..., M_k), (m_1, ..., m_k)$ are the variables solved with Z3.
