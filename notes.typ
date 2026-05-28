A program is of the form $(p_1...p_s)$, where each $p_i$ looks like $alpha(overline(t))$ for some instruction $alpha$ and sequence of indices $1 <= overline(t) <= i$.

A machine program is of the form $(M_1...M_k)$ where each $M_i$ looks like $c(overline(r))$ for some machine instruction $c$ and sequence of indices $1 <= overline(r) <= i$

There is also a sequence of variables $1 <= m_1...m_k <= s$ expressing the idea that machine instruction $M_i$ computes IR instruction $P_m_i$.

Define $"latency"(c(overline(r))) := max[{ "latency"(M_r) | r in overline(r) } union { 0 }] + "c.latency"$

Then $(M_1...M_k)$ is _correct_ if:
- $forall i in {1...k}: "latency"(M_i) <= L$, where $L$ is the given latency bound.
- $forall i in {1...k}: M_i = c(overline(r))$ has the correct arity for $c$, and each $r in overline(r)$ satisfies $1 <= r <= i$
- (Correct modeling) $forall i in {1...k}$:
  - #[
    #set par(spacing: 5pt)
    match $M_i$ with:
    #grid(columns: 3, inset: 4pt,
    [$"LOAD_A"()$],[$=>$],[$P_m_i = "load_a"()$],
    [$"ADD"(r_1, r_2)$],[$=>$],[$P_m_i = "add"(t_1, t_2) 
                                and (m_r_1, m_r_2) = (t_1, t_2)$],
    [$"LEA"(r_1, r_2, r_3)$],[$=>$],[$\
      &P_m_i = "add"(t_1, t_2)\
      &and P_t_2 = "shl"(t_3, t_4)\
      &and (M_r_1, M_r_2, M_r_3) = (t_1, t_2, t_3)
    $])
    ...and so on...
    ]
- For each root $P_R$, $R in "ROOTS": exists i in {1...k}: M_i = R$

Let $phi((p_1...p_s), L, k\; (M_1...M_k))$ be the formula asserting correctness. Our goal is to reduce $phi((p_1...p_s), L, k\; -)$ to Z3.
