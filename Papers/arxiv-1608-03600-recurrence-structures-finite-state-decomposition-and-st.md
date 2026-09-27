# arxiv-1608-03600-recurrence-structures-finite-state-decomposition-and-st

Citation: Sawon Pratiher, "Recurrence Structures, Finite State Decomposition, and Statistical Bias in Collatz Path Sequences", arXiv:1608.03600 [2016].

Authors: Sawon Pratiher

arXiv: [1608.03600](https://arxiv.org/abs/1608.03600)

Year: 2016

Classification: cycle

Abstract:

We investigate the structure of Collatz path sequences $\{F^k(n)\}_{k=0}^{\infty}$ for positive integers $n$, where $F$ denotes the standard Collatz map. By classifying natural numbers into residue classes modulo~4, we establish that the Collatz conjecture reduces to verifying convergence for integers congruent to $3 \pmod{4}$. For this class, we identify six recurrent forms -- residue classes modulo~9 -- through which the path sequence elements cycle, and we prove that these forms are \emph{complete} in the sense that every power of~2 belongs to exactly one of them. We construct a deterministic finite state machine (FSM) whose states correspond to these six forms and whose transitions encode the Collatz dynamics, yielding a system of coupled functional equations involving linear congruences. We prove closed-form characterizations of the power-of-2 elements within three of the six recurr

Lean file: `Collatz/Papers/Arxiv1608_03600.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
