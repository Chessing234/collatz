# arxiv-2602-06066-non-definability-of-reachability-in-b-chi-arithmetic-for-a-f

Citation: Madhav Dhiman and Rohan Pandey, "Non-Definability of Reachability in Büchi Arithmetic for a Family of Generalized Collatz Maps", arXiv:2602.06066 [2026].

Authors: Madhav Dhiman, Rohan Pandey

arXiv: [2602.06066](https://arxiv.org/abs/2602.06066)

Year: 2026

Classification: verification

Abstract:

Let $q \ge 3$ and $d \ge 1$ be odd integers with $q+d$ a power of $2$. We study the generalized Collatz map $T_{q,d}$, a one-dimensional piecewise-affine map on the positive integers, and its unparameterized reachability relation $R(x,z)$, which holds when $z$ is an iterate of $x$ under $T_{q,d}$. We prove that for every such pair $(q,d)$ the relation $R$ is not first-order definable in Büchi arithmetic $\langle \mathbb{N}, +, V_q \rangle$. Equivalently, no finite automaton recognizes the base-$q$ encoding of $R$. Assuming definability of $R$, we construct a first-order formula that defines the set of powers of $2$. Cobham's theorem then rules out this set. The family includes the classical map $T_{3,1}$. The family is infinite but restricted, isolated by the condition that $q+d$ is a power of $2$ . Unlike the undecidability results of Conway, Kurtz, and Simon, the construction does not embed universal computation and does not depend on the Collatz conjecture.

Lean file: `Collatz/Papers/Arxiv2602_06066.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
