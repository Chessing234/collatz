# arxiv-1504-00212-new-results-on-the-stopping-time-behaviour-of-the-colla

Citation: Mike Winkler, "New results on the stopping time behaviour of the Collatz 3x + 1 function", arXiv:1504.00212 [2015].

Authors: Mike Winkler

arXiv: [1504.00212](https://arxiv.org/abs/1504.00212)

Year: 2015

Classification: verification

Abstract:

Let $σ_n=\lfloor1+n\cdot\log_23\rfloor$. For the Collatz 3x + 1 function exists for each $n\in\mathbb{N}$ a set of different residue classes $(\text{mod}\ 2^{σ_n})$ of starting numbers $s$ with finite stopping time $σ(s)=σ_n$. Let $z_n$ be the number of these residue classes for each $n\geq0$ as listed in the OEIS as A100982. It is conjectured that for each $n\geq4$ the value of $z_n$ is given by the formula \begin{align*} z_n=\frac{(m+n-2)!}{m!\cdot(n-2)!}-\sum_{i=2}^{n-1}\binom{\big\lfloor\frac{3(n-i)+δ}{2}\big\rfloor}{n-i}\cdot z_i, \end{align*} where $m=\big\lfloor(n-1)\cdot\log_23\big\rfloor-(n-1)$ and $δ\in\mathbb{Z}$ assumes different values within the sum at intervals of 5 or 6 terms. This allows us to create an iterative algorithm which generates $z_n$ for each $n>6$.

Lean file: `Collatz/Papers/Arxiv1504_00212.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
