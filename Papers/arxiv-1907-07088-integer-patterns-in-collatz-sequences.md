# arxiv-1907-07088-integer-patterns-in-collatz-sequences

Citation: Zenon B. Batang, "Integer patterns in Collatz sequences", arXiv:1907.07088 [2019].

Authors: Zenon B. Batang

arXiv: [1907.07088](https://arxiv.org/abs/1907.07088)

Year: 2019

Classification: structural

Abstract:

The Collatz conjecture asserts that repeatedly iterating $f(x) = (3x + 1)/2^{a(x)}$, where $a(x)$ is the highest exponent for which $2^{a(x)}$ exactly divides $3x+1$, always lead to $1$ for any odd positive integer $x$. Here, we present an arborescence graph constructed from iterations of $g(x) = (2^{e(x)}x - 1)/3$, which is the inverse of $f(x)$ and where $x \not \equiv [0]_3$ and $e(x)$ is any positive integer satisfying $2^{e(x)}x - 1 \equiv [0]_3$, with $[0]_3$ denoting $0\pmod{3}$. The integer patterns inferred from the resulting arborescence provide new insights into proving the validity of the conjecture.

Lean file: `Collatz/Papers/Arxiv1907_07088.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
