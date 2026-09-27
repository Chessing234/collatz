# arxiv-1202-3670-natural-numbers-generalized-parity-and-the-collatz-algo

Citation: Ramon Carbó-Dorca, "Natural Numbers Generalized Parity, and the Collatz Algorithm", arXiv:1202.3670 [2026].

Authors: Ramon Carbó-Dorca

arXiv: [1202.3670](https://arxiv.org/abs/1202.3670)

Year: 2026

Classification: verification

Abstract:

An extended definition of the even-odd property for natural numbers is used to highlightprime numbers in their classification. For a given natural number $M$ and a chosen prime$P$, one can say that $PM$ is $P$-even-like, and $PM+K$, with$K = [1, 2, \ldots, P-1]$, is $P$-odd-like of $K$-class. This approach enables thedescription of a generalized Collatz conjecture and an associated algorithm. A filtervector is used in a new $P$-Collatz algorithmic path to divide any number $M$ at any stepwhen it has prime factors also in the filter. If $M$ cannot be divided by any prime filtervector element, then the transformation $PM+K$ is performed. Therefore, a new formulationof the Collatz conjecture is: ``the $P$-Collatz algorithm converges to 1 for all naturalnumbers $M$, through a transformation of the form $PM+K$ (the original Collatz algorithmuses $P=3$ and $K=1$), provided that a conveniently 

Lean file: `Collatz/Papers/Arxiv1202_3670.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
