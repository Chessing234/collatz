# arxiv-2310-13930-note-on-collatz-conjecture

Citation: Abdelrahman Ramzy, "Note on Collatz conjecture", arXiv:2310.13930 [2023].

Authors: Abdelrahman Ramzy

arXiv: [2310.13930](https://arxiv.org/abs/2310.13930)

Year: 2023

Classification: density

Abstract:

In this paper, we show that if the numbers in the range $[1,2^n]$ satisfy Collatz conjecture, then almost all integers in the range $[2^n+1,2^{n+1}]$ will satisfy the conjecture as $n \to \infty$. The previous statement is equivalent to claiming that almost all integers in $[2^n+1,2^{n+1}]$ will iterate to a number less than $2^n$. This actually has been proved by many previous results. But in this paper we prove this claim using different methods. We also utilize our assumption on numbers in $[1,2^n]$ to show that there are a set of integers (denoted by $p\operatorname{-}C$) whose seem to be not iterating to a number less than $2^n$, but since they are connected to Collatz numbers in $[1,2^n]$ they eventually will iterate to $1$. We address the distribution of $p\operatorname{-}C$ and give an explicit formula which computes a lower bound to the number of these integers. We also show (computationally) that the number of $p\operatorname{-}C$ in a given interval is proportional to the nu

Lean file: `Collatz/Papers/Arxiv2310_13930.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
