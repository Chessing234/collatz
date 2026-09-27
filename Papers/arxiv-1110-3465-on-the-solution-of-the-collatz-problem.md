# arxiv-1110-3465-on-the-solution-of-the-collatz-problem

Citation: Tan, Shan-Guang, "On the solution of the Collatz problem", arXiv:1110.3465 [2011].

Authors: Tan, Shan-Guang

arXiv: [1110.3465](https://arxiv.org/abs/1110.3465)

Year: 2011

Classification: structural

Abstract:

In this paper, we first prove that given a nonnegative integer $m$ and an odd number $t$ not divisible by $3$, there exists a unique Collatz's Sequence \[ S_{c}(m,t)=\{n_{0}(m,t),n_{1}(m,t),n_{2}(m,t),\ldots,n_{m}(m,t),n_{m+1}(m,t)\} \] produced by a function $n_{i+1}(m,t)=(3n_{i}(m,t)+1)/2$ for $i=0,1,2,\ldots,m$ and ended by an even number $n_{m+1}(m,t)$ where $n_{i}(m,t)=2^{m+1-i}\times3^{i}t-1$ for $i=0,1,2,\ldots,m+1$, by which all odd numbers can be expressed.
  Then we discuss the Collatz problem in two ways and prove that each Collatz's Sequence always returns to 1, i.e., the Collatz problem is solved.

Lean file: `Collatz/Papers/Arxiv1110_3465.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-d (2026-09-15)
