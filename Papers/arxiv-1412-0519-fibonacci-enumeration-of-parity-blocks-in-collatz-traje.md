# arxiv-1412-0519-fibonacci-enumeration-of-parity-blocks-in-collatz-traje

Citation: Mike Winkler, "Fibonacci Enumeration of Parity Blocks in Collatz Trajectories", arXiv:1412.0519 [2014].

Authors: Mike Winkler

arXiv: [1412.0519](https://arxiv.org/abs/1412.0519)

Year: 2014

Classification: density

Abstract:

Let $T(n)=n/2$ for even $n$ and $T(n)=(3n+1)/2$ for odd $n$. For an odd starting number $s$, let $\ell(s)$ be the first positive index $k$ for which $T^k(s)\equiv3\pmod4$ and $T^{k-1}(s)$ is even. The use of this single local cut time is the main structural step: it replaces the two block parameters of an earlier formulation and converts the endpoint condition into a local condition on consecutive parity symbols. We prove that, for every $r\geq2$, the starting numbers $s\equiv1\pmod4$ with $\ell(s)=r$ form exactly $F_{r-1}$ residue classes modulo $2^{r+2}$, while for every $r\geq3$ the starting numbers $s\equiv3\pmod4$ with $\ell(s)=r$ form exactly $F_r-1$ such classes. Fixing any odd residue class modulo $12$ leaves these counts unchanged and yields the two Fibonacci formulas conjectured in a 2014 preprint by the author as special cases. The proof uses the classical finite parity corres

Lean file: `Collatz/Papers/Arxiv1412_0519.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
