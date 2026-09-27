# arxiv-2107-11160-is-the-syracuse-falling-time-bounded-by-12

Citation: Shalom Eliahou et al., "Is the Syracuse falling time bounded by 12?", arXiv:2107.11160 [2021].

Authors: Shalom Eliahou, Jean Fromentin, Rénald Simonetto

arXiv: [2107.11160](https://arxiv.org/abs/2107.11160)

Year: 2021

Classification: verification

Abstract:

Let $T \colon \mathbb{N} \to \mathbb{N}$ denote the $3x+1$ function, where $T(n)=n/2$ if $n$ is even, $T(n)=(3n+1)/2$ if $n$ is odd. As an accelerated version of $T$, we define a jump at $n \ge 1$ by jp$(n) = T^{(\ell)}(n)$, where $\ell$ is the number of digits of $n$ in base 2. We present computational and heuristic evidence leading to surprising conjectures. The boldest one, inspired by the study of $2^{\ell}-1$ for $\ell \le 500000$, states that for any $n \ge 2^{500}$, at most four jumps starting from $n$ are needed to fall below $n$, a strong form of the Collatz conjecture.

Lean file: `Collatz/Papers/Arxiv2107_11160.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
