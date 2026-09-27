# arxiv-1909-13218-determining-monotonic-step-equal-sequences-of-any-limit

Citation: Longjiang Li, "Determining monotonic step-equal sequences of any limited length in the Collatz problem", arXiv:1909.13218 [2019].

Authors: Longjiang Li

arXiv: [1909.13218](https://arxiv.org/abs/1909.13218)

Year: 2019

Classification: structural

Abstract:

This paper proposes a formula expression for the well-known Collatz conjecture (or 3x+1 problem), which can pinpoint all the growth points in the orbits of the Collatz map for any natural numbers. The Collatz map $Col: \mathcal{N}+1 \rightarrow \mathcal{N}+1$ on the positive integers is defined as $x_{n+1}=Col(x_n)=(3 x_n +1)/2^{m_n}$ where $x_{n+1}$ is always odd and $m_n$ is the step size required to eliminate any possible even values. The Collatz orbit for any positive integer, $x_1$, is expressed by a sequence, $$ and $x_n$ is defined as a growth point if $Col(x_n)>x_n$ holds, and we show that every growth point is in a format of ``$4y+3$'' where $y$ is any natural number. Moreover, we derive that, for any given positive integer $n$, there always exists a natural number, $x_1$, that starts a monotonic increasing or decreasing Collatz sequence of length $n$ with the same step size. Fo

Lean file: `Collatz/Papers/Arxiv1909_13218.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
