# arxiv-2001-00482-collatz-polynomials-an-introduction-with-bounds-on-thei

Citation: Matt Hohertz and Bahman Kalantari, "Collatz polynomials: an introduction with bounds on their zeros", arXiv:2001.00482 [2019].

Authors: Matt Hohertz, Bahman Kalantari

arXiv: [2001.00482](https://arxiv.org/abs/2001.00482)

Year: 2019

Classification: verification

Abstract:

The Collatz Conjecture (also known as the 3x+1 Problem) proposes that the following algorithm will, after a certain number of iterations, always yield the number 1: given a natural number, multiply by three and add one if the number is odd, halve the resulting number, then repeat. In this article, for each $N$ for which the Collatz Conjecture holds we define the $N^{th}$ Collatz polynomial to be the monic polynomial with constant term $N$ and $k^{th}$ term (for $k > 1$) the $k^{th}$ iterate of $N$ under the Collatz function. In particular, we bound the moduli of the roots of these polynomials, prove theorems on when they have rational integer roots, and suggest further applications and avenues of research.

Lean file: `Collatz/Papers/Arxiv2001_00482.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
