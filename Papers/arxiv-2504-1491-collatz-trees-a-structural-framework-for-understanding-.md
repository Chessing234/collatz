# arxiv-2504-1491-collatz-trees-a-structural-framework-for-understanding-

Citation: Kazuhito Owada, "Collatz Trees: A Structural Framework for Understanding the 3x+1 Problem", arXiv:2504.1491 [2025].

Authors: Kazuhito Owada

arXiv: [2504.1491](https://arxiv.org/abs/2504.1491)

Year: 2025

Classification: cycle

Abstract:

The Collatz Conjecture remains one of the most enduring unsolved problems in mathematics, despite being based on an extraordinarily simple rule. Given any natural number n, the conjecture posits that repeatedly applying the operation—dividing by 2 if even, or multiplying by 3 and adding 1 if odd—will eventually result in the number 1.This paper develops a structural perspective by proposing the Collatz Tree as a framework to organize and visualize natural numbers. Each branch is the geometric ray {k·2^b} for an odd core k, and the trunk is the ray from 1. We introduce a trunk–branch indexing that bijects N with Z≥0 × Z≥0.Algebraically, we encode Collatz steps as affine maps and prove the absence of nontrivial finite cycles for a three-way map T. Through a bridge theorem, this implies the same for the standard accelerated map A(n) = (3n+1)/2^ν₂(3n+1) on odd integers. Thus, the global Coll

Lean file: `Collatz/Papers/Arxiv2504_1491.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
