# arxiv-2505-01372-bidirectional-dynamics-in-the-collatz-problem-a-complet

Citation: Eduardo Diedrich, "Bidirectional Dynamics in the Collatz Problem: A Complete Resolution", arXiv:2505.01372 [2025].

Authors: Eduardo Diedrich

arXiv: [2505.01372](https://arxiv.org/abs/2505.01372)

Year: 2025

Classification: cycle

Abstract:

The Collatz conjecture states that iterating the function $C(n) = n/2$ for even $n$ and $C(n) = 3n+1$ for odd $n$ eventually leads to 1 for any positive integer $n$. Despite its elementary formulation, the conjecture has resisted resolution for over 80 years. This paper introduces a novel bidirectional approach that analyzes both forward trajectories and backward paths simultaneously. We establish two independent properties: (1) all backward paths under the generator function (a multivalued mapping that inverts the Collatz function) are finite and terminate at elements of $\{1,2,4\}$, and (2) $\{1,4,2\}$ is the unique cycle in the Collatz system. We then construct a formal structural bridge connecting these properties, proving that all Collatz sequences must reach 1. Our work introduces a global convergence measure that rigorously prohibits divergent orbits and provides explicit bounds o

Lean file: `Collatz/Papers/Arxiv2505_01372.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
