# doi-10-5281-zenodo-20068639-a-delta-state-finite-automaton-framework

Citation: Moon, Kyung-Up, "A Delta-State Finite Automaton Framework for High-Energy Collatz Corridors: Exhaustive Symbolic Enumeration and Profinite State Compression", DOI:10.5281/zenodo.20068639 [2026].

Authors: Moon, Kyung-Up

DOI: [10.5281/zenodo.20068639](https://doi.org/10.5281/zenodo.20068639)

Year: 2026

Venue: (unknown)

Classification: structural

Abstract:

We introduce a Δ-state compression framework for the accelerated Collatz dynamics. High-energy valuation words w = (a₁,...,aₖ) with energy B(w) = k·log₂3 − Σaᵢ ≥ 10 are analyzed via two complementary engines. CPSE (Corridor-exit-compensation symbolic engine) exhaustively enumerates the complete finite domains W(30,{1,2},10) and W(30,{1,...,6},10), covering 1,510,808 and 13,681,233 valuation words respectively. In both cases, every word resolves into convergence to 1 or bounded-delay compensation (v₂(3n+1) ≥ 3) with zero unresolved words and maximum compensation delay at most 53. PCDS (Profinite constrained dynamical system) identifies the corrected finite-state descriptor q*(w) = (u, Δ(w) mod 2^(A(w)+m)) where u is a fixed-length suffix and Δ(w) satisfies the linear recurrence Δₖ₊₁ = 3Δₖ...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_20068639.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-i (2026-09-15)
