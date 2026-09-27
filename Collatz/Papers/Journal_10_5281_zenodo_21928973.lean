import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz Conjecture Highlighted as Key Unsolved Problem in MATH Dataset — E8 Intelligence Research", 2026.

Title: Collatz Conjecture Highlighted as Key Unsolved Problem in MATH Dataset — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: No unsolved competition problem identified; Collatz Conjecture highlighted as simplest unsolved problem, and MATH dataset introduced for machine learning evaluation. MATH: Collatz Conjecture: \( f(n) = \begin{cases} n/2 & \text{if } n \text{ even} \\ 3n+1 & \text{if } n \text{ odd} \end{cases} \); no known closed-form solution or proof of convergence for all \( n \in \mathbb{N} \). CONNECTION: None — Collatz dynamics lack known geometric ratios or symmetries; no link to 0.382, 0.618, 0.786, 1.618, 2.618, base-60, or crystallographic structures. DEPTH: 2 — Collatz is a well-known open problem but yields no new geometric or harmonic insight; MATH dataset is a benchmark, not a discover...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21928973
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21928973

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz Conjecture Highlighted as Key Unsolved Problem in MATH Dataset — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21928973 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21928973
