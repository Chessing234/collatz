import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Caldin, Andrew Stewart, "The Collatz Conjecture: A Simple, Unsolved Problem Resistant to Proof — E8 Intelligence Research", 2026.

Title: The Collatz Conjecture: A Simple, Unsolved Problem Resistant to Proof — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: Collatz Conjecture — simplest unsolved problem; no computer can prove termination for all integers. | MATH: \( f(n) = \begin{cases} n/2 & \text{if } n \text{ even} \\ 3n+1 & \text{if } n \text{ odd} \end{cases} \); conjecture: iterates always reach 1. No known closed-form solution. | CONNECTION: None directly; no geometric ratios or symmetries emerge from the iteration. | DEPTH: 2 — Famous but isolated; no harmonic or crystallographic structure. FINDING: Hilbert's Decision Problem & Turing's halting problem — proof that some problems are algorithmically undecidable. | MATH: Halting problem: no Turing machine can decide if an arbitrary program halts. Equivalent to Gödel's incompleten...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21883043
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21883043

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Caldin, Andrew Stewart, \"The Collatz Conjecture: A Simple, Unsolved Problem Resistant to Proof — E8 Intelligence Research\", Zenodo, DOI:10.5281/zenodo.21883043 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21883043
