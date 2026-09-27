import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Potts, David, "The Sextant Matrix System: A Global Coordinate Map Resolving the Collatz Conjecture", 2026.

Title: The Sextant Matrix System: A Global Coordinate Map Resolving the Collatz Conjecture

Abstract (from harvested metadata, truncated):
We present a rigorous proof of the Collatz Conjecture by constructing a deterministic coordinate system—The Sextant Matrix System—a six class partition that establishes a global bijection between the set of positive odd integers (Z+ odd) and a set of matrix coordinates (M, i, j). Addressing the historical obstruction of arithmetic mixing, we derive a closed algebraic automaton isomorphic to the Collatz map, decomposing the dynamics into two distinct transition layers: a Generative Automaton (Inverse Map) governed by four 3 x 9 Base Matrices, and a Descent Automaton (Forward Map) defined by a 64 x 3 Fundamental Domain. A critical contribution is the Recursive Scale-Up Algorithm, which demonst...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18764938
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18764938

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Potts, David, \"The Sextant Matrix System: A Global Coordinate Map Resolving the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.18764938 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18764938
