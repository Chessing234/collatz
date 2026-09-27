import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yamamoto, Takeo, "A Proof of the Collatz Conjecture via Finite Fractal Structure and the Extremum Principle", 2026.

Title: A Proof of the Collatz Conjecture via Finite Fractal Structure and the Extremum Principle

Abstract (from harvested metadata, truncated):
The Collatz conjecture (1937) is proven within the F-Theory axiomatic framework. The Collatz sequence is recognized as a finite fractal structure: the same rule σ applied repeatedly within the space of positive integers. By the Extremum Principle (A1), the extremum of this space is 1. Assuming non-convergence leads to contradiction with A1. Two component theorems are formally verified in Lean 4 with Mathlib (CI: green). The proof is complete.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19015856
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19015856

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yamamoto, Takeo, \"A Proof of the Collatz Conjecture via Finite Fractal Structure and the Extremum Principle\", Zenodo, DOI:10.5281/zenodo.19015856 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_19015856
