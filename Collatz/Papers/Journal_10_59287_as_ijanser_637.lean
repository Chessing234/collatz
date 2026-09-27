import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Robert Kosova et al., "The Collatz Conjecture: Bridging Mathematics and Computational Exploration with Python", 2023.

Title: The Collatz Conjecture: Bridging Mathematics and Computational Exploration with Python

Abstract (from harvested metadata, truncated):
The Collatz Conjecture, proposed by Lothar Collatz in 1937, stands as an unsolved problem within the realm of number theory. This conjecture, also known as the "3x + 1 problem" or the "hailstone sequence," revolves around a simple iterative process applied to positive integers. The conjecture states that by repeatedly applying a specific rule—dividing even numbers by 2 and multiplying odd numbers by 3 and adding 1—any positive integer will eventually reach the cycle of 4, 2, 1. Historical insights unveil the conjecture's enduring appeal, while modern computational methods showcase extensive verifications for very large integers, reinforcing its validity yet without offering definitive proof for all integers. The pursuit of counterexamples and patterns has engaged computational frontiers,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.59287/as-ijanser.637
-/

namespace Collatz.Papers.Journal_10_59287_as_ijanser_637

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Robert Kosova et al., \"The Collatz Conjecture: Bridging Mathematics and Computational Exploration with Python\", International Journal of Advanced Natural Sciences and Engineering Researches, DOI:10.59287/as-ijanser.637 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_59287_as_ijanser_637
