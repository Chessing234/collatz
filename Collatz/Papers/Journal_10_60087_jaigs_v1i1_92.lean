import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Gaurangkumar Girishbhai Patel, "Collatz Conjecture Solution", 2024.

Title: Collatz Conjecture Solution

Abstract (from harvested metadata, truncated):
The Collatz conjecture, also known as the 3n + 1 conjecture, stands as one of the most enduring unsolved problems in mathematics. Proposed by German mathematician Lothar Collatz in 1937, the conjecture poses a deceptively simple question: can iteratively applying two basic arithmetic operations—dividing even numbers by 2 and multiplying odd numbers by 3 and adding 1—lead any positive integer to converge to the value 1? Despite extensive computational verification for vast ranges of integers, a proof or disproof remains elusive. This abstract explores the historical background, various attempts at proving the conjecture, and its implications across mathematical domains.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.60087/jaigs.v1i1.92
-/

namespace Collatz.Papers.Journal_10_60087_jaigs_v1i1_92

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Gaurangkumar Girishbhai Patel, \"Collatz Conjecture Solution\", Journal of Artificial Intelligence General science (JAIGS) ISSN 3006-4023, DOI:10.60087/jaigs.v1i1.92 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_60087_jaigs_v1i1_92
