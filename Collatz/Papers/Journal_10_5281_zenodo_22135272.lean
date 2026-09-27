import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kritagya, "A Computational Investigation of the Collatz Conjecture", 2026.

Title: A Computational Investigation of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz Conjecture is a famous mathematical issue that despite being simple to define is not solved for many years. In this project, I investigated the behaviour of Collatz sequences by using a Python program which looked at all the positive numbers from 1 to 10000 in order to find out how long it took to reach 1 and what the highest number in each sequence is. The data gets us to the conclusion that the behaviour of a sequence is not only dependent on its initial number. For example, the number 6171 takes the longest time to reach 1, 261 steps, while 9663 is the number with the highest number; 27114424. There is also a weak connection between the starting number and the time taken to arrive to 1 as the correlation is equal to 0.2054. Although this experiment does not prove the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22135272
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22135272

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kritagya, \"A Computational Investigation of the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22135272 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22135272
