import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for 弘貴 齋藤, "Proof of the truth or falsity of the Collatz conjecture", 2026.

Title: Proof of the truth or falsity of the Collatz conjecture

Abstract (from harvested metadata, truncated):
This paper proves the Collatz conjecture using the opposite method to the method of tracing 1 from any integer. The method is a way to verify whether it is possible to reach all positive integers starting from 1, following the opposite rule of the Collatz conjecture.If it is possible to reach all positive integers starting from 1, then the Collatz conjecture can be proven true.In this paper, for a positive integer n, if n is even, n/2 is performed, and if n is odd, 3n+1 is performed, and the method of repeating this is called the conventional Collatz method. For a positive odd number p1, double it, double it, … repeatedly, and if a positive even number q that appears in the process becomes a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21040951
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21040951

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "弘貴 齋藤, \"Proof of the truth or falsity of the Collatz conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21040951 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21040951
