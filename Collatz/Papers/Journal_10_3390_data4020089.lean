import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Reduced Collatz Dynamics Data Reveals Properties for the Future Proof of Collatz Conjecture", 2019.

Title: Reduced Collatz Dynamics Data Reveals Properties for the Future Proof of Collatz Conjecture

Abstract (from harvested metadata, truncated):
Collatz conjecture is also known as 3X + 1 conjecture. For verifying the conjecture, we designed an algorithm that can output reduced dynamics (occurred 3 × x + 1 or x/2 computations from a starting integer to the first integer smaller than the starting integer) and original dynamics of integers (from a starting integer to 1). Especially, the starting integer has no upper bound. That is, extremely large integers with length of about 100,000 bits, e.g., 2100000 − 1, can be verified for Collatz conjecture, which is much larger than current upper bound (about 260). We analyze the properties of those data (e.g., reduced dynamics) and discover the following laws; reduced dynamics is periodic and the period is the length of its reduced dynamics; the count of x/2 equals to minimal integer that...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3390/data4020089
-/

namespace Collatz.Papers.Journal_10_3390_data4020089

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Reduced Collatz Dynamics Data Reveals Properties for the Future Proof of Collatz Conjecture\", Data, DOI:10.3390/data4020089 [2019]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_3390_data4020089
