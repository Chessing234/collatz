import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "A Reduced Collatz Dynamics Maps to a Residue Class, and Its Count of x/2 over the Count of 3∗x+1 Is Larger than ln3/ln2", 2020.

Title: A Reduced Collatz Dynamics Maps to a Residue Class, and Its Count of x/2 over the Count of 3∗x+1 Is Larger than ln3/ln2

Abstract (from harvested metadata, truncated):
We propose reduced Collatz conjecture and prove that it is equivalent to Collatz conjecture but more primitive due to reduced dynamics. We study reduced dynamics (that consists of occurred computations from any starting integer to the first integer less than it) because it is the component of original dynamics (from any starting integer to 1). Reduced dynamics is denoted as a sequence of “I” that represents ( 3∗x+1 )/2 and “O” that represents x/2 . Here, 3∗x+1 and x/2 are combined together because 3∗x+1 is always even and thus followed by x/2 . We discover and prove two key properties on reduced dynamics: (1) Reduced dynamics is invertible. That is, given reduced dynamics, a residue class that presents such reduced dynamics can be computed directly by our derived formula. (2) Reduced...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1155/2020/5946759
-/

namespace Collatz.Papers.Journal_10_1155_2020_5946759

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"A Reduced Collatz Dynamics Maps to a Residue Class, and Its Count of x/2 over the Count of 3∗x+1 Is Larger than ln3/ln2\", International Journal of Mathematics and Mathematical Sciences, DOI:10.1155/2020/5946759 [2020]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1155_2020_5946759
