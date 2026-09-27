import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Unknown, "Reconstruction and Trial Verification of the Collatz Conjecture", 2022.

Title: Reconstruction and Trial Verification of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper further defines the Collatz-leaf node (corresponding to the Collatz-leaf integer) on the decimal tree. The Collatz-leaf nodes satisfy the strong Collatz conjecture. Through mathematical derivation, we prove that the Collatz-leaf node (Collatz-leaf integer) has the characteristics of inheritance. With computer large numbers and big data calculation, we conclude that all nodes at a depth of 800 are Collatz-leaf nodes. Thus, we prove that the strong Collatz conjecture is true, and therefore the Collatz conjecture must also be true. For any positive integer N greater than 1, the minimum number of Collatz transforms from N to 1 is log2 N, the maximum number of Collatz transforms is 800...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4018/ijsi.297510
-/

namespace Collatz.Papers.Journal_10_4018_ijsi_297510

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Unknown, \"Reconstruction and Trial Verification of the Collatz Conjecture\", International Journal of Software Innovation, DOI:10.4018/ijsi.297510 [2022]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_4018_ijsi_297510
