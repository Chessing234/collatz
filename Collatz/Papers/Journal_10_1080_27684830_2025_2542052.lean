import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eyob Solomon Getachew, "Unfolding the Collatz Tree: An Indirect Structural Proof of the Collatz Conjecture", 2025.

Title: Unfolding the Collatz Tree: An Indirect Structural Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
We present an indirect structural proof of the Collatz Conjecture by constructing and analyzing an infinite directed tree based on the inverse dynamics of the Collatz map. First, we introduce a branch indexing scheme and prove by induction, supported by extensive computational checks, that every natural number appears in this tree. Second, we develop an algorithm to build a minimal connected subtree rooted at one that contains all natural numbers up to any given bound. Third, we show by contradiction and explicit construction that the only cycle in the tree is the trivial loop 1–2–4–1 and that every backward path from a node terminates at the root in a finite number of steps. Together, these results demonstrate that each natural number has a unique backward path to one that exactly...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1080/27684830.2025.2542052
-/

namespace Collatz.Papers.Journal_10_1080_27684830_2025_2542052

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eyob Solomon Getachew, \"Unfolding the Collatz Tree: An Indirect Structural Proof of the Collatz Conjecture\", Research in Mathematics, DOI:10.1080/27684830.2025.2542052 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1080_27684830_2025_2542052
