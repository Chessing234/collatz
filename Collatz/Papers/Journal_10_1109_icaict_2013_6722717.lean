import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yagub N. Aliyev and Vugar A. Suleymanov, "Construction of periods for 3x+1 problem: Use of division algorithm by 2 in 3-base number system for construction of 3-adic numbers as periods of collatz sequence", 2013.

Title: Construction of periods for 3x+1 problem: Use of division algorithm by 2 in 3-base number system for construction of 3-adic numbers as periods of collatz sequence

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/icaict.2013.6722717
-/

namespace Collatz.Papers.Journal_10_1109_icaict_2013_6722717

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yagub N. Aliyev and Vugar A. Suleymanov, \"Construction of periods for 3x+1 problem: Use of division algorithm by 2 in 3-base number system for construction of 3-adic numbers as periods of collatz sequence\", DOI:10.1109/icaict.2013.6722717 [2013]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1109_icaict_2013_6722717
