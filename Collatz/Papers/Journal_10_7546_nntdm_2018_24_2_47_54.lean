import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Abdullah Arslan, "Methods for constructing Collatz numbers", 2018.

Title: Methods for constructing Collatz numbers

Abstract (from harvested metadata, truncated):
The Collatz conjecture is among the unsolved problems in mathematics.It says that if we take any natural number x; divide it by two if x is even, and multiply it by 3 and add 1 if x is odd; and repeat this rule on the resulting numbers, eventually we obtain 1.For a given positive integer x, we say that x is a Collatz number if the claim of the conjecture is true for x.Computer verification reveals a large range of Collatz numbers.We develop methods by which we construct sets of Collatz numbers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.7546/nntdm.2018.24.2.47-54
-/

namespace Collatz.Papers.Journal_10_7546_nntdm_2018_24_2_47_54

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Abdullah Arslan, \"Methods for constructing Collatz numbers\", Notes on Number Theory and Discrete Mathematics, DOI:10.7546/nntdm.2018.24.2.47-54 [2018]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_7546_nntdm_2018_24_2_47_54
