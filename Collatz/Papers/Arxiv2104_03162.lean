import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Raouf Rajab, "The fundamental properties characterizing the structural behaviors of Collatz sequences", arXiv:2104.03162 [2021].

Title: The fundamental properties characterizing the structural behaviors of Collatz sequences

Abstract (from OpenAlex metadata, truncated):
This work represents an in-depth study of the structural behavior of the Collatz sequences. We consider a finite arithmetic progression with a common difference is 2 and the number of terms in the sequence is equal to 2^n . After, we consider a 2^n x(n+1) matrix ((n+1) columns and 2^n rows) such as the first column contains the terms of arithmetic progression and each row of the matrix represent a finite Collatz sequence. Then, each element of the matrix will be replaced by 0 or 1 according to the following rule: the even integer is replaced by 0 and the odd integer is replaced by 1. We obtained a table contains all binary permutation with repetition this property is called the property of structural complementarily. Based on these tables, we can determine any other fundamentals properties characterizing the behavior of Collatz sequences. Thus, we can distinguish two other important properties such as the property of structural cyclical behavior characterized by a structural periodicit

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2104.03162
-/

namespace Collatz.Papers.Arxiv2104_03162

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Raouf Rajab, \"The fundamental properties characterizing the structural behaviors of Collatz sequences\", arXiv:2104.03162 [2021]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2104_03162
