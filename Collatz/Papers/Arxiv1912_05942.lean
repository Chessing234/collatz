import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Venkatesulu Mandadi and Devi Paramwswari, "Verification of Collatz Conjecture: An algorithmic approach based on binary representation of integers", arXiv:1912.05942 [2019].

Title: Verification of Collatz Conjecture: An algorithmic approach based on binary representation of integers

Abstract (from OpenAlex metadata, truncated):
Lothar Collatz had proposed in 1937 a conjecture in number theory called Collatz conjecture. Till today there is no evidence of proving or disproving the conjecture. In this paper, we propose an algorithmic approach for verification of the Collatz conjecture based on bit representation of integers. The scheme neither encounters any cycles in the so called Collatz sequence and nor the sequence grows indefinitely. Experimental results show that the Collatz sequence starting at the given integer , oscillates for finite number of times, never exceeds 1.7 times (scaling factor) size of the starting integer and finally reaches the value 1. The experimental results show strong evidence that conjecture is correct and paves a way for theoretical proof.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1912.05942
-/

namespace Collatz.Papers.Arxiv1912_05942

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Venkatesulu Mandadi and Devi Paramwswari, \"Verification of Collatz Conjecture: An algorithmic approach based on binary representation of integers\", arXiv:1912.05942 [2019]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv1912_05942
