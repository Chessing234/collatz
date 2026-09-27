import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hassan Rezai Soleymanpour, "A Proof of Collatz Conjecture Based on a New Tree Topology", arXiv:2104.12135 [2021].

Title: A Proof of Collatz Conjecture Based on a New Tree Topology

Abstract (from OpenAlex metadata, truncated):
Consider a finite positive integer. If it is even, divide it by 2, and if it is odd, multiply it by 3 and add 1. This will give you a new integer. Following the procedure for the new integer, you will receive another integer. Repeat the steps, and after a few repetitions, you will finally reach 1. Collatz conjecture states that the final integer in the mentioned process will always be 1, no matter what integer it starts with. Although the procedure of the conjecture is easy to describe, its correctness has not yet been confirmed. This article proves the conjecture by introducing a tree topology of it. Given the proposed tree, we can prove that all integers are uniquely distributed on the tree, and there is no cycle other than 1-2-1. We also see how every trajectory ends in 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2104.12135
-/

namespace Collatz.Papers.Arxiv2104_12135

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hassan Rezai Soleymanpour, \"A Proof of Collatz Conjecture Based on a New Tree Topology\", arXiv:2104.12135 [2021]."

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


end Collatz.Papers.Arxiv2104_12135
