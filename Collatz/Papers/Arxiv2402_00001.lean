import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jishe Feng, "Using binary string to prove the Collatz conjecture", arXiv:2402.00001 [2023].

Title: Using binary string to prove the Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
We introduce a full binary directed tree structure to represent the set of natural numbers, further categorizing them into three distinct subsets: pure odd numbers, pure even numbers, and mixed numbers. We adopt a binary string representation for natural numbers and elaborate on the composite methodology encompassing odd- and even-number functions. Our analysis focuses on examining the iteration sequence (or composition) of the Collatz function and its reduced variant, which serves as an analog to the inverse function, to scrutinize the validity of the Collatz conjecture. To substantiate this conjecture, we incorporate binary strings into an algebraic formula that captures the essence of the Collatz sequence. By this means, we transform discrete powers of 2 into continuous counterparts, ultimately culminating in the smallest natural number, 1. Consequently, the sequence generated through infinite iterations of the Collatz function emerges as an eventually periodic sequence, thereby val

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2402.00001
-/

namespace Collatz.Papers.Arxiv2402_00001

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jishe Feng, \"Using binary string to prove the Collatz conjecture\", arXiv:2402.00001 [2023]."

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


end Collatz.Papers.Arxiv2402_00001
