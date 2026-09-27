import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wei Ren, "Reduced Collatz Dynamics is Periodical and the Period Equals 2 to the Power of the Count of x/2", arXiv:2304.10491 [2023].

Title: Reduced Collatz Dynamics is Periodical and the Period Equals 2 to the Power of the Count of x/2

Abstract (from OpenAlex metadata, truncated):
In this paper, we prove that reduced dynamics on Collatz conjecture is periodical, and its period equals 2 to the power of the count of x/2 computation in the reduced dynamics. More specifically, if there exists reduced dynamics of x (that is, start from an integer x and the computation will go to an integer less than x), then there must also exist reduced dynamics of x+P (that is, if starting from an integer x+P, then computation will go to an integer less than x+P), where P equals 2 to the power of L, and L is the total count of x/2 computations (i.e., computational times) in the reduced dynamics of x (note that, equivalently, L is also the length of the reduced dynamics of x). Therefore, the power (or output) of this period property, which is discovered and proved in this paper, is - the study of the existence of reduced dynamics of x will result in the existence of reduced dynamics of x+P (and iteratively x+n*P, n is a positive integer). Hence, only partition of integers needs to b

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2304.10491
-/

namespace Collatz.Papers.Arxiv2304_10491

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wei Ren, \"Reduced Collatz Dynamics is Periodical and the Period Equals 2 to the Power of the Count of x/2\", arXiv:2304.10491 [2023]."

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


end Collatz.Papers.Arxiv2304_10491
