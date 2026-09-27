import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for J. Stöckl, "Observations towards a proof of the Collatz conjecture using $2^{j}k+x$ number series", arXiv:2311.16765 [2023].

Title: Observations towards a proof of the Collatz conjecture using $2^{j}k+x$ number series

Abstract (from OpenAlex metadata, truncated):
The document tries to put focus on sequences with certain properties and periods leading to the first value smaller than the starting value in the Collatz problem. With the idea that, if all starting numbers lead ultimately to a smaller number, all full sequences lead to 1 with a finite stopping time, the problem could be reduced to more structured shorter sequences. It is shown that this sequences exist and follow consistent rules. Potential features of an infinite cycle, also leading to a smaller number, are also discussed. Further, an argument for only one possible closed cycle is given for the special sequence of alternating odd and even steps as well as arguments that infinite cycles must exist. Using the observation that periodic behavior is exists an additional argument is provided the probability of subsets which will end up at a number smaller the initial value possibly even of N will indeed end up at unity in the Collatz problem [1]. The work is to be seen as in progress and 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2311.16765
-/

namespace Collatz.Papers.Arxiv2311_16765

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "J. St\u00f6ckl, \"Observations towards a proof of the Collatz conjecture using $2^{j}k+x$ number series\", arXiv:2311.16765 [2023]."

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


end Collatz.Papers.Arxiv2311_16765
