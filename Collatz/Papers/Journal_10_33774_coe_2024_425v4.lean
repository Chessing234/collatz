import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sean Gilligan, "Absolute, mathematical proof that a hypothesised 2nd loop cannot exist in the Collatz Conjecture.", 2024.

Title: Absolute, mathematical proof that a hypothesised 2nd loop cannot exist in the Collatz Conjecture.

Abstract (from harvested metadata, truncated):
This proof shows that the necessary requirements for a 2nd loop in the Collatz cannot be met, ever. For a loop to exist all rises and falls in values between each value of x leaving and returning to itself must cancel to a net rise of 0. However I prove using simple algebra and elementary logic that if the lowest odd value of x has a net rise of 0 the 2nd lowest odd value of x cannot have a net rise of 0 so such a 2nd loop can never exist.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2024-425v4
-/

namespace Collatz.Papers.Journal_10_33774_coe_2024_425v4

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sean Gilligan, \"Absolute, mathematical proof that a hypothesised 2nd loop cannot exist in the Collatz Conjecture.\", DOI:10.33774/coe-2024-425v4 [2024]."

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

end Collatz.Papers.Journal_10_33774_coe_2024_425v4
