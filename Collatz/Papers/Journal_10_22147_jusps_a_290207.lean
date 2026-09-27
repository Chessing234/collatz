import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for W. B. Vasantha Kandasamy et al., "The 3n p Conjecture: A Generalization of Collatz Conjecture", 2017.

Title: The 3n p Conjecture: A Generalization of Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture is an open conjecture in mathematics named so after Lothar Collatz who proposed it in 1937. It is also known as 3n 1 conjecture, the Ulam conjecture (after Stanislaw Ulam), Kakutanis problem (after Shizuo Kakutani) and so on. Several various generalization of the Collatz conjecture has been carried. In this paper a new generalization of the Collatz conjecture called as the 3n  p conjecture; where p is a prime is proposed. It functions on 3n  p and 3n  p , and for any starting number n , its sequence eventually enters a finite cycle and there are finitely many such cycles. The 3n 1 conjecture, is a special case of the 3n  p conjecture when p is 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.22147/jusps-a/290207
-/

namespace Collatz.Papers.Journal_10_22147_jusps_a_290207

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "W. B. Vasantha Kandasamy et al., \"The 3n p Conjecture: A Generalization of Collatz Conjecture\", Journal of Ultra Scientist of Physical Sciences Section A, DOI:10.22147/jusps-a/290207 [2017]."

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

end Collatz.Papers.Journal_10_22147_jusps_a_290207
