import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Amirian, Robert and Amirian, Alan, "A GENERALIZATION OF 3x+1 PROBLEM TO 3x+4y+1", 2026.

Title: A GENERALIZATION OF 3x+1 PROBLEM TO 3x+4y+1

Abstract (from harvested metadata, truncated):
This paper seeks to generalize the infamous Collatz Conjecture which has haunted mathematicians for the last 100 years. Our research shows that there are infinite variations to the Collatz Conjecture, or the 3x+1 problem, in the form of 3x+4y+1 for all integer values of y, positive and negative. The proposed Generalized Collatz Conjecture (GCC), or 3x+4y+1 problem, generalizes the Collatz Conjecture and shows that all GCC variations finish their cycle at the minimum value of 1-2y, rather than just 1 as the Collatz Conjecture states. We believe this generalization opens the door to solving the Generalized Collatz Conjecture, and thus, Collatz Conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.6993335
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_6993335

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Amirian, Robert and Amirian, Alan, \"A GENERALIZATION OF 3x+1 PROBLEM TO 3x+4y+1\", SSRN Electronic Journal, DOI:10.2139/ssrn.6993335 [2026]."

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

end Collatz.Papers.Journal_10_2139_ssrn_6993335
