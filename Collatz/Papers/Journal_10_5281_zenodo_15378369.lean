import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for yu, gande, "Updated Version of the Complete Proof of the Collatz Conjecture", 2025.

Title: Updated Version of the Complete Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Abstract: This paper completely proves the Collatz conjecture. First, we analyze that the positive integers that converge to 1 have some identical fixed paths, and regard the fixed paths and the "4→2→1" cycle as a whole. Then, we exclude the existence of non-"4→2→1" cycles and the existence of positive integers that diverge to infinity, respectively, thus proving that all positive integers can converge to 1, that is, the Collatz conjecture holds. Finally, we propose a general method to generalize the Collatz iteration rule to other rules. Keywords: Collatz conjecture; 3n+1 conjecture; hailstone conjecture; even-odd-unity conjecture; 421 conjecture; Kakutani conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15378369
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15378369

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "yu, gande, \"Updated Version of the Complete Proof of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.15378369 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_15378369
