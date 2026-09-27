import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Raouf Rajab, "ON A GENERALIZED COLLATZ PROBLEM : CONJECTURES AND THE UNIQUENESS OF THE TRIVIAL CYCLE (1, 2)", 2026.

Title: ON A GENERALIZED COLLATZ PROBLEM : CONJECTURES AND THE UNIQUENESS OF THE TRIVIAL CYCLE (1, 2)

Abstract (from harvested metadata, truncated):
The Collatz conjecture remains one of the most famous open problems in number theory. This work introduces an unexplored generalization of the classical Syracuse function. By expanding the traditional framework, we formulate a set of fascinating new conjectures. Surprisingly, these theoretical extensions preserve the fundamental structure of the original problem. The numerical and theoretical analyses conducted show that the set of these generalized trajectories is consistent with the uniqueness of the trivial cycle (1, 2). This work thus opens a new avenue for understanding the robustness of the Collatz conjecture through the lens of its variants.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21071359
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21071359

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Raouf Rajab, \"ON A GENERALIZED COLLATZ PROBLEM : CONJECTURES AND THE UNIQUENESS OF THE TRIVIAL CYCLE (1, 2)\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21071359 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21071359
