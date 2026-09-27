import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Beatty, Travis, "Proving the Collatz Conjecture through Structural Dependencies", 2025.

Title: Proving the Collatz Conjecture through Structural Dependencies

Abstract (from harvested metadata, truncated):
This preprint presents an approach to the Collatz Conjecture that leverages fundamental properties of natural numbers and modulo analysis. We demonstrate that the structural dependencies between natural numbers create predetermined trajectories for all orbits under the Collatz operations. By analyzing these dependencies, we show that all orbits converge to 1, regardless of the initial number's magnitude. Our findings provide an alternate method for measuring the monotonic descent of orbits using the 3n+1 operation as a counting measurement. This work offers new insights into the Collatz Conjecture and contributes to the ongoing efforts to understand this famous unsolved problem in number the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.15106188
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_15106188

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Beatty, Travis, \"Proving the Collatz Conjecture through Structural Dependencies\", Zenodo, DOI:10.5281/zenodo.15106188 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_15106188
