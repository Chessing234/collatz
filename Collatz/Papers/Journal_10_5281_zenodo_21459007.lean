import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Chairunnur Fajar, Muhammad Irvan, "[Final] Dynamics of the Collatz Conjecture & the Ivan Law of Crowding Formulation", 2026.

Title: [Final] Dynamics of the Collatz Conjecture & the Ivan Law of Crowding Formulation

Abstract (from harvested metadata, truncated):
This paper establishes a comprehensive analytical and empirical framework to investigatethe behavioral dynamics of the Collatz Conjecture through the lens of the newly formulatedIvan Law of Crowding. By incorporating algorithmic orbit tracking and deterministic spatial compression principles, we evaluate how numerical trajectories navigate modular spatialboundaries. The investigation focuses on the mechanisms that prevent structural divergenceand mathematically exclude stable alternative attractors. Our real-time computational execution definitively proves that all numerical sequences under the tested domain undergo anaggressive entropy collapse, validating that the systemic crowding effect...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21459007
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21459007

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Chairunnur Fajar, Muhammad Irvan, \"[Final] Dynamics of the Collatz Conjecture & the Ivan Law of Crowding Formulation\", Zenodo, DOI:10.5281/zenodo.21459007 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21459007
