import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Régent, Xavier J., "Structural Ascension and the Collatz Conjecture: A Historical Nitescence-Based Metamathematical Study", 2026.

Title: Structural Ascension and the Collatz Conjecture: A Historical Nitescence-Based Metamathematical Study

Abstract (from harvested metadata, truncated):
This document represents the culmination of an initial line of research devoted to the Collatz Conjecture within the framework of the Nitescence Theorem. The purpose of this approach was not yet to establish the convergence of Collatz trajectories directly, but to study the problem at a metamathematical level: to identify the formal framework in which the obstruction appears, characterize the resources required for its resolution, and examine the possibility of structural ascension toward a more relevant framework. Several successive versions progressively corrected and clarified this approach. The earliest formulations were overly ambitious in their interpretation of the scope of structural...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21331029
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21331029

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Régent, Xavier J., \"Structural Ascension and the Collatz Conjecture: A Historical Nitescence-Based Metamathematical Study\", Zenodo/CERN, DOI:10.5281/zenodo.21331029 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21331029
