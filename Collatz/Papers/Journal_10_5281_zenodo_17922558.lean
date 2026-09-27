import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "Natural Numbers and the Halting Problem: Rediscovering Structural Blind Spots in the Collatz Conjecture", 2025.

Title: Natural Numbers and the Halting Problem: Rediscovering Structural Blind Spots in the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Abstract Despite the surge of structural approaches in 2025—such as inverse Collatz tree constructions and classifications of stopping regions—the Collatz conjecture remains unresolved as a halting problem. The central difficulty lies not in arithmetic errors but in a structural asymmetry: natural numbers lack an initial value problem, which inevitably generates a halting problem over infinite domains. To overcome this, we introduce the structural requirement of one-to-one responsibility and apply arrow symmetrization, familiar in memory spaces between addresses and data, to enforce Start = Stop symmetry. This guarantees complete bijective closure across infinite sets and establishes a direc...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17922558
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17922558

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"Natural Numbers and the Halting Problem: Rediscovering Structural Blind Spots in the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.17922558 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17922558
