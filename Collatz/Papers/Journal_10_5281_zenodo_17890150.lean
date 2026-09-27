import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "Relativization of Natural Numbers and the Responsibility of Bijection: Establishing Structural Closure in the Collatz Conjecture", 2025.

Title: Relativization of Natural Numbers and the Responsibility of Bijection: Establishing Structural Closure in the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Abstract The Collatz conjecture remains unresolved as a halting problem, despite the surge of structural approaches in 2025 (such as inverse Collatz tree constructions and classifications of stopping regions) and extensive computational verification. The central challenge is the direct proof of halting for all positive integers, whose difficulty lies not in arithmetic errors but in a structural asymmetry inherent in the definition of natural numbers.This study emphasizes that the generative structure of natural numbers, fixed by Peano induction, is bound to an “absolute scheme biased toward the starting point.” Such bias omits the responsibility of defining bijection, thereby obstructing str...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17890150
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17890150

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"Relativization of Natural Numbers and the Responsibility of Bijection: Establishing Structural Closure in the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.17890150 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17890150
