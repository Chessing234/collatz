import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ancar, Cebrail, "Character-Based Representation and Analysis of the Collatz Problem", 2025.

Title: Character-Based Representation and Analysis of the Collatz Problem

Abstract (from harvested metadata, truncated):
Title of the Work: Character-Based Representation and Analysis of the Collatz Problem This work proposes a new symbolic framework based on the classification of positive integers around the 6n modulation. Numbers are labeled with the characters [0], [+1], [2], and [c] , and arithmetic operations are redefined with consistent rules over the u($6n-1$) and d(6n+1) bands Collatz Problem: Using this framework, the flow of the Collatz algorithm is analyzed in a layered manner at the character level4. By relating the "Infinity Scale" and "Guide-Metric" dynamics 5, the position of b=4a+1 type metric transitions within the [c] \to d \to u \to [c] character cycle is formally presented. The study suggests that all numbers are connected by generating equal and infinite quantities of character traits,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17721717
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17721717

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ancar, Cebrail, \"Character-Based Representation and Analysis of the Collatz Problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.17721717 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17721717
