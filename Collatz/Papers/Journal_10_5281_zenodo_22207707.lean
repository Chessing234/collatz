import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jean Patrick Yann Orphée Brou, "Résolution structurelle de la conjoncture de collatz par classification multiplicative des entiers", 2026.

Title: Résolution structurelle de la conjoncture de collatz par classification multiplicative des entiers

Abstract (from harvested metadata, truncated):
The Collatz conjecture, formulated in 1937, states that by iteratively applying the rule n \to n/2 if n is even, and n \to 3n+1 if n is odd, every positive integer eventually reaches the trivial cycle 4 \to 2 \to 1 . In this paper, I present a complete proof of this conjecture. My method relies on an original classification of integers based on their prime factorization. I define a projection function f that skips directly from one odd number to the next, and I introduce a step counter t to track the evolution of the sequence. By partitioning odd numbers into four groups (A, B, C, D), I prove two fundamental lemmas: (1) every composite odd number projects, after a finite number of steps, ont...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22207707
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22207707

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jean Patrick Yann Orphée Brou, \"Résolution structurelle de la conjoncture de collatz par classification multiplicative des entiers\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22207707 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22207707
