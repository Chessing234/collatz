import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nikolai Arkhipov, "«Complete Proof of the Collatz Conjecture and the Arche Principle»", 2026.

Title: «Complete Proof of the Collatz Conjecture and the Arche Principle»

Abstract (from harvested metadata, truncated):
This work presents a complete proof of the Collatz conjecture (3n+1 problem) based on "proper quadruples" and the governing equation 3x² − 4x − 4 = 0. A general theory for 3n+d systems is built. Global convergence and the uniqueness of the cycle 4→2→1 are rigorously proved. The Arche Principle is formulated, linking the proof to the architecture of the binary system.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21095395
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21095395

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nikolai Arkhipov, \"«Complete Proof of the Collatz Conjecture and the Arche Principle»\", DOI:10.5281/zenodo.21095395 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21095395
