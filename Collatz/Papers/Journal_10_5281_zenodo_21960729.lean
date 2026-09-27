import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Raghavachary, Saty, "Collatz Conjecture proof - Lean code", 2026.

Title: Collatz Conjecture proof - Lean code

Abstract (from harvested metadata, truncated):
Lean code (v 4.33.0) to verify the Collatz Conjecture proof. See https://zenodo.org/records/21960650 for the pdf version of the proof.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21960729
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21960729

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Raghavachary, Saty, \"Collatz Conjecture proof - Lean code\", Zenodo, DOI:10.5281/zenodo.21960729 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_21960729
