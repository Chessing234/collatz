import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jeffrey Alexander Webb, "Collatz Descent Certificate — Verified Combined Result", 2026.

Title: Collatz Descent Certificate — Verified Combined Result

Abstract (from harvested metadata, truncated):
Purpose This document records the verified combination of certificates for the Collatz Conjecture

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22699284
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22699284

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jeffrey Alexander Webb, \"Collatz Descent Certificate — Verified Combined Result\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22699284 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_22699284
