import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jha, Rohit Kumar, "A Computer-Assisted Proof of the Collatz Conjecture", 2026.

Title: A Computer-Assisted Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19543317
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19543317

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jha, Rohit Kumar, \"A Computer-Assisted Proof of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.19543317 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_19543317
