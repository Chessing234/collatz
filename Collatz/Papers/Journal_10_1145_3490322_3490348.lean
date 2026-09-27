import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hongyuan Ye and Lei Zhang, "Reconstruction and Trial Verification of the Collatz Conjecture Based On Big Data", 2021.

Title: Reconstruction and Trial Verification of the Collatz Conjecture Based On Big Data

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1145/3490322.3490348
-/

namespace Collatz.Papers.Journal_10_1145_3490322_3490348

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hongyuan Ye and Lei Zhang, \"Reconstruction and Trial Verification of the Collatz Conjecture Based On Big Data\", 2021 4th International Conference on Big Data Technologies, DOI:10.1145/3490322.3490348 [2021]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1145_3490322_3490348
