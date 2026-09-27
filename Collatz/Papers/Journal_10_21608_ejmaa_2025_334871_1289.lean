import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Samrat Dutta, "Chronological Verification of the Collatz Conjecture using Theoretically Proven Sieves", 2025.

Title: Chronological Verification of the Collatz Conjecture using Theoretically Proven Sieves

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.21608/ejmaa.2025.334871.1289
-/

namespace Collatz.Papers.Journal_10_21608_ejmaa_2025_334871_1289

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Samrat Dutta, \"Chronological Verification of the Collatz Conjecture using Theoretically Proven Sieves\", Electronic Journal of Mathematical Analysis and Applications, DOI:10.21608/ejmaa.2025.334871.1289 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_21608_ejmaa_2025_334871_1289
