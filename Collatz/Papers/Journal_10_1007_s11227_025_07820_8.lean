import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Frinkle, Karl et al., "Computing streaks of consecutive numbers with the same Collatz height", 2025.

Title: Computing streaks of consecutive numbers with the same Collatz height

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1007/s11227-025-07820-8
-/

namespace Collatz.Papers.Journal_10_1007_s11227_025_07820_8

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Frinkle, Karl et al., \"Computing streaks of consecutive numbers with the same Collatz height\", The Journal of Supercomputing, DOI:10.1007/s11227-025-07820-8 [2025]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1007_s11227_025_07820_8
