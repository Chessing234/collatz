import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for David Barina, "Convergence verification of the Collatz problem", 2020.

Title: Convergence verification of the Collatz problem

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1007/s11227-020-03368-x
-/

namespace Collatz.Papers.Journal_10_1007_s11227_020_03368_x

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "David Barina, \"Convergence verification of the Collatz problem\", The Journal of Supercomputing, DOI:10.1007/s11227-020-03368-x [2020]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1007_s11227_020_03368_x
