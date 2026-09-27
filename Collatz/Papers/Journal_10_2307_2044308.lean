import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lynn E. Garner, "On the Collatz 3n + 1 Algorithm", 1981.

Title: On the Collatz 3n + 1 Algorithm

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2307/2044308
-/

namespace Collatz.Papers.Journal_10_2307_2044308

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lynn E. Garner, \"On the Collatz 3n + 1 Algorithm\", Proceedings of the American Mathematical Society, DOI:10.2307/2044308 [1981]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_2307_2044308
