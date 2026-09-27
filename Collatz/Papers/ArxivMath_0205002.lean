import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Krasikov, Ilia, Lagarias, Jeffrey C., "Bounds for the 3x+1 Problem using Difference Inequalities", arXiv:math/0205002 [2002].

Title: Bounds for the 3x+1 Problem using Difference Inequalities

Abstract (from arXiv metadata, truncated):
We study difference inequality systems for the 3x+1 problem introduced by the first author in 1989. These systemes can be used to give lower bounds for the number of integers below x that contain 1 in their forward orbit under the 3x+1 map. Previous methods gave away some information in these inequalities. We give an improvement which apparantly extracts full information from the inequalities. By computer aided proof we show that at least x^{0.84} of the integers below x contain 1 in their forward orbit under the 3x+1 map.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/math/0205002
-/

namespace Collatz.Papers.ArxivMath_0205002

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Krasikov, Ilia and Lagarias, Jeffrey C., \"Bounds for the 3x+1 Problem using Difference Inequalities\", arXiv:math/0205002 [2002]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.ArxivMath_0205002
