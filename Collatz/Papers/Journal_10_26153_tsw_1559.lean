import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Matthew Alexander Denend and 0000-0001-7002-7426, "Challenging variants of the Collatz Conjecture", 2018.

Title: Challenging variants of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz Conjecture (also known as the 3N + 1 problem) is simple to explain, yet proving that all positive integers following the Collatz Mapping must converge to 1 has eluded mathematicians for over half a century. Aaronson and Heule are exploring solving the Collatz Conjecture using an approach involving string rewrite systems: Aaronson transformed the Conjecture into a string rewrite system and Heule has been applying parallel SAT solvers on instances of this system. Similar approaches have been applied successfully to other mathematical problems. We started looking into simpler variants of the conjecture. This thesis defines some of these variants and investigates easily provable as well as very hard variants. We study the hardness of unsolved variants by computing the number of...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.26153/tsw/1559
-/

namespace Collatz.Papers.Journal_10_26153_tsw_1559

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Matthew Alexander Denend and 0000-0001-7002-7426, \"Challenging variants of the Collatz Conjecture\", DOI:10.26153/tsw/1559 [2018]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_26153_tsw_1559
