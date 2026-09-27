import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Maxwell C. Siegel, "Functional Equations Associated to Collatz-Type Maps on Integer Rings of Algebraic Number Fields", arXiv:2111.07882 [2021].

Title: Functional Equations Associated to Collatz-Type Maps on Integer Rings of Algebraic Number Fields

Abstract (truncated):
In 1995, Meinardus & Berg presented a reformulation of the Collatz Conjecture in terms of a functional equation in a single complex variable over the open unit disk. This paper generalizes that method to deal with not only a large class of Collatz-type maps defined on the integers, but further generalizations thereof to Collatz-type maps on the rings of integers on an arbitrary algebraic number field.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2111.07882
-/

namespace MathlibAttack.Papers.Arxiv2111_07882

open MathlibAttack.Papers

def citation : String := "Maxwell C. Siegel, \"Functional Equations Associated to Collatz-Type Maps on Integer Rings of Algebraic Number Fields\", arXiv:2111.07882 [2021]."

/-- Recorded claim shell (generalization); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2111_07882
