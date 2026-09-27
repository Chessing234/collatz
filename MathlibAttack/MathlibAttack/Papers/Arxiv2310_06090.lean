import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Kerry M. Soileau, "A Necessary Condition on the Collatz Conjecture", arXiv:2310.06090 [2023].

Title: A Necessary Condition on the Collatz Conjecture

Abstract (truncated):
The Collatz conjecture implies that an iterated function sequence under a certain linear operator, beginning with a certain complex valued function, must converge to a certain complex function.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2310.06090
-/

namespace MathlibAttack.Papers.Arxiv2310_06090

open MathlibAttack.Papers

def citation : String := "Kerry M. Soileau, \"A Necessary Condition on the Collatz Conjecture\", arXiv:2310.06090 [2023]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2310_06090
