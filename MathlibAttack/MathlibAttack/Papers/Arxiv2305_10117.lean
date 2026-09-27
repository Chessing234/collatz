import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Giulio Masetti, "A new conjecture equivalent to Collatz conjecture", arXiv:2305.10117 [2023].

Title: A new conjecture equivalent to Collatz conjecture

Abstract (truncated):
In this paper a new conjecture equivalent to Collatz conjecture is presented. In particural, showing that (all) the solution(s) of newly introduced iterative functional equation(s) have a given property is equivalent to prove Collatz conjecture.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2305.10117
-/

namespace MathlibAttack.Papers.Arxiv2305_10117

open MathlibAttack.Papers

def citation : String := "Giulio Masetti, \"A new conjecture equivalent to Collatz conjecture\", arXiv:2305.10117 [2023]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2305_10117
