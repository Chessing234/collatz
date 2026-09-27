import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Руслан Шарипов, "Evolution patterns in Collatz problem", arXiv:2202.04441 [2022].

Title: Evolution patterns in Collatz problem

Abstract (truncated):
The concept of evolution patterns is introduced for Collatz sequences and it is shown that any finite evolution pattern is implemented in some particular Collatz sequence.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2202.04441
-/

namespace MathlibAttack.Papers.Arxiv2202_04441

open MathlibAttack.Papers

def citation : String := "\u0420\u0443\u0441\u043b\u0430\u043d \u0428\u0430\u0440\u0438\u043f\u043e\u0432, \"Evolution patterns in Collatz problem\", arXiv:2202.04441 [2022]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2202_04441
