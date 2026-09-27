import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Raouf Rajab, "General formulas of global characteristic coefficients of Collatz function", arXiv:2105.03415 [2021].

Title: General formulas of global characteristic coefficients of Collatz function

Abstract (truncated):
The purpose of this paper is to show three general formulas of three global characteristic coefficients of Collatz function. The Collatz function is defined by the following operation on an arbitrary positive integer if N is odd multiply it by 3 and add 1 then the sum obtained is divided by 2, if N is even divide it by 2. Based on the principle, we define the n-order function denoted by T^n such as the different expressions of that function are results of applying Collatz function n times to a natural numbers which are expressed in well determined forms. Based on these expressions, we can characterize that n-order function by three global characteristic coefficients. In the first, we define these three global coefficients. Secondly, we show that each global characteristic coefficient has a general expression as a function of n.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2105.03415
-/

namespace MathlibAttack.Papers.Arxiv2105_03415

open MathlibAttack.Papers

def citation : String := "Raouf Rajab, \"General formulas of global characteristic coefficients of Collatz function\", arXiv:2105.03415 [2021]."

/-- Recorded claim shell (structural); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2105_03415
