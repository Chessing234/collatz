import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Raouf Rajab, "The sequence of Collatz functions, exceptionality of the 3n+1 function and the notion of Collatz generalized Matrix", arXiv:2107.05629 [2021].

Title: The sequence of Collatz functions, exceptionality of the 3n+1 function and the notion of Collatz generalized Matrix

Abstract (truncated):
In this article, we define a very important sequence of functions, all the functions of this sequence present behaviors very close to that of the Collatz function. The study of such functions allows us to obtain very interesting results concerning the collatz conjecture and more precisely concerning the generalization of this problem, the nature of the Collatz function, on the statement of the Collatz conjecture we show that this conjecture can be stated for each function on a well-determined subset of Z and other interesting properties in relation to the behaviors of Collatz sequences are studied and proved in this article.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2107.05629
-/

namespace MathlibAttack.Papers.Arxiv2107_05629

open MathlibAttack.Papers

def citation : String := "Raouf Rajab, \"The sequence of Collatz functions, exceptionality of the 3n+1 function and the notion of Collatz generalized Matrix\", arXiv:2107.05629 [2021]."

/-- Recorded claim shell (generalization); paper theorem not proved.
Placeholder equals the Collatz conjecture proposition. -/
def mainStatement : Prop := CollatzConjecture

theorem step_one_eq : step 1 = 4 := step_one
theorem step_two_eq : step 2 = 1 := step_two

end MathlibAttack.Papers.Arxiv2107_05629
