import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Raouf Rajab, "The sequence of Collatz functions, exceptionality of the 3n+1 function and the notion of Collatz generalized Matrix", arXiv:2107.05629 [2021].

Title: The sequence of Collatz functions, exceptionality of the 3n+1 function and the notion of Collatz generalized Matrix

Abstract (from OpenAlex metadata, truncated):
In this article, we define a very important sequence of functions, all the functions of this sequence present behaviors very close to that of the Collatz function. The study of such functions allows us to obtain very interesting results concerning the collatz conjecture and more precisely concerning the generalization of this problem, the nature of the Collatz function, on the statement of the Collatz conjecture we show that this conjecture can be stated for each function on a well-determined subset of Z and other interesting properties in relation to the behaviors of Collatz sequences are studied and proved in this article.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2107.05629
-/

namespace Collatz.Papers.Arxiv2107_05629

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Raouf Rajab, \"The sequence of Collatz functions, exceptionality of the 3n+1 function and the notion of Collatz generalized Matrix\", arXiv:2107.05629 [2021]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2107_05629
