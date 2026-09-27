import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Raouf Rajab, "General formulas of global characteristic coefficients of Collatz function", arXiv:2105.03415 [2021].

Title: General formulas of global characteristic coefficients of Collatz function

Abstract (from OpenAlex metadata, truncated):
The purpose of this paper is to show three general formulas of three global characteristic coefficients of Collatz function. The Collatz function is defined by the following operation on an arbitrary positive integer if N is odd multiply it by 3 and add 1 then the sum obtained is divided by 2, if N is even divide it by 2. Based on the principle, we define the n-order function denoted by T^n such as the different expressions of that function are results of applying Collatz function n times to a natural numbers which are expressed in well determined forms. Based on these expressions, we can characterize that n-order function by three global characteristic coefficients. In the first, we define these three global coefficients. Secondly, we show that each global characteristic coefficient has a general expression as a function of n.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2105.03415
-/

namespace Collatz.Papers.Arxiv2105_03415

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Raouf Rajab, \"General formulas of global characteristic coefficients of Collatz function\", arXiv:2105.03415 [2021]."

/-- Recorded main claim shell (structural); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2105_03415
