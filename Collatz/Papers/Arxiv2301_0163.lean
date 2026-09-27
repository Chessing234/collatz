import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jishe Feng, "Solve the 3x+1 Problem by the Multiplication and Division of Binary Numbers", arXiv:2301.0163 [2023].

Title: Solve the 3x+1 Problem by the Multiplication and Division of Binary Numbers

Abstract (from OpenAlex metadata, truncated):
The 3x+1 problem asks the following: Suppose we start with a positive integer, and if it is odd then multiply it by 3 and add 1, and if it is even, divide it by 2. Then repeat this process as long as you can. Do you eventually reach the integer 1, no matter what you started with? Collatz conjecture (or 3n+1 problem) has been explored for about 85 years. In this paper, we convert an integer number from decimal to binary number, and convert the Collatz function to binary function, which is multiplication and division of two binary numbers. Finally the iternation of the Collatz function, eventually reach the integer 1, thus we solve the 3x+1 problem completely.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2301.0163
-/

namespace Collatz.Papers.Arxiv2301_0163

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jishe Feng, \"Solve the 3x+1 Problem by the Multiplication and Division of Binary Numbers\", arXiv:2301.0163 [2023]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2301_0163
