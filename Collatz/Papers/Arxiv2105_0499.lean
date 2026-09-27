import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Li Jiang, "3x + 1 Problem: Iterative Operations Neither Cause Loops nor Diverge to Infinity", arXiv:2105.0499 [2022].

Title: 3x + 1 Problem: Iterative Operations Neither Cause Loops nor Diverge to Infinity

Abstract (from OpenAlex metadata, truncated):
The 3x+1 problem is a problem of continuous iteration for integers. According to the basic theorem of arithmetic and the way of iteration, we derive a general formula for continuous iteration for odd integers. Through this formula, we can construct a loop iteration equation and obtain the result of the equation: the equation has only one positive integer solution. In addition, this general formula can be converted into a linear indeterminate equation. The process of solving this equation shows that the relationship between the iteration result and the odd number being iterated is linear. Extending this result to all positive even numbers, we get the answer to the 3x + 1 question.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2105.0499
-/

namespace Collatz.Papers.Arxiv2105_0499

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Li Jiang, \"3x + 1 Problem: Iterative Operations Neither Cause Loops nor Diverge to Infinity\", arXiv:2105.0499 [2022]."

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

end Collatz.Papers.Arxiv2105_0499
