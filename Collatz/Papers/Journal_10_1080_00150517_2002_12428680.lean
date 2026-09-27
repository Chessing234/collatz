import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Paul J. Andaloro, "The 3 x + 1 Problem and Directed Graphs", 2002.

Title: The 3 x + 1 Problem and Directed Graphs

Abstract (from harvested metadata, truncated):
Let Z denote the set of integers, P denote the positive integers, and N denote the nonnegative integers. Define the Collatz mapping T: 2N +1-> 2N +1 by T(x) = (3x +1) / 2 J, where V \\3x +1 but 2- / ' +1 |3x + l. The famous 3x + l Conjecture, or Collatz Problem, asserts that, for any x e 2N + 1, there exists k eN satisfying T k (x) = 1, where T k

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1080/00150517.2002.12428680
-/

namespace Collatz.Papers.Journal_10_1080_00150517_2002_12428680

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Paul J. Andaloro, \"The 3 x + 1 Problem and Directed Graphs\", The Fibonacci Quarterly, DOI:10.1080/00150517.2002.12428680 [2002]."

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

end Collatz.Papers.Journal_10_1080_00150517_2002_12428680
