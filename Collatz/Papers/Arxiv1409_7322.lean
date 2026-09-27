import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michel Pascal, "Simulation of the Collatz 3x+1 function by Turing machines", arXiv:1409.7322 [2014].

Title: Simulation of the Collatz 3x+1 function by Turing machines

Abstract (from OpenAlex metadata, truncated):
We give new Turing machines that simulate the iteration of the Collatz 3x+1 function. First, a never halting Turing machine with 3 states and 4 symbols, improving the known 3x5 and 4x4 Turing machines. Second, Turing machines that halt on the final loop, in the classes 3x10, 4x6, 5x4, and 13x2.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1409.7322
-/

namespace Collatz.Papers.Arxiv1409_7322

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michel Pascal, \"Simulation of the Collatz 3x+1 function by Turing machines\", arXiv:1409.7322 [2014]."

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

end Collatz.Papers.Arxiv1409_7322
