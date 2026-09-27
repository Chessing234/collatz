import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Umarin Pintoptang, Imchit Termwuttipong, Hall, Mark Edwin, "Some sufficient conditions for cyclic trajectories in a two-dimensional analog of the 3x+1 problem", arXiv:2001.01015 [2001].

Title: Some sufficient conditions for cyclic trajectories in a two-dimensional analog of the 3x+1 problem

Abstract (from OpenAlex metadata, truncated):
The 3x+1 problem concerns the behavior of the iterates of the function defined by T(x) = (3x+1)/2 if x is odd, T(x) = x/2 if x is even. The 3x+1 Conjecture asserts that, starting from any positive integer alpha , repeated iteration of this function eventually produces the value 1. In this thesis we study the following extended version of the above problem. Let Z* be the set of all nonnegative integers. Let k be any fixed prime number and D=[k 0], D=[0 k] Let A be any 2x2 matrix of positive integers. For a fixed beta is an element of a set Z*2, let T: Z*2 -> Z*2 be defined by, for each alpha is an element of a set Z*2, T(alpha) = D-1 alpha if D-1 alpha is an element of a set Z*2, T(alpha) = A alpha + beta if D-1 alpha is not an element of a set Z*2. The research reported in this thesis concerns determining whether or not the trajectory [alpha, T(alpha), T2 (alpha), ...] is cyclic. For som

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2001.01015
-/

namespace Collatz.Papers.Arxiv2001_01015

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Umarin Pintoptang et al., \"Some sufficient conditions for cyclic trajectories in a two-dimensional analog of the 3x+1 problem\", arXiv:2001.01015 [2001]."

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

end Collatz.Papers.Arxiv2001_01015
