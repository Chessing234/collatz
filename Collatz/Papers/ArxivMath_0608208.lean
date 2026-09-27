import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lagarias, Jeffrey C., "The 3x+1 Problem: An Annotated Bibliography, II (2000-2009)", arXiv:math/0608208 [2006].

Title: The 3x+1 Problem: An Annotated Bibliography, II (2000-2009)

Abstract (from arXiv metadata, truncated):
The 3x+1 problem concerns iteration of the map T(n) =(3n+1)/2 if n odd; n/2 if n even. The 3x +1 Conjecture asserts that for every positive integer n>1 the forward orbit of n includes the integer 1. This paper is an annotated bibliography of work done on the 3x+1 problem published from 2000 through 2009, plus some later papers that were preprints by 2009. This is a sequel to an annotated bibliography on the 3x+1 problem covering 1963-1999.
  At present the 3x+1 Conjecture remains unsolved.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/math/0608208
-/

namespace Collatz.Papers.ArxivMath_0608208

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lagarias, Jeffrey C., \"The 3x+1 Problem: An Annotated Bibliography, II (2000-2009)\", arXiv:math/0608208 [2006]."

/-- Recorded main claim shell (logic); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.ArxivMath_0608208
