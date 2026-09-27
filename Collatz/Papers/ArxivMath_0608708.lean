import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Liang, Wang, "Collatz's "3x+1" problem and iterative maps on interval", 2006.

Title: Collatz's "3x+1" problem and iterative maps on interval

Abstract (from harvested metadata, truncated):
In this paper, we convert Collatz map into a simple conjugate iterative maps defined in [0,1]. Such maps are more familiar to us and easier to deal with. Some new features of this map are observed by this method. An interesting heuristic proof is also presented. This research may provide a new venture to crack the "3x+1" problem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/math/0608708
-/

namespace Collatz.Papers.ArxivMath_0608708

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Liang, Wang, \"Collatz's \"3x+1\" problem and iterative maps on interval\", arXiv:math/0608708 [2006]."

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

end Collatz.Papers.ArxivMath_0608708
