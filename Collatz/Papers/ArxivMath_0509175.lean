import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lagarias, Jeffrey C., Soundararajan, K., "Benford's law for the $3x+1$ function", arXiv:math/0509175 [2005].

Title: Benford's law for the $3x+1$ function

Abstract (from arXiv metadata, truncated):
We show that for most choices of an initial seed $x_0$, the sequence of the first $N$ iterates of $x_0$ under the $3x+1$ map approximately satisfies Benford's law.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/math/0509175
-/

namespace Collatz.Papers.ArxivMath_0509175

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lagarias, Jeffrey C. and Soundararajan, K., \"Benford's law for the $3x+1$ function\", arXiv:math/0509175 [2005]."

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

end Collatz.Papers.ArxivMath_0509175
