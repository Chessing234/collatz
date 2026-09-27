import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Peter Hellekalek, "On the 3x+1 conjecture", arXiv:1605.02634 [2016].

Title: On the 3x+1 conjecture

Abstract (from OpenAlex metadata, truncated):
In this paper, we discuss the well known 3x+1 conjecture in form of the accelerated Collatz function T defined on the positive odd integers. We present a sequence of quotient spaces and an invertible map that are intrinsically related to the behavior of T. This approach allows to express the 3x+1 conjecture in form of equivalent problems, which might be more accessible than the original conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1605.02634
-/

namespace Collatz.Papers.Arxiv1605_02634

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Peter Hellekalek, \"On the 3x+1 conjecture\", arXiv:1605.02634 [2016]."

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

end Collatz.Papers.Arxiv1605_02634
