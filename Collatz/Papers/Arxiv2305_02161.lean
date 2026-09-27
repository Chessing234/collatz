import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for HUANG Qingxue, "A Proof of Collatz Conjecture", arXiv:2305.02161 [2023].

Title: A Proof of Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
In 1937,German mathematician L.Collatz proposed the following conjeture:for any positive integer,if it is even,divide it by 2,if it is odd,multiply it by 3 and add 1 to get an even number.Continuing with the above rule, the final result will be 1.This paper gives a proof of this conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2305.02161
-/

namespace Collatz.Papers.Arxiv2305_02161

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "HUANG Qingxue, \"A Proof of Collatz Conjecture\", arXiv:2305.02161 [2023]."

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

end Collatz.Papers.Arxiv2305_02161
