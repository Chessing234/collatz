import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yuyin Yu and Dingyi Pei, "On the Glide of 3x+1 Problem", arXiv:1710.01525 [2017].

Title: On the Glide of 3x+1 Problem

Abstract (from OpenAlex metadata, truncated):
For any positive integer $n$, define an iterated function $$ f(n)=\left\{\begin{array}{ll} n/2, & \mbox{$n$ even,} \\ 3n+1, & \mbox{$n$ odd.} \end{array} \right. $$ Suppose $k$ (if it exists) is the lowest number such that $f^{k}(n)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1710.01525
-/

namespace Collatz.Papers.Arxiv1710_01525

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yuyin Yu and Dingyi Pei, \"On the Glide of 3x+1 Problem\", arXiv:1710.01525 [2017]."

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

end Collatz.Papers.Arxiv1710_01525
