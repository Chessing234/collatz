import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ke Li, "The Introduction of the Rule of 3x +1 Problem", arXiv:2109.0156 [2021].

Title: The Introduction of the Rule of 3x +1 Problem

Abstract (from OpenAlex metadata, truncated):
This article introduces a change rule of 3x+1 problem (Collatz conjecture), it’s named LiKe’s rule: For any positive integer, change by the Collatz conjecture, it will change to an odd number; the odd numbers will must change to a number of LiKe’s second sequence {3n-1∣n∈Z+}; then this 3n-1 will change to a smaller 3n-1 and gradually decrease to 8(that is 3^2-1) then back to 1 in theend.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2109.0156
-/

namespace Collatz.Papers.Arxiv2109_0156

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ke Li, \"The Introduction of the Rule of 3x +1 Problem\", arXiv:2109.0156 [2021]."

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

end Collatz.Papers.Arxiv2109_0156
