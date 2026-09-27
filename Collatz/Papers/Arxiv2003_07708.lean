import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Danial Karami, "A new method to prove the Collatz conjecture", arXiv:2003.07708 [2020].

Title: A new method to prove the Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture is a famous math problem that was introduced by Lothar Collatz in 1937, and nobody has yet succeeded in proving or disproving it. In this article, I will analyze this problem with a new approach and I will discuss my important findings that are helpful in getting closer to the proof of this unsolved problem in mathematics.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2003.07708
-/

namespace Collatz.Papers.Arxiv2003_07708

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Danial Karami, \"A new method to prove the Collatz conjecture\", arXiv:2003.07708 [2020]."

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

end Collatz.Papers.Arxiv2003_07708
