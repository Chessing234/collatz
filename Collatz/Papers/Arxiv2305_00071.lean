import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Masoud Allame, A. Hadi‐Vencheh, "Does the Collatz Sequence Eventually Reach 1 for All Positive Integer Initial Values?", arXiv:2305.00071 [2023].

Title: Does the Collatz Sequence Eventually Reach 1 for All Positive Integer Initial Values?

Abstract (from OpenAlex metadata, truncated):
This study focuses on one of the most famous open problems in mathematics, namely the Collatz conjecture. The Collatz conjecture or 3x + 1 Problem is perhaps today's most enigmatic unsolved mathematical problem. It is named after Lothar Collatz, who rst proposed it in 1937. It may be stated as as follow: Take any positive integer n. If n is even then divide it by 2, else do \triple plus one" and get 3n + 1. The conjecture is that this process will eventually reach the number 1, regardless of which positive integer is chosen initially. In this paper, we present a simple proof for the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2305.00071
-/

namespace Collatz.Papers.Arxiv2305_00071

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Masoud Allame and A. Hadi\u2010Vencheh, \"Does the Collatz Sequence Eventually Reach 1 for All Positive Integer Initial Values?\", arXiv:2305.00071 [2023]."

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

end Collatz.Papers.Arxiv2305_00071
