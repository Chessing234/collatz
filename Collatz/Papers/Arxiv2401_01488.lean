import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mehdi Khoshakhlagh Varnosfaderani, "A Proof of Collatz Conjecture Using Pyramid Fractions", arXiv:2401.01488 [2024].

Title: A Proof of Collatz Conjecture Using Pyramid Fractions

Abstract (from OpenAlex metadata, truncated):
In this paper, I introduce a new concept of representing numbers in base ; in other words, I have found new series for any number similar to series that could be written according to the collatz sequence which is called zi(n) in this article. These series need to end with 1. Then, we use two sets of rules to make a diagram which then proves the existence of such series for any number.In this diagram, by branching numbers into different branches in accordance to the modularity of 4 and continuing branching to the point that their numbers have enough common terms in their collatz series, we could reduce zi(n) to zi(k) so that k

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2401.01488
-/

namespace Collatz.Papers.Arxiv2401_01488

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mehdi Khoshakhlagh Varnosfaderani, \"A Proof of Collatz Conjecture Using Pyramid Fractions\", arXiv:2401.01488 [2024]."

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

end Collatz.Papers.Arxiv2401_01488
