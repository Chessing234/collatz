import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael Mark Anthony, "The Collatz Conjecture", arXiv:2510.01777 [2025].

Title: The Collatz Conjecture

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture states any positive integer will eventually reach 1 if you repeatedly apply a simple set of rules: if the number is even, divide it by two; if it is odd, multiply it by three and add one. The conjecture is till unproven due to its difficult binary nature between even and odd sequence values. However, a new trigonometric method is proposed to give a general proof that a Collatz sequence always end up at 1. The general path of the proof is similar to Euclid’s proof of the infinitude of primes by ascension.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2510.01777
-/

namespace Collatz.Papers.Arxiv2510_01777

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael Mark Anthony, \"The Collatz Conjecture\", arXiv:2510.01777 [2025]."

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

end Collatz.Papers.Arxiv2510_01777
