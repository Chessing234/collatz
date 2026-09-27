import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Feng Pan and J. P. Draayer, "A polynomial approach to the Collatz conjecture", arXiv:1905.08462 [2019].

Title: A polynomial approach to the Collatz conjecture

Abstract (from OpenAlex metadata, truncated):
The Collatz conjecture is explored using polynomials based on a binary numeral system. It is shown that the degree of the polynomials, on average, decreases after a finite number of steps of the Collatz operation, which provides a weak proof of the conjecture by using induction with respect to the degree of the polynomials.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1905.08462
-/

namespace Collatz.Papers.Arxiv1905_08462

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Feng Pan and J. P. Draayer, \"A polynomial approach to the Collatz conjecture\", arXiv:1905.08462 [2019]."

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

end Collatz.Papers.Arxiv1905_08462
