import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elia, Marcus, Tucker, Amanda, "Consecutive Integers and the Collatz Conjecture", arXiv:1511.09141 [2015].

Title: Consecutive Integers and the Collatz Conjecture

Abstract (from arXiv metadata, truncated):
Pairs of consecutive integers have the same height in the Collatz problem with surprising frequency. Garner gave a conjectural family of conditions for exactly when this occurs. Our main result is an infinite family of counterexamples to Garner's conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1511.09141
-/

namespace Collatz.Papers.Arxiv1511_09141

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elia, Marcus and Tucker, Amanda, \"Consecutive Integers and the Collatz Conjecture\", arXiv:1511.09141 [2015]."

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

end Collatz.Papers.Arxiv1511_09141
