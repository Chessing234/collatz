import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Cho, Seong Ik, "Collatz Problem of Positive Integers", arXiv:1002.3973 [2010].

Title: Collatz Problem of Positive Integers

Abstract (from arXiv metadata, truncated):
This paper has been withdrawn by the author due to a serious mistake on Lemma 2.4.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1002.3973
-/

namespace Collatz.Papers.Arxiv1002_3973

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Cho, Seong Ik, \"Collatz Problem of Positive Integers\", arXiv:1002.3973 [2010]."

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

end Collatz.Papers.Arxiv1002_3973
