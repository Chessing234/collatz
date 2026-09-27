import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Paul S. Bruckman, "RETRACTED ARTICLE: A proof of the Collatz conjecture", 2008.

Title: RETRACTED ARTICLE: A proof of the Collatz conjecture

Abstract (from harvested metadata, truncated):
An elementary proof by contradiction of the Collatz Conjecture (CC) (also known as the '3X + 1' Conjecture), is presented. A modified form of the Collatz transformation is formulated, leading to the concept of a modified Collatz chain. A smallest counterexample N0 is hypothesized; the existence of N0 implies that N0 must generate an infinite sequence {Nk}, each of whose elements is at least as large as N0. A formula for Nk is derived, in terms of an auxiliary sequence {Ek} and the starting value N0. It is shown that each Ek satisfies k = Ek < 1.585k; this, in turn, leads us to conclude that N0 is unbounded, which is a contradiction of its definition, thereby establishing CC.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1080/00207390701691574
-/

namespace Collatz.Papers.Journal_10_1080_00207390701691574

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Paul S. Bruckman, \"RETRACTED ARTICLE: A proof of the Collatz conjecture\", International Journal of Mathematical Education in Science and Technology, DOI:10.1080/00207390701691574 [2008]."

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

end Collatz.Papers.Journal_10_1080_00207390701691574
