import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wolfdieter Lang, "On Collatz' Words, Sequences and Trees", arXiv:1404.2710 [2014].

Title: On Collatz' Words, Sequences and Trees

Abstract (from OpenAlex metadata, truncated):
Motivated by a recent work of Trümper we consider the general Collatz word (up-down pattern) and the sequences following this pattern. The recurrences for the first and last sequence entries are given, obtained from repeated application of the general solution of a binary linear inhomogeneous Diophantine equation. These recurrences are then solved. The Collatz tree is also discussed.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1404.2710
-/

namespace Collatz.Papers.Arxiv1404_2710

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wolfdieter Lang, \"On Collatz' Words, Sequences and Trees\", arXiv:1404.2710 [2014]."

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

end Collatz.Papers.Arxiv1404_2710
