import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Shalom Eliahou and Jean-Louis Verger-Gaugry, "The number system in rational base $3/2$ and the $3x+1$ problem", arXiv:2504.13716 [2025].

Title: The number system in rational base $3/2$ and the $3x+1$ problem

Abstract (from OpenAlex metadata, truncated):
The representation of numbers in rational base $p/q$ was introduced in 2008 by Akiyama, Frougny & Sakarovitch, with a special focus on the case $p/q=3/2$. Unnoticed since then, natural questions related to representations in that specific base turn out to intimately involve the Collatz $3x+1$ function. Our purpose in this note is to expose these links and motivate further research into them.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2504.13716
-/

namespace Collatz.Papers.Arxiv2504_13716

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Shalom Eliahou and Jean-Louis Verger-Gaugry, \"The number system in rational base $3/2$ and the $3x+1$ problem\", arXiv:2504.13716 [2025]."

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

end Collatz.Papers.Arxiv2504_13716
