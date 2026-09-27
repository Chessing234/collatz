import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lagarias, Jeffrey C., "The 3x+1 Problem: An Overview", arXiv:2111.02635 [2021].

Title: The 3x+1 Problem: An Overview

Abstract (from OpenAlex metadata, truncated):
This paper is an overview and survey of work on the 3x+1 problem, also called the Collatz problem, and generalizations of it. It gives a history of the problem. It addresses two questions: (1) What can mathematics currently say about this problem? (as of 2010). (2) How can this problem be hard, when it is so easy to state?

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2111.02635
-/

namespace Collatz.Papers.Arxiv2111_02635

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lagarias, Jeffrey C., \"The 3x+1 Problem: An Overview\", arXiv:2111.02635 [2021]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2111_02635
