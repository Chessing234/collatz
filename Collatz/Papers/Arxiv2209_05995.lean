import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for H. Nelson Crooks and Chigozie Nwoke, "Collatz Conjecture: Patterns Within", arXiv:2209.05995 [2022].

Title: Collatz Conjecture: Patterns Within

Abstract (from OpenAlex metadata, truncated):
Collatz Conjecture sequences increase and decrease in seemingly random fashion. By identifying and analyzing the forms of numbers, we discover that Collatz sequences are governed by very specific, well-defined rules, which we call cascades.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2209.05995
-/

namespace Collatz.Papers.Arxiv2209_05995

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "H. Nelson Crooks and Chigozie Nwoke, \"Collatz Conjecture: Patterns Within\", arXiv:2209.05995 [2022]."

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

end Collatz.Papers.Arxiv2209_05995
