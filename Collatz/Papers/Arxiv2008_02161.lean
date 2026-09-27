import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ken Surendran and Desarazu Krishna Babu, "Collatz Conjecture: Exposition and Proof Through A Structured Approach", arXiv:2008.02161 [2020].

Title: Collatz Conjecture: Exposition and Proof Through A Structured Approach

Abstract (from OpenAlex metadata, truncated):
A structured approach for the Collatz conjecture is presented using just the odd integers that are, in turn, divided into categories based on the roles they play such as Starter, Intermediary and Terminal. The expression 4x+1 is used as a tool to expose all the hidden and significant characteristics of the conjecture that lead us to its proof. The mixing properties of the iterates are addressed by showing that the Collatz iterates of half of all the odd integers that are of the form 4m+3, on the average, increase by three times the value of the odd integer that was used to start with, while the iterates of those of 4m+1, on the average, decrease by a factor of four. Further, expressions are provided to generate all the sets of odd integers where the Collatz iterate of all the integers in each set is an integer of the of form 6m+1 or 6m+5. The significance of the Collatz net (tree) become

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2008.02161
-/

namespace Collatz.Papers.Arxiv2008_02161

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ken Surendran and Desarazu Krishna Babu, \"Collatz Conjecture: Exposition and Proof Through A Structured Approach\", arXiv:2008.02161 [2020]."

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

end Collatz.Papers.Arxiv2008_02161
