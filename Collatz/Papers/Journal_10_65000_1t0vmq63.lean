import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for A Okoth and Bernard Okelo, "Arnold's Digitized Summation Technique and Generalized Notion of the Collatz Conjecture", 2019.

Title: Arnold's Digitized Summation Technique and Generalized Notion of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Many mathematicians have studied Collatz conjecture and its applications; however, it remains an open problem in the field of number theory and is interesting to study. In the present paper, we give a generalized notion of Collatz conjecture as per the new notion of Arnold's Digitized Summation Technique which involves adding digits of a number until we are left with only one single digit. Moreover, a detailed description of the first twenty positive integers is given.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.65000/1t0vmq63
-/

namespace Collatz.Papers.Journal_10_65000_1t0vmq63

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "A Okoth and Bernard Okelo, \"Arnold's Digitized Summation Technique and Generalized Notion of the Collatz Conjecture\", International Journal of Modern Computation Information and Communication Technology, DOI:10.65000/1t0vmq63 [2019]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_65000_1t0vmq63
