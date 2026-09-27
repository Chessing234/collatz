import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Amauri Gutierrez, "Collatz conjecture revisited: an elementary generalization", 2020.

Title: Collatz conjecture revisited: an elementary generalization

Abstract (from harvested metadata, truncated):
Abstract Collatz conjecture states that iterating the map that takes even natural number n to n 2 {n \over 2} and odd natural number n to 3n + 1, will eventually obtain 1. In this paper a new generalization of the Collatz conjecture is analyzed and some interesting results are obtained. Since Collatz conjecture can be seen as a particular case of the generalization introduced in this articule, several more general conjectures are also presented.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2478/ausm-2020-0007
-/

namespace Collatz.Papers.Journal_10_2478_ausm_2020_0007

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Amauri Gutierrez, \"Collatz conjecture revisited: an elementary generalization\", Acta Universitatis Sapientiae Mathematica, DOI:10.2478/ausm-2020-0007 [2020]."

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

end Collatz.Papers.Journal_10_2478_ausm_2020_0007
