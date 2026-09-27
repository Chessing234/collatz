import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Alex Nguhi and Cleophas Kweyu, "On Generalized Convergence in Collatz Systems", 2021.

Title: On Generalized Convergence in Collatz Systems

Abstract (from harvested metadata, truncated):
The Collatz Conjecture belongs to the generalized class of Dynamicalsystem δk + β, where δ = 3, β = 1.This paper establishes that such asystem converges to β as long as the conditions are suitable. A full de-scription of the Collatz system is given and formula derived for the reversenumber, synchronized elements(those with similar Collatz Sequence) andclosed forms that can help ease with the computation.One of the most important discoveries of this paper is that the CollatzSpace is bounded by 1 at the end and by an odd multiple of 3 on theother end. From this a proof of the elusive conjecture can then be derivedeasily

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/fzhn5
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_fzhn5

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Alex Nguhi and Cleophas Kweyu, \"On Generalized Convergence in Collatz Systems\", DOI:10.31219/osf.io/fzhn5 [2021]."

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

end Collatz.Papers.Journal_10_31219_osf_io_fzhn5
