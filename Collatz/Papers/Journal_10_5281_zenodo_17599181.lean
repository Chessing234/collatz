import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bozhilov, Dobri, "On the impossibility of divergent sequences in The Collatz conjecture", 2026.

Title: On the impossibility of divergent sequences in The Collatz conjecture

Abstract (from harvested metadata, truncated):
This paper proves that it is impossible to have an infinite sequence of numbers, built according to the rules of the Collatz Conjecture. This is due to the accumulation of unfulfillable requirements for the first member of this sequence when the number of steps becomes infinite.This paper can be seen as a simplified version of the previous paper, entitled "On the impossibility of an infinite chain in The Collatz Conjecture"

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17599181
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17599181

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bozhilov, Dobri, \"On the impossibility of divergent sequences in The Collatz conjecture\", Zenodo, DOI:10.5281/zenodo.17599181 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17599181
