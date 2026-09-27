import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jorge Crespo, "Orbits Theory. A Complete Proof of the Collatz Conjecture", 2021.

Title: Orbits Theory. A Complete Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
In this work a complete proof of the Collatz Conjecture is presented. The solution assumes as hypothesis that Collatz's Conjecture is a consequence. We found that every natural number n_i∈N can be calculated starting from 1, using the function n_i=((2^(i-Ω)-C))⁄3^Ω , where: i≥0 represents the number of steps (operations of multiplications by two subtractions of one and divisions by three) needed to get from 1 to n_i, Ω≥0 represents the number of multiplications by three required and 0≤C≤2^(i-⌊i/3⌋ )-2^((i mod 3)) 3^⌊i/3⌋ is an accumulative constant that takes into account the order in which the operations of multiplication and division have been performed. Reversing the inversion, we have obtained the function: ((3^Ω n_i+C))⁄2^(i-Ω)=1 that proves that Collatz Conjecture it’s a consequence...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2021-9w3gs
-/

namespace Collatz.Papers.Journal_10_33774_coe_2021_9w3gs

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jorge Crespo, \"Orbits Theory. A Complete Proof of the Collatz Conjecture\", DOI:10.33774/coe-2021-9w3gs [2021]."

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

end Collatz.Papers.Journal_10_33774_coe_2021_9w3gs
