import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mesut Kavak, "Brief Solutions To Collatz Problem, Goldbach Conjecture And Twin Primes", 2017.

Title: Brief Solutions To Collatz Problem, Goldbach Conjecture And Twin Primes

Abstract (from harvested metadata, truncated):
I published some solutions a time ago to Goldbach Conjecture, Collatz Problem and Twin Primes; but I noticed that there were some serious logic voids to explain the problems. After that I made some corrections in my another article; but still there were some mistakes. Even so, I can say it easily that here I brought exact solutions for them out by new methods back to the drawing board.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.1299204
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_1299204

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mesut Kavak, \"Brief Solutions To Collatz Problem, Goldbach Conjecture And Twin Primes\", Figshare, DOI:10.5281/zenodo.1299204 [2017]."

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

end Collatz.Papers.Journal_10_5281_zenodo_1299204
