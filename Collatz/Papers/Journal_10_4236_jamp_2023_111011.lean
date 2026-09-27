import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ramon Carbó‐Dorca, "Collatz Conjecture Redefinition on Prime Numbers", 2023.

Title: Collatz Conjecture Redefinition on Prime Numbers

Abstract (from harvested metadata, truncated):
The definition of Collatz Operator, the mathematical avatar of the Collatz Algorithm, permits the transformation of the Collatz conjecture, which is delineated over the whole natural number set, into an equivalent inference restricted to the odd prime number set only. Based on this redefinition, one can describe an empirical-heuristic proof of the Collatz conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4236/jamp.2023.111011
-/

namespace Collatz.Papers.Journal_10_4236_jamp_2023_111011

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ramon Carbó‐Dorca, \"Collatz Conjecture Redefinition on Prime Numbers\", Journal of Applied Mathematics and Physics, DOI:10.4236/jamp.2023.111011 [2023]."

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

end Collatz.Papers.Journal_10_4236_jamp_2023_111011
