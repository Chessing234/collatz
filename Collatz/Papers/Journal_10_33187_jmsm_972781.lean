import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ramon Carbó‐Dorca and Carlos Castro Perelman, "Boolean Hypercubes, Classification of Natural Numbers, and the Collatz Conjecture", 2022.

Title: Boolean Hypercubes, Classification of Natural Numbers, and the Collatz Conjecture

Abstract (from harvested metadata, truncated):
Using simple arguments derived from the Boolean hypercube configuration, the structure of natural spaces, and the recursive exponential generation of the set of natural numbers, a linear classification of the natural numbers is presented. The definition of a pseudolinear Collatz operator, the description of the set of powers of $2$, and the construction of the natural numbers via this power set might heuristically prove the Collatz conjecture from an empirical point of view.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33187/jmsm.972781
-/

namespace Collatz.Papers.Journal_10_33187_jmsm_972781

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ramon Carbó‐Dorca and Carlos Castro Perelman, \"Boolean Hypercubes, Classification of Natural Numbers, and the Collatz Conjecture\", Journal of Mathematical Sciences and Modelling, DOI:10.33187/jmsm.972781 [2022]."

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

end Collatz.Papers.Journal_10_33187_jmsm_972781
