import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bouazad, El Bachir, "Collatz Conjecture Proof Sidi Abdessalam Yassine Theorem", 2025.

Title: Collatz Conjecture Proof Sidi Abdessalam Yassine Theorem

Abstract (from harvested metadata, truncated):
The Collatz Conjecture is one of the most famous unsolved problems in mathematics .It is named after mathematician LOTHAR COLLATZ who proposed it in 1937 , Collatz Conjecture is also known as (3n+1 problem) or the (3n+1 Conjecture)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.5365949
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_5365949

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bouazad, El Bachir, \"Collatz Conjecture Proof Sidi Abdessalam Yassine Theorem\", DOI:10.2139/ssrn.5365949 [2025]."

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

end Collatz.Papers.Journal_10_2139_ssrn_5365949
