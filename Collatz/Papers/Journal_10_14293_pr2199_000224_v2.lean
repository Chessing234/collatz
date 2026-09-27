import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Javier Vicente Hernandez, "THE COLLATZ REGULAR LANGUAGE", 2023.

Title: THE COLLATZ REGULAR LANGUAGE

Abstract (from harvested metadata, truncated):
Does the Collatz conjecture shelter a regular language? In this article we address that question representing the Collatz sequences as words from the language L, accepted by the deterministic finite automaton M.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.14293/pr2199.000224.v2
-/

namespace Collatz.Papers.Journal_10_14293_pr2199_000224_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Javier Vicente Hernandez, \"THE COLLATZ REGULAR LANGUAGE\", DOI:10.14293/pr2199.000224.v2 [2023]."

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

end Collatz.Papers.Journal_10_14293_pr2199_000224_v2
