import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Khaled Mounir, "Collatz theory", 2024.

Title: Collatz theory

Abstract (from harvested metadata, truncated):
"The paper explores a novel solution to the Collatz conjecture, presenting a new perspective that simplifies its understanding. The proposed method addresses key steps in the conjecture and provides a complete proof, which could have significant implications for number theory."

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2024-d01z9
-/

namespace Collatz.Papers.Journal_10_33774_coe_2024_d01z9

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Khaled Mounir, \"Collatz theory\", DOI:10.33774/coe-2024-d01z9 [2024]."

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

end Collatz.Papers.Journal_10_33774_coe_2024_d01z9
