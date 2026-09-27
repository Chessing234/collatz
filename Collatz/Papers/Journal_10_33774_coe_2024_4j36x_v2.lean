import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Saleh Omran, "Suggested proof for the Collatz conjecture", 2024.

Title: Suggested proof for the Collatz conjecture

Abstract (from harvested metadata, truncated):
In the present work, we suggest a proof for 3n+1 problem which was originally introduced by Lothar Collatz in 1937. Collatz conjecture asserts that the function C : N to N; de�fined by C(n) = 3n + 1 if n is odd positive integer number, and C(n) = n/2 if n is even positive integer number goes to 1. We proof that the k-th iterate of Collatz function C^k(n) is bounded for all positive integer numbers k; n and converges to 1.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2024-4j36x-v2
-/

namespace Collatz.Papers.Journal_10_33774_coe_2024_4j36x_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Saleh Omran, \"Suggested proof for the Collatz conjecture\", DOI:10.33774/coe-2024-4j36x-v2 [2024]."

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

end Collatz.Papers.Journal_10_33774_coe_2024_4j36x_v2
