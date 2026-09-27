import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sebastien Riche, "PARTIAL SUMS OF THE 3X+1 ACCUMULATION TERM", 2025.

Title: PARTIAL SUMS OF THE 3X+1 ACCUMULATION TERM

Abstract (from harvested metadata, truncated):
The "3x+1" accumulation term, E(v_k), is what becomes of the "+1" part after k iteration of the "shortcut" Collatz function T(n) which takes odd integers n to (3n+1)/2 and even integers n to n/2, so T^k(n)=(3^i*n+E(v_k))/2 where i is the number of odd terms in the trajectory of n. A known and easy to prove result is that the total sum of the accumulation terms of all the 2^k possible parity vectors v_k of length k is k4^(k-1). This paper will show that the partial sum of the accumulation terms of all vectors v_k of length k for a fixed value of i is the sum from p=0 to i-1 of the binomial(k,p)*(2^k - 3^p). A very insightful proof of this will be presented, as well as a more classical one.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2025-f00x5-v2
-/

namespace Collatz.Papers.Journal_10_33774_coe_2025_f00x5_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sebastien Riche, \"PARTIAL SUMS OF THE 3X+1 ACCUMULATION TERM\", DOI:10.33774/coe-2025-f00x5-v2 [2025]."

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

end Collatz.Papers.Journal_10_33774_coe_2025_f00x5_v2
