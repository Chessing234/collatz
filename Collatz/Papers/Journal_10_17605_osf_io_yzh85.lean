import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for محمد سالم السيد مصطفى, "3N+1 Proof of the Collatz Conjecture", 2025.

Title: 3N+1 Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
All questions related to the Collatz conjecture have been answered from the smallest to the largest. My proof of the Collatz conjecture is based on analyzing the changes in the resulting values when applying the operation to odd numbers. I have proven that every odd number can be classified according to its rank, which determines its position among the odd numbers, and that it cannot increase to infinity and that there is no closed circle in the integer. This proof is entirely mine.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17605/osf.io/yzh85
-/

namespace Collatz.Papers.Journal_10_17605_osf_io_yzh85

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "محمد سالم السيد مصطفى, \"3N+1 Proof of the Collatz Conjecture\", OSF Registries, DOI:10.17605/osf.io/yzh85 [2025]."

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

end Collatz.Papers.Journal_10_17605_osf_io_yzh85
