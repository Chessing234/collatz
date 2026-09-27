import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rajab, Raouf, "A new approach to study and analysis of behavior of Collatz sequences", 2025.

Title: A new approach to study and analysis of behavior of Collatz sequences

Abstract (from harvested metadata, truncated):
This paper introduces a new approach for the study and analysis of Collatz sequences based on three key Diophantine equations that describes the polynomial relationships between the length and the number of odd terms in any Collatz sequence. First, we prove the Diophantine equations used. Then, by choosing Collatz sequences with particular characteristics to effectively exploit the above equations, we study the behavior of Collatz sequences (of finite and infinite length). By using these equations, we can establish several simple relationships between the first term of the Collatz sequence and the parity vector of the sequence under consideration. In other words, these equations allow us to determine several properties of these sequences related to the conditions necessary for a sequence...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17879748
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17879748

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rajab, Raouf, \"A new approach to study and analysis of behavior of Collatz sequences\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.17879748 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17879748
