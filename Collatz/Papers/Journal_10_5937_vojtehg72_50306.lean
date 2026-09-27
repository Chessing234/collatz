import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nicola Fabiano et al., "Some considerations on the total stopping time for the Collatz problem", 2024.

Title: Some considerations on the total stopping time for the Collatz problem

Abstract (from harvested metadata, truncated):
Introduction/purpose: The Collatz conjecture has been considered and the stopping time needed for the recursive transformation to end has been investigated. Methods: A statistical analysis on the stopping time has been used. Results: The statistical approach shows that the probability of finding an infinite stopping time, that is a violation of the Collatz conjecture, is extremely low. Conclusion: Picking precisely one particular atom in the Universe is still more favorable, by more than 61 orders of magnitude, than encountering an infinite total stopping time.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5937/vojtehg72-50306
-/

namespace Collatz.Papers.Journal_10_5937_vojtehg72_50306

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nicola Fabiano et al., \"Some considerations on the total stopping time for the Collatz problem\", Vojnotehnicki glasnik, DOI:10.5937/vojtehg72-50306 [2024]."

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

end Collatz.Papers.Journal_10_5937_vojtehg72_50306
