import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ismail (Ari Khusraw) Mostafanejad, "proof of Collatz conjecture - Theorem", 2026.

Title: proof of Collatz conjecture - Theorem

Abstract (from harvested metadata, truncated):
Collatz conjecture is now proven. It was first introduced by German mathematician Lothar Collatz in 1937.It is not a conjecture anymore but a proven Theorem.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21683175
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21683175

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ismail (Ari Khusraw) Mostafanejad, \"proof of Collatz conjecture - Theorem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21683175 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21683175
