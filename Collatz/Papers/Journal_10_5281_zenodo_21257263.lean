import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Abolfazl Shahraki, "A Complete Proof of the Collatz Conjecture", 2026.

Title: A Complete Proof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
In this paper, we prove the Collatz conjecture (3n+1 problem) using strong induction and binary analysis. Contact: +98 935 628 6975 (Iran)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21257263
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21257263

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Abolfazl Shahraki, \"A Complete Proof of the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21257263 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21257263
