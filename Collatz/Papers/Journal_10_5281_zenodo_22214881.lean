import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Claudio Lucherini, "Terminal Residue Sieves in the Single-Defect Stratum of a Width-Two Collatz Survivor System", 2026.

Title: Terminal Residue Sieves in the Single-Defect Stratum of a Width-Two Collatz Survivor System

Abstract (from harvested metadata, truncated):
We study a finite terminal residue sieve arising from the single-defect stratum of a width-two accelerated odd Collatz survivor system. Using the exact top-bit realization criterion for class-7 defects together with the class-3 mod-6 realization law, we define the residue classes not certified by the first R terminal witnesses. We prove that, over the natural common period, the exceptional set has exact cardinality 2R for every R >= 2. The proof uses half-period complementarity of the terminal characters, uniqueness of a zero-witness 2-adic branch, and a two-lift recurrence. The result is finite-depth and does not establish diagonal avoidance, the general width-two dominance conjecture, or t...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22214881
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22214881

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Claudio Lucherini, \"Terminal Residue Sieves in the Single-Defect Stratum of a Width-Two Collatz Survivor System\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22214881 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22214881
