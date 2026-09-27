import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for redero, julian, "A source-compatible finite-certificate framework for the Collatz conjecture via compact L = 7 certification and global primitive", 2026.

Title: A source-compatible finite-certificate framework for the Collatz conjecture via compact L = 7 certification and global primitive

Abstract (from harvested metadata, truncated):
This article develops a finite-certificate framework for the Collatz problem based on asource-compatible decomposition of the odd dynamics. The argument separates three layers.First, an anti-9 reduction sends every odd integer not divisible by 3 to an odd predecessorsource divisible by 3. Second, a compact L = 7 frontier certificate organizes the residualsource dynamics into a finite family of admissible first-exit classes. Third, a primitive re-entrymechanism gives a strict descent of the primitive parameter outside the finite base rangeξ ≤ 6561.The proof is reduced to two explicitly identified components: an analytic descent argumenton primitive source families, and a finite certificate layer checking the frontier, first-exit,positivity, and compatibility conditions used by the descent....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20686113
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20686113

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "redero, julian, \"A source-compatible finite-certificate framework for the Collatz conjecture via compact L = 7 certification and global primitive\", DOI:10.5281/zenodo.20686113 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20686113
