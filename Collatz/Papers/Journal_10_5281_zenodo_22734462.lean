import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Saed Darabi, "A Structural Approach to the Collatz Conjecture", 2026.

Title: A Structural Approach to the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This preprint develops a structural and set-theoretic approach to the Collatz conjecture, with emphasis on the dynamics of odd integers. The usual Collatz process is compressed into odd-to-odd steps, and the sets Am are defined according to the exact number of compressed steps required to reach the terminal state 1. Their union is denoted by U. Independently, the odd integers are partitioned through residue classes and finite-depth constraint families C, providing a complete arithmetic covering of the odd domain without omission. The paper carefully distinguishes between arithmetic coverage and membership in U, proves the parent-child inclusion relation for the partition constraints, and cla...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22734462
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22734462

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Saed Darabi, \"A Structural Approach to the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22734462 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22734462
