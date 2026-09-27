import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rock, James, "A Proof of the Collatz Conjecture: Universality via Modular Partitioning", 2026.

Title: A Proof of the Collatz Conjecture: Universality via Modular Partitioning

Abstract (from harvested metadata, truncated):
We introduce a new methodology: Exhaustive Modular Partitioning. By dividing the positive integers into fifteen distinct residue classes modulo 24, we demonstrate that every class converges to a finite branch structure. We define a Usage Factor and prove that the geometric series of branch proportions sums to exactly 1 (100%).

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21114137
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21114137

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rock, James, \"A Proof of the Collatz Conjecture: Universality via Modular Partitioning\", Zenodo, DOI:10.5281/zenodo.21114137 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21114137
