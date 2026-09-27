import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Arvind kumar singh, "A Deterministic Variant of the Collatz Process via Divisibility by 3", 2026.

Title: A Deterministic Variant of the Collatz Process via Divisibility by 3

Abstract (from harvested metadata, truncated):
Abstract This paper introduces a variant of the Collatz process based on divisibility by 3. Starting with any naturalnumber greater than 2, the procedure involves dividing by 3 when possible, or adjusting by ±1 to achievedivisibility before division. The sequence always converges to 1, offering a deterministic alternative to theclassical Collatz conjecture. This simple yet rigorous process highlights the interplay between modulararithmetic and iterative reduction, making it suitable for educational exploration. This record presents a deterministic iterative process on natural numbers greater than 2, inspired by the structural mechanics of the classical Collatz conjecture. The procedure maps...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22163592
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22163592

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Arvind kumar singh, \"A Deterministic Variant of the Collatz Process via Divisibility by 3\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22163592 [2026]."

/-- Recorded generalization-style claim shell; the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Journal_10_5281_zenodo_22163592
