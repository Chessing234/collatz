import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Easterly, Karl, "A Geometric Framework for the Collatz Conjecture: Coordinate Space, Bounding Surfaces, Partition Formulas, and Applications to Cryptography and Compression", 2026.

Title: A Geometric Framework for the Collatz Conjecture: Coordinate Space, Bounding Surfaces, Partition Formulas, and Applications to Cryptography and Compression

Abstract (from harvested metadata, truncated):
This paper presents a geometric framework for the Collatz conjecture based on a navigable two-dimensional coordinate space in which the Collatz tree operations define four movement directions. The framework introduces three foundational bounding surface equations — upSurface, bottomSurface, and deltaMatrix — whose algebraic identity proves that the gap between bounding surfaces is exactly independent of the initialization vector IV for all coordinates. This IV cancellation is a proven algebraic result, not a conjecture. The coordinate space is characterized by a walker model in which ascending and descending the Collatz tree corresponds to counterclockwise and clockwise rotation through the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19560537
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19560537

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Easterly, Karl, \"A Geometric Framework for the Collatz Conjecture: Coordinate Space, Bounding Surfaces, Partition Formulas, and Applications to Cryptography and Compression\", Zenodo, DOI:10.5281/zenodo.19560537 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19560537
