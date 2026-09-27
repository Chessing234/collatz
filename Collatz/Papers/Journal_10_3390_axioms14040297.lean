import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Edward Tutaj and Halszka Tutaj–Gasińska, "Furstenberg Topology and Collatz Problem", 2025.

Title: Furstenberg Topology and Collatz Problem

Abstract (from harvested metadata, truncated):
The aims of this paper are two-fold. First, we present the result of the decomposition on the iterations of a Collatz transform into arithmetic sequences. With this, we prove that in Furstenberg topology, the set of (odd) integers with an infinite stopping time is closed and nowhere dense. Then, we move our considerations to some monoids L in N, where we define a suitably modified Collatz transform, and we present some results of numerical investigations on the behaviour of these modified transforms.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3390/axioms14040297
-/

namespace Collatz.Papers.Journal_10_3390_axioms14040297

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Edward Tutaj and Halszka Tutaj–Gasińska, \"Furstenberg Topology and Collatz Problem\", Axioms, DOI:10.3390/axioms14040297 [2025]."

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

end Collatz.Papers.Journal_10_3390_axioms14040297
