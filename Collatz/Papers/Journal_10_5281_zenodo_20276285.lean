import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Galoppo, Travis, "The Collatz Conjecture is a Two-Bit Problem", 2026.

Title: The Collatz Conjecture is a Two-Bit Problem

Abstract (from harvested metadata, truncated):
In this work we prove a reduction of the Collatz Conjecture to an open question of ergodic mixing. By positioning the Collatz sequence as a race between the leading bit and trailing bit of the iterates in dyadic representation, we prove that convergence hinges on the local ergodicity of just two "indicator" bits governing contraction. We prove a structural upper bound on the velocity of the leading bit, and a stochastic lower bound on the velocity of the trailing bit contingent on the uniformity of these indicator bits. The resulting velocity gap implies global convergence for any trajectory meeting the local ergodicity condition. We derive the asymptotic uniformity of these bits via the fra...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20276285
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20276285

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Galoppo, Travis, \"The Collatz Conjecture is a Two-Bit Problem\", Zenodo, DOI:10.5281/zenodo.20276285 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20276285
