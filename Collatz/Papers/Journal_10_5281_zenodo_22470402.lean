import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "Collatz, Halting, and the Uncomputable Edge of Simple Arithmetic — E8 Intelligence Research", 2026.

Title: Collatz, Halting, and the Uncomputable Edge of Simple Arithmetic — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The Collatz Conjecture (3n+1 problem) is the simplest undecidable-looking arithmetic iteration; Hilbert's Entscheidungsproblem and Turing's halting problem prove a class of problems are formally uncomputable. | MATH: Collatz map: \( T(n) = n/2 \) if \( n \) even, \( T(n) = 3n+1 \) if \( n \) odd. Conjecture: \( \forall n \in \mathbb{Z}^+ \), \( \exists k \): \( T^k(n) = 1 \). No closed-form solution; known to hold for \( n < 2^{68} \) (empirical). Turing: no general algorithm decides halting for all (input, program) pairs — diagonalization argument. Hilbert's Entscheidungsproblem: first-order logic validity is undecidable (Church–Turing theorem). | CONNECTION: The Collatz map is a d...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22470402
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22470402

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"Collatz, Halting, and the Uncomputable Edge of Simple Arithmetic — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22470402 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22470402
