import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lafontaine, Mary, "A Note on a Claimed Disproof of the Collatz Conjecture", 2026.

Title: A Note on a Claimed Disproof of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This note provides a critical analysis of a recent manuscript claiming a disproof of the Collatz conjecture. We demonstrate that the central step of the argument is not mathematically well-defined, due to a misuse of asymptotic notation. Consequently, the reasoning cannot support the claimed conclusion. More generally, this note highlights the importance of exact use of asymptotic notation in discrete dynamical systems.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19830846
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19830846

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lafontaine, Mary, \"A Note on a Claimed Disproof of the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.19830846 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19830846
