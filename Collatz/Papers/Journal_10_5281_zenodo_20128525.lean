import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for julian redero, "Analytic Reduction of the Collatz Problem to a Finite Residual Frontier", 2026.

Title: Analytic Reduction of the Collatz Problem to a Finite Residual Frontier

Abstract (from harvested metadata, truncated):
We present a standalone analytic reduction of the Collatz problem to a finite explicitresidual frontier. The argument proceeds through reduction to odd multiples of 3, analyticdescent in the regime e(u) = v2(9u + 1) ≥ 7, reduction of the residual regime e(u) ≤ 6to stable dyadic leaves, passage from depth-3 stable leaves to primitive families, andreorganization of the resulting primitive layer into 64 admissible affine families modulo192. The active branch of each admissible family is reduced to a distinguished terminalfamily associated with 104, whose remaining 34 base cases are finite and explicitly listed.The only configurations not closed analytically in the present paper are the rigid first-exitseeds arising from the admissible active families. These seeds form a finite explicit...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20128525
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20128525

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "julian redero, \"Analytic Reduction of the Collatz Problem to a Finite Residual Frontier\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20128525 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20128525
