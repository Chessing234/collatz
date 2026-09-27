import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Griff Gurwell, "An Affine-Remainder Refinement of Coefficient Stopping Time in the Collatz Problem", 2026.

Title: An Affine-Remainder Refinement of Coefficient Stopping Time in the Collatz Problem

Abstract (from harvested metadata, truncated):
This paper develops an affine-remainder refinement of the classical Terras–Garner coefficient-stopping-time framework for the 3n+1 (Collatz) problem. For a trajectory whose normalized coefficient first falls below unity after q odd iterates, an exact extremal formula is derived for the largest additive affine remainder compatible with all preceding coefficient-survival constraints. The resulting first-crossing threshold is Theta_q = ( ( 2^{ ceil( q * log_2(3) ) - q * log_2(3) } - 1 ) / 3 ) * sum_{i=0}^{q-1} 2^{ - frac( i * log_2(3) ) } where frac(x) denotes the fractional part of x. This converts the additive obstruction into a Birkhoff sum for an irrational rotation by log_2(3). At continued-fraction convergent denominators, the Denjoy–Koksma inequality gives an explicit O(1) error...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22022716
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22022716

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Griff Gurwell, \"An Affine-Remainder Refinement of Coefficient Stopping Time in the Collatz Problem\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22022716 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22022716
