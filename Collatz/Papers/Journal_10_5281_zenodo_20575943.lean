import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "A Word-Level Occupation–Realizer Reduction for the Accelerated 3x + 1 Map", 2026.

Title: A Word-Level Occupation–Realizer Reduction for the Accelerated 3x + 1 Map

Abstract (from harvested metadata, truncated):
This note turns EOC into a finite congruence problem: high time-axis occupation must force high least-realizer cost. In this form, the Collatz obstruction becomes a word-level arithmetic question — whether dangerous valuation words can be realized by small odd integers.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20575943
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20575943

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"A Word-Level Occupation–Realizer Reduction for the Accelerated 3x + 1 Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20575943 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20575943
