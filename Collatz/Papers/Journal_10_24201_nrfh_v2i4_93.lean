import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Ana María Barrenechea, "Tomás Navarro, Estudios de fonología española. Syracuse University Press. Syracuse, New York, 1946, 217 págs.", 2017.

Title: Tomás Navarro, Estudios de fonología española. Syracuse University Press. Syracuse, New York, 1946, 217 págs.

Abstract (from harvested metadata, truncated):
Se reseñó el libro: Estudios de fonología española.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.24201/nrfh.v2i4.93
-/

namespace Collatz.Papers.Journal_10_24201_nrfh_v2i4_93

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Ana María Barrenechea, \"Tomás Navarro, Estudios de fonología española. Syracuse University Press. Syracuse, New York, 1946, 217 págs.\", Nueva Revista de Filología Hispánica (NRFH), DOI:10.24201/nrfh.v2i4.93 [2017]."

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

end Collatz.Papers.Journal_10_24201_nrfh_v2i4_93
