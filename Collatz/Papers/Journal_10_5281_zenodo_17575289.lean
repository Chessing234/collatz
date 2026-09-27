import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for ARDITO, NICOLA, "A convergence proposal for the Collatz sequence: the geometric proof of the Custom Conjecture", 2025.

Title: A convergence proposal for the Collatz sequence: the geometric proof of the Custom Conjecture

Abstract (from harvested metadata, truncated):
The present paper is an extension of the paper entitled "A convergence proposal for the Collatz sequence: the Custom Conjecture". In that paper, a reformulation of the famous Collatz conjecture was proposed, through a personalized sequence that preserves its structure but allows a more targeted analysis of the behavior of the natural numbers.In this new version, the geometric aspect of the custom sequence is deepened, introducing a proof of the conjecture based on the intersection between two lines constructed from the segments associated with the terms of the sequence. In particular, the segments deriving from the congruous numbers 3 modulo 4 are analyzed, demonstrating that the average value of their angular coefficient exceeds the constant value of the second segment. Such a...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17575289
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17575289

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "ARDITO, NICOLA, \"A convergence proposal for the Collatz sequence: the geometric proof of the Custom Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.17575289 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17575289
