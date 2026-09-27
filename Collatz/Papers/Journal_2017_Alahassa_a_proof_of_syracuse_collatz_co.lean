import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nonvikan Karl-Augustt Alahassa, ": A proof of Syracuse/Collatz conjecture", 2017.

Title: : A proof of Syracuse/Collatz conjecture

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: (no stable URL in metadata)
-/

namespace Collatz.Papers.Journal_2017_Alahassa_a_proof_of_syracuse_collatz_co

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nonvikan Karl-Augustt Alahassa, \": A proof of Syracuse/Collatz conjecture\", HAL (Le Centre pour la Communication Scientifique Directe) [2017]."

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

end Collatz.Papers.Journal_2017_Alahassa_a_proof_of_syracuse_collatz_co
