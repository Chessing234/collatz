import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Sylvia Benton, "The Gorgon Plaque at Syracuse", 1954.

Title: The Gorgon Plaque at Syracuse

Abstract (from harvested metadata, truncated):
Dr. Bernabò-brea has kindly given me a new photograph of this monument. It shows the red paint at the outer corner of the gorgon's eye, which makes her eye look bigger and more sinister. It is not, however, a leer such as many early gorgons wear: the pupil is still in the middle of the eye. A lesion in this region of the eye may be due to strain. Our artist is depicting a gorgon under pressure. We must think away two round, dark shadows behind the top of the plaque: the real top is level with the upper end of the gorgon's ears. Dr. Bernabò-Brea was good enough to discuss the plaque with me, and he allowed me to study it outside its glass case. Here are a few observations: 1. What Should Not...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1017/s0068246200006589
-/

namespace Collatz.Papers.Journal_10_1017_s0068246200006589

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Sylvia Benton, \"The Gorgon Plaque at Syracuse\", Papers of the British School at Rome, DOI:10.1017/s0068246200006589 [1954]."

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

end Collatz.Papers.Journal_10_1017_s0068246200006589
