import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for timjicht, Ayman, "Collatz Conjucture", 2024.

Title: Collatz Conjucture

Abstract (from harvested metadata, truncated):
This is an artical that contain a Proof of Syracuse conjecture and an explication of why is its hard to solve.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.24955449
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_24955449

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "timjicht, Ayman, \"Collatz Conjucture\", figshare, DOI:10.6084/m9.figshare.24955449 [2024]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_24955449
