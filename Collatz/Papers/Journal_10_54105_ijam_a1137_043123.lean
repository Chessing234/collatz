import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for T M Nishad and Mohamed M Azzedine, "Proofs of Beal’s Conjecture, Fermat’s Conjecture, Collatz Conjecture and Goldbach Conjecture", 2022.

Title: Proofs of Beal’s Conjecture, Fermat’s Conjecture, Collatz Conjecture and Goldbach Conjecture

Abstract (from harvested metadata, truncated):
In this article the elementary mathematical methods are used to prove Beal’s Conjecture, Fermat’s Conjecture, Collatz Conjecture and Goldbach Conjecture.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.54105/ijam.a1137.043123
-/

namespace Collatz.Papers.Journal_10_54105_ijam_a1137_043123

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "T M Nishad and Mohamed M Azzedine, \"Proofs of Beal’s Conjecture, Fermat’s Conjecture, Collatz Conjecture and Goldbach Conjecture\", Indian Journal of Advanced Mathematics, DOI:10.54105/ijam.a1137.043123 [2022]."

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

end Collatz.Papers.Journal_10_54105_ijam_a1137_043123
