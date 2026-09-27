import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rahimi, Al, "The Inverse Syracuse Graph: Automaticity and Regular Structure in Collatz Dynamics", 2026.

Title: The Inverse Syracuse Graph: Automaticity and Regular Structure in Collatz Dynamics

Abstract (from harvested metadata, truncated):
This paper investigates a fundamental asymmetry in Collatz (Syracuse) dynamics.It expands and refines the idea of automaticity of the inverse Collatz (Syracuse) published in our earlier work [13] While the forward map F is many-to-one and resists finite-state characterization, its inverse relation F−1 exhibits a rigid, automatic structure. For any odd integer D ̸≡ 0 (mod 3), we prove that the ordered predecessor sequence {P(D,k)}k≥1 satisfies the affine recurrence P(D,k +1) = 4P(D,k)+1, and that its binary encodings form the Regular Language bin(P(D,1))(01)∗, where P(D,1) is the minimal odd preimage. This regular-language description leads to a second main result: the Inverse Syracuse Graph...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.31435792
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_31435792

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rahimi, Al, \"The Inverse Syracuse Graph: Automaticity and Regular Structure in Collatz Dynamics\", figshare, DOI:10.6084/m9.figshare.31435792 [2026]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_31435792
