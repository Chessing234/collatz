import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Saharsh Kumar, "Contribution to Collatz Conjecture", 2024.

Title: Contribution to Collatz Conjecture

Abstract (from harvested metadata, truncated):
It is proved that, lim 𝑛→∞ 𝑧 (𝑛) = 1 Where, z(n) =, 𝑧(𝑛){ ⌊ 𝑛 2 ⌋ Because in collatz conjecture n/2 is important. And a number will only decrease when n/2 is performed.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.4992792
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_4992792

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Saharsh Kumar, \"Contribution to Collatz Conjecture\", SSRN Electronic Journal, DOI:10.2139/ssrn.4992792 [2024]."

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

end Collatz.Papers.Journal_10_2139_ssrn_4992792
