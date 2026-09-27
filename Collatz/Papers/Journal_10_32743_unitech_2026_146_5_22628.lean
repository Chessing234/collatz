import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Davletyrov, Nurbolat Nursultanovich and Aliyev, Yagub, "A STREAMING FPGA SOC FOR INVERSE COLLATZ PREDECESSOR GENERATION", 2026.

Title: A STREAMING FPGA SOC FOR INVERSE COLLATZ PREDECESSOR GENERATION

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.32743/unitech.2026.146.5.22628
-/

namespace Collatz.Papers.Journal_10_32743_unitech_2026_146_5_22628

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Davletyrov, Nurbolat Nursultanovich and Aliyev, Yagub, \"A STREAMING FPGA SOC FOR INVERSE COLLATZ PREDECESSOR GENERATION\", Universum:Technical sciences, DOI:10.32743/unitech.2026.146.5.22628 [2026]."

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

end Collatz.Papers.Journal_10_32743_unitech_2026_146_5_22628
