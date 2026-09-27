import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Urrutia Martinez, Kilder Alexis, "No Finite Modular Obstructions for the Inverse Collatz Tree", 2026.

Title: No Finite Modular Obstructions for the Inverse Collatz Tree

Abstract (from harvested metadata, truncated):
The paper demonstrates a general method for determining if a generalized Collatz-type map (called herein an a, b, c map) has modular obstructions via an exact solution over the accelerated inverse tree formulation. We fully work the case for the Collatz map (3, 1, 2 map) and demonstrate that no finite modular obstructions, equivalently, no modular holes, no profinite obstructions, and that the tree contains infinite representatives at each class.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20479807
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20479807

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Urrutia Martinez, Kilder Alexis, \"No Finite Modular Obstructions for the Inverse Collatz Tree\", Zenodo, DOI:10.5281/zenodo.20479807 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20479807
