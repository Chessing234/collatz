import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nuriyev, Urfat and Nuriyeva, Fidan, "On a Representation of the Collatz Procedure", 2025.

Title: On a Representation of the Collatz Procedure

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1109/pci66488.2025.11219837
-/

namespace Collatz.Papers.Journal_10_1109_pci66488_2025_11219837

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nuriyev, Urfat and Nuriyeva, Fidan, \"On a Representation of the Collatz Procedure\", 2025 6th International Conference on Problems of Cybernetics and Informatics (PCI), DOI:10.1109/pci66488.2025.11219837 [2025]."

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

end Collatz.Papers.Journal_10_1109_pci66488_2025_11219837
