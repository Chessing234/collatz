import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Theophilus Agama, "The theory of the Collatz process and the method of dynamical balls", 2022.

Title: The theory of the Collatz process and the method of dynamical balls

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.14293/111.000/000032.v1
-/

namespace Collatz.Papers.Journal_10_14293_111_000_000032_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Theophilus Agama, \"The theory of the Collatz process and the method of dynamical balls\", DOI:10.14293/111.000/000032.v1 [2022]."

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

end Collatz.Papers.Journal_10_14293_111_000_000032_v1
