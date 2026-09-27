import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Vincent Béhani, "Étude de la Conjecture de Syracuse et des opérateurs de Bishop du point de vue de la dynamique linéaire", 2023.

Title: Étude de la Conjecture de Syracuse et des opérateurs de Bishop du point de vue de la dynamique linéaire

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.70675/ea85b41aze6b7z44b9zb487zbede92fa1743
-/

namespace Collatz.Papers.Journal_10_70675_ea85b41aze6b7z44b9zb487zbede92fa1743

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Vincent Béhani, \"Étude de la Conjecture de Syracuse et des opérateurs de Bishop du point de vue de la dynamique linéaire\", DOI:10.70675/ea85b41aze6b7z44b9zb487zbede92fa1743 [2023]."

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

end Collatz.Papers.Journal_10_70675_ea85b41aze6b7z44b9zb487zbede92fa1743
