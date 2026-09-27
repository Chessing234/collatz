import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Régent, Xavier J., "Version 1 — Nitescence and the Collatz Conjecture: Early Metamathematical Draft", 2025.

Title: Version 1 — Nitescence and the Collatz Conjecture: Early Metamathematical Draft

Abstract (from harvested metadata, truncated):
Superseded historical version. This intermediate draft belongs to the early Nitescence-based, metamathematical phase of the project. For the final account of that approach, see “Structural Ascension and the Collatz Conjecture: A Historical Nitescence-Based Metamathematical Study”. The subsequent geometric development and current proposed resolution are presented in “The Syracuse Conjecture: A Categorical Resolution by Transport of Structure in the Sense of Bourbaki”.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.16410963
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_16410963

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Régent, Xavier J., \"Version 1 — Nitescence and the Collatz Conjecture: Early Metamathematical Draft\", DOI:10.5281/zenodo.16410963 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_16410963
