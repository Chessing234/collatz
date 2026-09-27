import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hamaji, Shinsuke, "The Hamaji Conjecture: A Structural Formulation of the Collatz Problem via 4D Natural Numbers", 2025.

Title: The Hamaji Conjecture: A Structural Formulation of the Collatz Problem via 4D Natural Numbers

Abstract (from harvested metadata, truncated):
The Collatz Conjecture has remained unsolved due to its nature as a Halting Problem and the structural deficit arising from the lack of integration between linear number theory (Peano Axioms) and non-linear structural analysis (Cantor Set Theory). The author successfully proposed a structural resolution to the Collatz Conjecture by utilizing the Cantor Pairing Function to enforce the "Symmetrization of the Start and Stop Point (1)". This paper defines the Hamaji Conjecture, a new proposition logically stronger than the Collatz Conjecture, derived from the established structural resolution. The Hamaji Conjecture asserts that the total count of $4n+1$ type odd numbers (Generations), $K$, encountered by any natural number $N$ before reaching $1$, is always less than the initial number $N$....

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17693599
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17693599

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hamaji, Shinsuke, \"The Hamaji Conjecture: A Structural Formulation of the Collatz Problem via 4D Natural Numbers\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.17693599 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17693599
