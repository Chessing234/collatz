import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jordan Gidman, "A synthetic spectral operator for the Collatz (3x+1) conjecture", 2026.

Title: A synthetic spectral operator for the Collatz (3x+1) conjecture

Abstract (from harvested metadata, truncated):
# Collatz Operator Toolkit **A synthetic spectral operator for the Collatz (3x+1) conjecture** **Author:** Jordan Gidman (CoreTheoretics) **ORCID:** [0009-0000-2955-5833](https://orcid.org/0009-0000-2955-5833) ## Abstract Using the Operator Toolkit framework, we constructed a **synthetic Collatz operator** from real trajectories and stopping times. The operator automatically discovered the correct asymptotic law: stopping time grows as \( c \cdot \ln n \). **Accuracy on real Collatz data:** **68.0%** **Core eigenvalue discovered:** λ₁ = 0.23636765 ## Key Results | Starting number | Predicted stopping time | |-----------------|-------------------------| | 27 | 7 | | 703 | 13 | | 871 | 14 | | 6171 | 17 | | 100,000 | 23 | | 1,000,000 | 28 | | 10,000,000 | 32 | ## Files (locked) -...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.31743010.v1
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_31743010_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jordan Gidman, \"A synthetic spectral operator for the Collatz (3x+1) conjecture\", Figshare, DOI:10.6084/m9.figshare.31743010.v1 [2026]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_31743010_v1
