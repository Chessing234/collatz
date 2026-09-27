import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lixin Wang, "An Equivalent Helix Wave Construction for the Collatz Sequence: From Euler's Formula to Fourier Three-Component Isolation (V2)", 2026.

Title: An Equivalent Helix Wave Construction for the Collatz Sequence: From Euler's Formula to Fourier Three-Component Isolation (V2)

Abstract (from harvested metadata, truncated):
This paper establishes an equivalent geometric wave model for the Collatz sequence. The sole foundation of the construction is Euler's formula e^{i\pi} = -1, from which one derives \cos(\pi n) = (-1)^n for every integer n — an exact parity switch that makes it possible to distribute the three Collatz operations (\div 2, 3n, +1) uniquely into three mutually orthogonal Fourier components. Each positive integer n is modeled as the frequency of a positive helix; the helix's continued extension legitimizes the use of Fourier analysis, a legitimacy itself rooted in Euler's formula. The three-component decomposition shows that the entire contribution of +1 falls precisely in C_3 = (1 - \cos\pi z)/4 — a pure wave of frequency 1/2 containing no z — completely decoupled from the multiplicative \div...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20476704
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20476704

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lixin Wang, \"An Equivalent Helix Wave Construction for the Collatz Sequence: From Euler's Formula to Fourier Three-Component Isolation (V2)\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20476704 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20476704
