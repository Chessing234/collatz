import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Fujimoto, Nobuki et al., "Carry Mixing and Spectral Gap Analysis of the Collatz Conjecture: 202 Lean4 Theorems and the Fibonacci Firewall", 2026.

Title: Carry Mixing and Spectral Gap Analysis of the Collatz Conjecture: 202 Lean4 Theorems and the Fibonacci Firewall

Abstract (from harvested metadata, truncated):
A structural proof chain for the Collatz conjecture: 202 Lean4 theorems (zero sorry). Introduces Carry Mixing mechanism (firewall at consecutive zero-bits), Fibonacci Firewall (F(k+2)/2^k exponential decay), spectral gap analysis (gap >= 0.345), and Perelman-Collatz structural correspondence. Reduces Collatz to Carry Mixing Conjecture (CMC), strictly weaker than full equidistribution.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19495461
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19495461

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Fujimoto, Nobuki et al., \"Carry Mixing and Spectral Gap Analysis of the Collatz Conjecture: 202 Lean4 Theorems and the Fibonacci Firewall\", Zenodo, DOI:10.5281/zenodo.19495461 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19495461
