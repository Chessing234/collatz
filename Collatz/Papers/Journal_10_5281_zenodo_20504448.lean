import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wang, Lixin(Dirk), "Collatz Conjecture: A Geometric Construction from Euler's Formula to Fourier Isolation of +1 (V2)", 2026.

Title: Collatz Conjecture: A Geometric Construction from Euler's Formula to Fourier Isolation of +1 (V2)

Abstract (from harvested metadata, truncated):
Starting from the single line e^(iπ) = −1, this paper builds a complete geometric argument for the Collatz conjecture. Euler's formula gives cos(πn) = (−1)^n — an exact odd-even switch. The +1 in the Collatz operation, modulated by this switch, falls uniquely into the frequency-1/2 pure wave C₃ = (1−cos πz)/4, orthogonally isolated from the ÷2 and 3n channels. With +1 isolated, each odd step has frequency factor 3/2^k. The k=1 growth chain has length exactly v₂(n+1)−1 — finite for all positive integers. An infinite chain requires n = −1 (2-adic), not in Z⁺. Finite growth plus infinite shrinkage forces descent to 1. The same framework proves 5n+1 divergence and the uniqueness of p = 3. Biling...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20504448
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20504448

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wang, Lixin(Dirk), \"Collatz Conjecture: A Geometric Construction from Euler's Formula to Fourier Isolation of +1 (V2)\", Zenodo, DOI:10.5281/zenodo.20504448 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20504448
