import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "A Lyapunov Criterion for the Accelerated Collatz Map: Valuation Means, Leakage Coordinates, and the Counterexample Profile", 2026.

Title: A Lyapunov Criterion for the Accelerated Collatz Map: Valuation Means, Leakage Coordinates, and the Counterexample Profile

Abstract (from harvested metadata, truncated):
This revised note studies the accelerated odd-only Collatz map using the logarithmic Lyapunov potential (V(m)=\log_2 m). The main rigorous result is a conditional convergence criterion: if the global Cesàro mean of the 2-adic valuation discharges satisfies (\liminf \bar D_N>\log_2(10/3)), then the orbit reaches (1) in finite time. The paper does not prove the Collatz conjecture. Instead, it identifies the valuation profile that any hypothetical non-terminating orbit would have to maintain: such an orbit must satisfy (\liminf \bar D_N\leq\log_2(10/3)). The revision clarifies the distinction between exact algebra, uniform-residue heuristic drift, leakage-coordinate reparameterization, and the remaining pointwise orbit obstruction.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20462324
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20462324

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"A Lyapunov Criterion for the Accelerated Collatz Map: Valuation Means, Leakage Coordinates, and the Counterexample Profile\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20462324 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20462324
