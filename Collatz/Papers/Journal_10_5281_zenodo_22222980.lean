import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Osama Amer, "On the Global Convergence of the 3n+1 Problem: A Hybrid Telescoping Sieve, Diophantine Metric Gap, and Automated SMT Refutation of Non-Trivial Cycles", 2026.

Title: On the Global Convergence of the 3n+1 Problem: A Hybrid Telescoping Sieve, Diophantine Metric Gap, and Automated SMT Refutation of Non-Trivial Cycles

Abstract (from harvested metadata, truncated):
The Collatz (3n+1) conjecture asserts that the iterative discrete piecewise map T(n) = n/2 if n is even and T(n) = (3n+1)/2 if n is odd universally converges to the global attractor x_final = 1 for all positive integers. In this monograph, we establish an exhaustive algebraic and automated constraint framework that refutes the existence of non-trivial cycles and infinite divergence. We prove that all closed periodic orbits of k odd steps and m even divisions correspond exactly to integer solutions of the Telescoping Fixed-Point Identity x0 = C / (2^m - 3^k). Through a multi-stage parity and residue sieve, candidate cycle generators are restricted to the prime wheel {6k ± 1}. We derive the un...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22222980
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22222980

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Osama Amer, \"On the Global Convergence of the 3n+1 Problem: A Hybrid Telescoping Sieve, Diophantine Metric Gap, and Automated SMT Refutation of Non-Trivial Cycles\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22222980 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_22222980
