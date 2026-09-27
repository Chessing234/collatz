import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Lin Guan, "Complete Iteration Theory of the Collatz Conjecture: Bidirectional Nested Accumulation Recursion and Closed-Loop Diophantine Equation Derivation", 2026.

Title: Complete Iteration Theory of the Collatz Conjecture: Bidirectional Nested Accumulation Recursion and Closed-Loop Diophantine Equation Derivation

Abstract (from harvested metadata, truncated):
Traditional studies of the Collatz conjecture rely on stepwise iteration and immediate division by 2, which only provides empirical numerical convergence. This paper establishes a novel nested recursion framework: all odd-layer \(3N+1\) iterations are fully accumulated first, all powers of 2 are globally collected, and division operations are uniformly decomposed in reverse order. Through bidirectional equivalent derivation, we rigorously recover the core Diophantine equation of the Collatz system, form a self-consistent closed-loop iteration structure, and explain the essential mechanism of orbital convergence without divergence or abnormal cycles. This supplementary manuscript builds on th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21812940
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21812940

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Lin Guan, \"Complete Iteration Theory of the Collatz Conjecture: Bidirectional Nested Accumulation Recursion and Closed-Loop Diophantine Equation Derivation\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21812940 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21812940
