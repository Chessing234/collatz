import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jean-Michel Munderich, "Cycle Exclusion in the Collatz Iteration via an Elementary Correction-Sum Bound", 2026.

Title: Cycle Exclusion in the Collatz Iteration via an Elementary Correction-Sum Bound

Abstract (from harvested metadata, truncated):
For the Collatz map, every candidate cycle with a odd steps and b halvingsdetermines a branch fixed point x* = C(v)/(2b − 3a), where C(v) is the correctionsum of the halving pattern v = (v1, …, va). We prove a closed-form sharp boundCmax(a,b) = 3a−1 + (3a−1 − 2a−1)·2b−a+1 (Theorem 1) and deduce twoconsequences. First, non-trivial cycles with a ≤ 2 are impossible by size alone.Second, combining the bound with the computational verification of convergencefor all n < 268 (Barina 2020) excludes all non-trivial cycles with a ≤ 110 odd steps(Theorem 2); the argument is elementary and uses no bounds on linear forms inlogarithms. An ultrametric rigidity lemma shows that integrality of the branchfixe...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22195604
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22195604

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jean-Michel Munderich, \"Cycle Exclusion in the Collatz Iteration via an Elementary Correction-Sum Bound\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22195604 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22195604
