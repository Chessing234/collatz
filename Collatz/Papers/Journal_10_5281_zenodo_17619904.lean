import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Washburn, Jonathan, "The Collatz Conjecture via Recognition Stability Audit and Canonical J-Cost Dynamics - A Structural Reduction", 2026.

Title: The Collatz Conjecture via Recognition Stability Audit and Canonical J-Cost Dynamics - A Structural Reduction

Abstract (from harvested metadata, truncated):
We develop a structural approach to the Collatz conjecture using the Recognition Stability Audit (RSA) framework and the canonical reciprocal cost functional J(x) = (1/2)(x + 1/x) - 1. The Collatz map is encoded as a sequence of multiplicative recognition events whose J-costs satisfy the d’Alembert composition law. We prove three families of results unconditionally: (1) a cycle-exclusion reduction that shows, modulo an explicit Baker-constant input, that any non-trivial Collatz cycle has minimum element exceeding 2^40; (2) a mod-8 finite-state classification of Collatz parity orbits with 8-window contraction criteria; and (3) a pessimistic tracking lemma showing that the mod-2^k automaton ne...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17619904
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17619904

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Washburn, Jonathan, \"The Collatz Conjecture via Recognition Stability Audit and Canonical J-Cost Dynamics - A Structural Reduction\", Zenodo, DOI:10.5281/zenodo.17619904 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17619904
