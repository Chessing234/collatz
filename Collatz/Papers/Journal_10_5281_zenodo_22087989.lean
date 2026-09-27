import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "A Global Occupation Conjecture for the Accelerated 3x + 1 Map", 2026.

Title: A Global Occupation Conjecture for the Accelerated 3x + 1 Map

Abstract (from harvested metadata, truncated):
Formal verification note: A companion GitHub repository containing the Lean 4/Mathlib formalization and machine-checked verification of results through Proposition 5.9 is available at the link provided below. This work develops the Effective Occupation Conjecture (EOC) for the accelerated Collatz map, asking whether the time an orbit spends near or below the critical valuation-drift line can be bounded logarithmically in its initial value. The main conceptual result is a separation of the problem into two largely distinct axes. On the drift axis, strong unconditional sparsity results constrain how a hypothetical divergent orbit can behave; incorporating the Garcia–Tal/Curry mechanism yields...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22087989
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22087989

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"A Global Occupation Conjecture for the Accelerated 3x + 1 Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22087989 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22087989
