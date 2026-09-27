import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Elias De Jesus, "Valuation-Mean Classification for the Accelerated Collatz Map: A Conditional Lyapunov Criterion, the Critical Boundary log2 3, and the Cycle Window", 2026.

Title: Valuation-Mean Classification for the Accelerated Collatz Map: A Conditional Lyapunov Criterion, the Critical Boundary log2 3, and the Cycle Window

Abstract (from harvested metadata, truncated):
Ongoing formalization and the latest developments in this research program are available in the EOC Lean verification repository: https://github.com/innerlightr-wq/eoc-lean-verification This revised note studies the accelerated odd-only Collatz map using the logarithmic Lyapunov potential V(m)=\log_2 m. The main rigorous result is a conditional convergence criterion: if the global Cesàro mean of the 2-adic valuation discharges satisfies \liminf \bar D_N>\log_2(10/3), then the orbit reaches 1 in finite time. The paper does not prove the Collatz conjecture. Instead, it identifies the valuation profile that any hypothetical non-terminating orbit would have to maintain: such an orbit must satisf...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18149680
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18149680

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Elias De Jesus, \"Valuation-Mean Classification for the Accelerated Collatz Map: A Conditional Lyapunov Criterion, the Critical Boundary log2 3, and the Cycle Window\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18149680 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18149680
