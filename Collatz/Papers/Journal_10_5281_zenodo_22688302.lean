import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for seif waqas, "A Farey Mediant Refinement of the Diophantine Lower Bound on Collatz Cycle Lengths", 2026.

Title: A Farey Mediant Refinement of the Diophantine Lower Bound on Collatz Cycle Lengths

Abstract (from harvested metadata, truncated):
Building on the product-telescoping bound 0 < n/m − log₂3 < 1/(3ln2·x₀) for hypothetical non-trivial Collatz cycles, we investigate whether a Farey-mediant refinement — exploiting that n/m approaches log₂3 from above only — can improve the lower bound on m beyond the classical two-sided Legendre–Khinchin result. A naive application suggests m ≥ 137,528,045,312, but a complete case analysis reveals an intermediate semiconvergent that limits the fully rigorous conclusion to m ≥ 72,057,431,991 under x₀ ≥ 2⁷¹. We report this honestly, including the gap between the optimistic and justified bounds, and separately record the independently published bound n ≥ 217,976,794,617 (Bouhamidi, 2026). Note...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22688302
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22688302

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "seif waqas, \"A Farey Mediant Refinement of the Diophantine Lower Bound on Collatz Cycle Lengths\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22688302 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22688302
