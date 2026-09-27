import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Juan Gabriel Molina, "Conditional Results on the Collatz Conjecture: A Compactification Criterion for Cycle Uniqueness, a Quantitative Divergence Bound, and the Non-Viability of KAM Methods", 2026.

Title: Conditional Results on the Collatz Conjecture: A Compactification Criterion for Cycle Uniqueness, a Quantitative Divergence Bound, and the Non-Viability of KAM Methods

Abstract (from harvested metadata, truncated):
We establish four results on the Collatz conjecture. Theorem 1: cycle uniqueness follows from a single topological condition (the Compactification Condition) on the Alexandroff compactification of a topology introduced by Santana (arXiv:2601.03297v3, 2026), via a parity argument verified for all cycle structure parameters. Theorem 2: a quantitative divergence bound showing that divergence requires the 2-adic valuation v₂(3n+1) = 1 at asymptotic frequency exceeding p* ≈ 0.7075 among odd steps, when the natural rate is 0.5. Theorem 3: if both conditions hold, the Collatz conjecture is true. Theorem 4 (unconditional): the Syracuse map is non-injective on odd integers, with an explicit infinite...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19054987
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19054987

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Juan Gabriel Molina, \"Conditional Results on the Collatz Conjecture: A Compactification Criterion for Cycle Uniqueness, a Quantitative Divergence Bound, and the Non-Viability of KAM Methods\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19054987 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19054987
