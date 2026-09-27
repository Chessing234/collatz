import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Bélanger, Josie O. Magee, "The Collatz Conjecture: A Complete Proof via Valuation Stratification and Spectral Closure", 2026.

Title: The Collatz Conjecture: A Complete Proof via Valuation Stratification and Spectral Closure

Abstract (from harvested metadata, truncated):
ABSTRACT We establish unconditionally that no non-trivial odd positive integer cycle exists under the Collatz map n 7 → (3n + 1)/2ν2(3n+1). The proof partitions all cycle step-sequences β = (d0, d1, . . . , dL−1) by the leading 2-adic valuation d0 ≥ 1 into three mutually exclusive and exhaustive cases: d0 ≥ 3: Closed unconditionally by the Steiner lift criterion and a G7 residue-graph analysis. d0 = 2: Closed algebraically (pure-2 and single-gap tails) plus exhaustive computation over 236,600,276 step-sequences (zero hits). d0 = 1: Pure-1 and single-gap sub-cases closed algebraically for all L; multi-gap sub-case closed unconditionally for all L: a computational certificate covers 1,760,334,...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20510398
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20510398

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Bélanger, Josie O. Magee, \"The Collatz Conjecture: A Complete Proof via Valuation Stratification and Spectral Closure\", Zenodo, DOI:10.5281/zenodo.20510398 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20510398
