import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for seif waqas, "Rigorous Diophantine Lower Bounds on Collatz Cycle Lengths via Exact Product Telescoping and Verified Continued Fraction Convergents", 2026.

Title: Rigorous Diophantine Lower Bounds on Collatz Cycle Lengths via Exact Product Telescoping and Verified Continued Fraction Convergents

Abstract (from harvested metadata, truncated):
Assuming x₀ ≥ M₀ = 2⁷¹ ≈ 2.3611832414348 × 10²¹, we prove rigorous Diophantine lower bounds on the lengths m (odd steps) and n (total steps) of any hypothetical non-trivial Collatz cycle. By employing the exact product telescoping identity ∏(3 + 1/xⱼ) = 2ⁿ and the sharp logarithmic distance bound 0 < n/m − log₂3 < 1/(3ln2·x₀), we eliminate reliance on auxiliary partial sum bounds. Using a finite descent proof for the minimum distance property of type-II convergents together with a strict monotonic index selection criterion, we determine the optimal index k*=21, yielding the conditional lower bounds m ≥ 65,470,613,321 odd steps and n ≥ 103,768,467,013 total steps. Note on prior art: Hercher &...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22688036
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22688036

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "seif waqas, \"Rigorous Diophantine Lower Bounds on Collatz Cycle Lengths via Exact Product Telescoping and Verified Continued Fraction Convergents\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22688036 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22688036
