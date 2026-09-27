import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for C. Mike Rubendall, "A Direct Proof of the Collatz Conjecture Via 2-adic Normalization", 2026.

Title: A Direct Proof of the Collatz Conjecture Via 2-adic Normalization

Abstract (from harvested metadata, truncated):
Abstract. We present a proof of the Collatz Conjecture within ZFC. By introducing a single-rule iteration f(x) = 3x + 2^(𝝂₂(x)), where 𝝂₂(x) denotes the largest exponent, n, such that 2ⁿ | x, we show that the Collatz dynamics reduce to a successor map that is strictly increasing along each forward orbit (orbitwise/time injective). Using orbitwise injectivity, nontrivial cycles are ruled out. An exact algebraic covariant relation to stopping time invariance, T(x) = 4x + 1, is identified; 3Tⁿ(x) + 1 = 4ⁿ(3x + 1) forcing absorption into the power of two ladder, we prove that all positive integers eventually reach 1 in finite time.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22005893
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22005893

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "C. Mike Rubendall, \"A Direct Proof of the Collatz Conjecture Via 2-adic Normalization\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22005893 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22005893
