import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hernández Reveles, Ricardo, "The Null Equivalence of the Collatz Conjecture", 2026.

Title: The Null Equivalence of the Collatz Conjecture

Abstract (from harvested metadata, truncated):
We show that the Collatz conjecture is equivalent to the arithmetic triviality 𝒩 ∩ ℤ⁺ = ∅, where 𝒩 = {−1/2 · 2^k : k ∈ ℤ} is the null orbit of the map f(x) = 3x+1 under the transparent operation x ↦ 2x. The null x₀ = −1/2 is simultaneously the algebraic fixed point of f, the Ramanujan-regularised value of the divergent accumulation Σ3ⁱ, and (up to the transparent factor 2) the unique 2-adic fixed point sustaining maximal expansion in the Syracuse map. Non-existence of non-trivial cycles follows from Baker's theorem on linear forms in logarithms. Non-existence of divergent orbits follows from the well-definedness of the asymptotic attractor at −1/2 ∉ ℤ⁺ and the 2-adic closure at −1 ∉ ℤ⁺. Since 𝒩 ∩ ℤ⁺ = ∅ is a trivial arithmetic fact, the conjecture holds. Serie I

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19874523
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19874523

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hernández Reveles, Ricardo, \"The Null Equivalence of the Collatz Conjecture\", DOI:10.5281/zenodo.19874523 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19874523
