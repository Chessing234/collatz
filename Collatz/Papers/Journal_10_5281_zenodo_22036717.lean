import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Javier Muñoz Romero, "A Collision-Safe 21-Polynomial Gram Reduction for Defect-Three Collatz Kernels", 2026.

Title: A Collision-Safe 21-Polynomial Gram Reduction for Defect-Three Collatz Kernels

Abstract (from harvested metadata, truncated):
A low-defect approach to hypothetical Collatz cycles leads, on the boundary branch h3 = s, to a cyclic operator with a seven-term Laurent kernel. After imposing η^−s = 2/3, two cyclic coincidences reduce this kernel to six atoms. Its Gram autocorrelation therefore contains 36 ordered-pair contributions. We prove that these contributions admit an exact grouping into 21 symbolic shift classes and, crucially, that the grouping remains valid when different symbolic classes collide in Z/sZ. Each class mass is then identified with an explicit low-degree polynomial in η, u1 = η^−h1 and u2 = η^−h2. The 21 polynomials are further identified with the 18-monomial integer coefficient table used by an ex...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22036717
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22036717

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Javier Muñoz Romero, \"A Collision-Safe 21-Polynomial Gram Reduction for Defect-Three Collatz Kernels\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22036717 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22036717
