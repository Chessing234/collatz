import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Banazadeh Farhad, "A Ternary (4k−1(2))/3 Collatz-Type Map: Complete 3-Adic Reduction, Algebraic Cycle Analysis, and Exhaustive Computational Verification up to 10^9", 2026.

Title: A Ternary (4k−1(2))/3 Collatz-Type Map: Complete 3-Adic Reduction, Algebraic Cycle Analysis, and Exhaustive Computational Verification up to 10^9

Abstract (from harvested metadata, truncated):
This paper studies a ternary Collatz-type dynamical system on the positive integers not divisible by 3. For each admissible positive integer x, let r(x) be its nonzero residue modulo 3, so that r(x) is either 1 or 2. The accelerated map is defined by T(x) = (4x − r(x)) / 3^v, where v is the exact exponent of 3 dividing 4x − r(x). Thus, all available factors of 3 are removed at every iteration. The paper develops the two residue branches of the map, exact inverse branches, the associated 3-adic valuation structure, and an algebraic cycle equation relating periodic orbits to the balance between powers of 4 and powers of 3. Three positive attractors were observed in the finite computation: the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22662979
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22662979

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Banazadeh Farhad, \"A Ternary (4k−1(2))/3 Collatz-Type Map: Complete 3-Adic Reduction, Algebraic Cycle Analysis, and Exhaustive Computational Verification up to 10^9\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22662979 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22662979
