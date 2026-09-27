import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Banazadeh Farhad, "A Ternary (4k+1(2))/3 Collatz-Type Map with Two Attracting Cycles: Theoretical Analysis and Exhaustive Computational Verification up to 10⁹", 2026.

Title: A Ternary (4k+1(2))/3 Collatz-Type Map with Two Attracting Cycles: Theoretical Analysis and Exhaustive Computational Verification up to 10⁹

Abstract (from harvested metadata, truncated):
This paper studies a ternary Collatz-type map on the positive integers not divisible by 3. For an admissible integer n, the map applies an affine transformation determined by the residue class of n modulo 3 and then removes all powers of 3 from the resulting value. This produces a compressed 3-adic Collatz-type dynamical system. The theoretical analysis examines the 3-adic valuation, its distribution under a Haar-measure heuristic on the 3-adic integers, the expected number of removed factors of 3, and the corresponding average logarithmic drift. These calculations provide a heuristic explanation for the observed contracting behavior of the system but are not presented as a proof of global c...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22279137
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22279137

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Banazadeh Farhad, \"A Ternary (4k+1(2))/3 Collatz-Type Map with Two Attracting Cycles: Theoretical Analysis and Exhaustive Computational Verification up to 10⁹\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22279137 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22279137
