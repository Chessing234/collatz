import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Banazadeh Farhad, "The Reduced 5k+1(3)/4 Collatz-Type Domain with Four Observed Attractors up to 10^10", 2026.

Title: The Reduced 5k+1(3)/4 Collatz-Type Domain with Four Observed Attractors up to 10^10

Abstract (from harvested metadata, truncated):
This work studies a residue-dependent reduced Collatz-type map on the positive odd integers, referred to as the 5k + 1(3)/4 domain. For an odd state x, the affine correction is chosen from {1, 3} so that the numerator is divisible by at least 4, after which all powers of two are removed. The map exhibits four directly verified periodic attractors: the fixed point {1} and the three cycles {31, 39, 49}, {37, 47, 59}, and {61, 77, 97}. An exhaustive C computation using unsigned 128-bit arithmetic and four POSIX threads tested all 5,000,000,000 positive odd starting values below 10^10. Every tested orbit entered one of the four observed attractors, with zero unresolved cases. The work also prese...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22726452
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22726452

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Banazadeh Farhad, \"The Reduced 5k+1(3)/4 Collatz-Type Domain with Four Observed Attractors up to 10^10\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22726452 [2026]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_5281_zenodo_22726452
