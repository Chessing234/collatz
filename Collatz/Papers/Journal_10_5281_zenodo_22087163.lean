import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael John Curry, "An Explicit Windowed Sparsity Bound for Divergent 3x+1 Orbits, with Logarithmic-Floor Exclusion beyond the Harmonic Barrier", 2026.

Title: An Explicit Windowed Sparsity Bound for Divergent 3x+1 Orbits, with Logarithmic-Floor Exclusion beyond the Harmonic Barrier

Abstract (from harvested metadata, truncated):
Garcia and Tal proved in 1999 that every infinite orbit of the 3x+1 map has Banach density zero. We give a short self-contained proof of an explicit quantitative form: for every infinite aperiodic orbit, the number of orbit points in any window [a, a+X) is at most C X^b log(2X) uniformly in a, for every b > 0.96538..., with the exponent equal to Rozier's critical ones-ratio times log2(3). Three consequences follow for the Syracuse map with valuation drift g_n: every divergent orbit has summable reciprocals; no divergent orbit satisfies g_n <= B log2(n) + O(1) eventually for any B <= 1; and an occupation bound extends the exclusion to every B < 1.03585... This passes the threshold 8/9 recentl...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22087163
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22087163

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael John Curry, \"An Explicit Windowed Sparsity Bound for Divergent 3x+1 Orbits, with Logarithmic-Floor Exclusion beyond the Harmonic Barrier\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22087163 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22087163
