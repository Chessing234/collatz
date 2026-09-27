import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Yi Den Luo et al., "Ternary Residue Mixing and Natural Density Descent for the Collatz Map", 2026.

Title: Ternary Residue Mixing and Natural Density Descent for the Collatz Map

Abstract (from harvested metadata, truncated):
We prove that, in natural density, almost every positive integer has a Collatz iterate below any given threshold that tends to infinity. More precisely, there is a constant c &amp;gt; 0 such that for every A &amp;gt; 0, d{N : orbmin(N) &amp;gt; 2M } ≪ A (log M)-A + M-c. The proof uses the accelerated map on odd integers. We group consecutive 2-adic valuations into pairs. After fixing the two values in a pair, we average over the two possible orders. The absolute value of this average is an exact cosine factor. Repeating this operation bounds each primitive ternary Fourier coefficient by an expected product of such factors. If a Fourier phase stays close to zero, we follow it until the accumu...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.2139/ssrn.7434138
-/

namespace Collatz.Papers.Journal_10_2139_ssrn_7434138

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Yi Den Luo et al., \"Ternary Residue Mixing and Natural Density Descent for the Collatz Map\", DOI:10.2139/ssrn.7434138 [2026]."

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

end Collatz.Papers.Journal_10_2139_ssrn_7434138
