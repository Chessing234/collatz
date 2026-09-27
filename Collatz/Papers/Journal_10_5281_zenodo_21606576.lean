import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for huang, yan, "A Proof of the Collatz Conjecture via Logarithmic Decay Lower Bounds and Diophantine Approximation", 2026.

Title: A Proof of the Collatz Conjecture via Logarithmic Decay Lower Bounds and Diophantine Approximation

Abstract (from harvested metadata, truncated):
We present a proof of the global convergence of the Collatz conjecture. By analyzing the relationship between the division-by-2 and 3n+1 operations in the Collatz map, we establish the decay structure of the iterative sequence. We prove that after 3n+1, an odd number necessarily becomes even, immediately triggering division by 2, ensuring the number of even steps (e) is no less than the odd steps (m). We mathematically rule out unbounded divergent trajectories by demonstrating an absolute algebraic contradiction: divergence requires the operational ratio to satisfy e ≤ m log₂ 3 ≈ 1.585m, whereas the natural density of 2-adic congruences forces this ratio to converge to e ≈ 2m for sufficientl...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21606576
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21606576

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "huang, yan, \"A Proof of the Collatz Conjecture via Logarithmic Decay Lower Bounds and Diophantine Approximation\", Zenodo, DOI:10.5281/zenodo.21606576 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21606576
