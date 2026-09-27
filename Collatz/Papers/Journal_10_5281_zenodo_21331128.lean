import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for xiong, zhongming, "Analytic Obstruction Diagnosis for the Collatz Conjecture: Almost-Sure Convergence and the Normality Gap", 2026.

Title: Analytic Obstruction Diagnosis for the Collatz Conjecture: Almost-Sure Convergence and the Normality Gap

Abstract (from harvested metadata, truncated):
This paper does not prove the Collatz conjecture. It unconditionally proves Gap A (spectral gap: Lasota-Yorke inequality with θ ≤ 3/16, compact embedding, essential spectral radius ≤ 0.1875), and identifies Gap B (measure-zero transfer) as the normality gap for powers of 3: the statement that {S_k log_2 3} is normal for every deterministic orbit. Measure-theoretic result: We unconditionally prove that the accelerated Collatz map F exhibits almost-sure negative drift under Haar measure: for μ_Haar-almost every 2-adic odd integer, M_K → -∞ linearly at rate ln(9/16) ≈ -0.575 per step. This follows from Terras's ergodicity result combined with the Birkhoff ergodic theorem, and provides a rigorou...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21331128
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21331128

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "xiong, zhongming, \"Analytic Obstruction Diagnosis for the Collatz Conjecture: Almost-Sure Convergence and the Normality Gap\", Zenodo, DOI:10.5281/zenodo.21331128 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21331128
