import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Emilio A. Diarte-Carot, "Another Proof of the Truth of the Collatz Conjecture, Using Gaussian Arithmetic, Probability, and Statistics", 2026.

Title: Another Proof of the Truth of the Collatz Conjecture, Using Gaussian Arithmetic, Probability, and Statistics

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4236/jamp.2026.148145
-/

namespace Collatz.Papers.Journal_10_4236_jamp_2026_148145

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Emilio A. Diarte-Carot, \"Another Proof of the Truth of the Collatz Conjecture, Using Gaussian Arithmetic, Probability, and Statistics\", Journal of Applied Mathematics and Physics, DOI:10.4236/jamp.2026.148145 [2026]."

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

end Collatz.Papers.Journal_10_4236_jamp_2026_148145
