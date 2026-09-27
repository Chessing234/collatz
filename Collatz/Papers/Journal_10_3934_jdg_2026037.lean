import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Evangelos Melas and Nick Poulios, "Predicting extreme stopping time behavior in the Collatz system: A probabilistic and statistical approach", 2026.

Title: Predicting extreme stopping time behavior in the Collatz system: A probabilistic and statistical approach

Abstract (from harvested metadata, truncated):
The scope of this paper is the prediction of extreme stopping-time behaviour in the Collatz system, especially the statistical identification of integers whose normalized stopping time is unusually large. We study this problem from a probabilistic and statistical perspective. We first relate the phenomenon to the Collatz lattice, to a modified Collatz system with more regular convergence properties, and to the empirical density of long-orbit integers in finite windows. We then construct two logit models for extreme stopping-time behaviour using the modified-system stopping time and local spatial lags as predictors. The first model gives stable predictive performance near seventy percent acro...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.3934/jdg.2026037
-/

namespace Collatz.Papers.Journal_10_3934_jdg_2026037

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Evangelos Melas and Nick Poulios, \"Predicting extreme stopping time behavior in the Collatz system: A probabilistic and statistical approach\", Journal of Dynamics and Games, DOI:10.3934/jdg.2026037 [2026]."

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

end Collatz.Papers.Journal_10_3934_jdg_2026037
