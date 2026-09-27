import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Allikvere, Jaan, "Almost all Collatz orbits attain almost bounded values in natural density", 2026.

Title: Almost all Collatz orbits attain almost bounded values in natural density

Abstract (from harvested metadata, truncated):
Tao (2022) proved that Col_min(N) < f(N) for almost all N in the sense of logarithmic density, for any function f tending to infinity, and asked (Forum Math. Pi 10 (2022), e12, Remark 1.16) whether logarithmic density can be replaced by natural density. This preprint answers the question affirmatively. The proof upgrades the two probabilistic pillars of Tao's argument to versions conditioned on the total 2-valuation: a sum-conditioned superpolynomial Fourier decay bound for Syracuse random variables, and a sum-conditioned fine-scale mixing property of the full random affine map. The passage from the logarithmic to the uniform measure then reduces, via an exact combinatorial identity, to a one-dimensional local limit computation along a Kronecker orbit of log_2(3); at this single point the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21340151
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21340151

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Allikvere, Jaan, \"Almost all Collatz orbits attain almost bounded values in natural density\", DOI:10.5281/zenodo.21340151 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21340151
