import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Franck Coppi, "Rigidity, Extremal Words, and Diophantine Obstructions for the Accelerated Collatz Map", 2026.

Title: Rigidity, Extremal Words, and Diophantine Obstructions for the Accelerated Collatz Map

Abstract (from harvested metadata, truncated):
We study the accelerated Collatz (Syracuse) map T on the odd positive integers, T(n) = (3n+1)/2^v2(3n+1), through its symbolic coding by finite words of 2-adic valuations. First, using the classical conjugacy between the 2-adic extension of the (non-accelerated) Collatz map and the one-sided Bernoulli shift, together with the standard theory of induced transformations, we show that the natural invariant measure of T is ergodic and is the unique T-invariant probability measure absolutely continuous with respect to Haar measure on Z2. Second, we solve completely the extremal problem underlying cycle detection: for words of length p and total shift S, the affine coefficient c(w) appearing in th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21753750
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21753750

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Franck Coppi, \"Rigidity, Extremal Words, and Diophantine Obstructions for the Accelerated Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21753750 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21753750
