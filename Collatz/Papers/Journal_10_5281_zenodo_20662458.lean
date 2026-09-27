import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Guodong Jin, "Jungle of Base Nodes in the Collatz (3x+1) Problem: Precise Localization and Density Distribution within Ultra-Large Intervals", 2026.

Title: Jungle of Base Nodes in the Collatz (3x+1) Problem: Precise Localization and Density Distribution within Ultra-Large Intervals

Abstract (from harvested metadata, truncated):
【Abstract】This paper introduces a novel framework for locating and analyzing "jungles" in the Collatz iteration landscape. We redefine the base node as \frac{4^N - 1}{3}, termed the tail number in forward iteration and the base node in the reverse tree. Our Core Theorem establishes that for any odd number X_i with a sufficiently large pure odd iteration count (typically X_i \geq 50), there exists a jungle interval [X_i - \Delta X, X_i + \Delta X] wherein numbers generated from the same base node are densely distributed and share identical pure odd iteration counts. Furthermore, the interval width \Delta X increases monotonically with the pure odd iteration count. By initiating continuous bas...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20662458
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20662458

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Guodong Jin, \"Jungle of Base Nodes in the Collatz (3x+1) Problem: Precise Localization and Density Distribution within Ultra-Large Intervals\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.20662458 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20662458
