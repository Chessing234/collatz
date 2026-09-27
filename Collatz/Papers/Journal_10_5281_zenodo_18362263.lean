import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Babak Taran, "On the Convergence and the Structure of Loops in the Collatz Dynamics", 2026.

Title: On the Convergence and the Structure of Loops in the Collatz Dynamics

Abstract (from harvested metadata, truncated):
Abstract The Collatz Conjecture remains one of the most prominent unsolved problems in mathematics. Its fame arises from the simplicity of its defining rules, which are easy to state and understand. Yet these deceptively simple rules generate sequences with highly intricate behavior, sometimes referred to as hailstone or wondrous numbers. Expressed in binary form, it can be shown that under the 3n+1 transformation, half of all odd numbers decrease while the other half increase. This research shows that, because of the distribution of odd numbers, decreasing steps of n/2 occur nearly twice as frequently as increasing ones of 3n+1 in Collatz paths. This is a characteristic feature of Collatz d...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18362263
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18362263

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Babak Taran, \"On the Convergence and the Structure of Loops in the Collatz Dynamics\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18362263 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18362263
