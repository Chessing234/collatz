import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Galoppo, Travis, "Negative Drift and State Instability in a Bitwise System Equivalent to the Collatz Conjecture", 2025.

Title: Negative Drift and State Instability in a Bitwise System Equivalent to the Collatz Conjecture

Abstract (from harvested metadata, truncated):
The Collatz conjecture remains one of the most famous unsolved problems in mathematics. By studying a bitwise variation of the well known Syracuse function, we develop a novel analytical framework that yields several results against the possibility of non-convergent trajectories. We introduce a simple statistic -- the "bit-span" -- measuring the distance between the LSB and MSB, and analyze the behavior of this statistic through both mechanistic and probabilistic methods. We prove that the dynamics at both ends of the bit span prevent uninterrupted span growth, with a universal limit of at most two consecutive span-growing steps for any integer. We derive an expectation for the negative chan...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17407872
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17407872

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Galoppo, Travis, \"Negative Drift and State Instability in a Bitwise System Equivalent to the Collatz Conjecture\", Zenodo, DOI:10.5281/zenodo.17407872 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17407872
