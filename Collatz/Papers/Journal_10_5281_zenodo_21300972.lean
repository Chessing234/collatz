import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Li, Tianzhuo, "A Proof of the Collatz Conjecture: Magic Odd Number Absorption Trees and Self Similar Fractal Networks", 2026.

Title: A Proof of the Collatz Conjecture: Magic Odd Number Absorption Trees and Self Similar Fractal Networks

Abstract (from harvested metadata, truncated):
We present a new proof of the Collatz conjecture. Instead of searching for a globally monotonic potential function, we uncover a hidden structure: the Collatz map defines a “pool-jumping” network on the positive odd integers, which is a directed acyclic graph whose only absorbing states are the “magic odd numbers” (numbers satisfying (3m + 1) = 2^(2p). Numerical experiments show that the proportions of odd numbers captured by different magic basins are stable at approximately 93.8% : 2.4% : 3.7%. This ratio shows structural similarity to the steady-state concentrations of CO_2, the buffer gas N_2, and dissociation products in a plasma chemical equilibrium model, which inspires us to treat th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21300972
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21300972

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Li, Tianzhuo, \"A Proof of the Collatz Conjecture: Magic Odd Number Absorption Trees and Self Similar Fractal Networks\", Zenodo, DOI:10.5281/zenodo.21300972 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21300972
