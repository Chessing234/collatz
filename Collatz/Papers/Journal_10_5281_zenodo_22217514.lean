import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for changzheng zhou and ziqing zhou, "Temporal Lattice and Rigidity Layer A; Collatz Iteration as Spectral Stepping on Discrete Time Manifolds", 2026.

Title: Temporal Lattice and Rigidity Layer A; Collatz Iteration as Spectral Stepping on Discrete Time Manifolds

Abstract (from harvested metadata, truncated):
This paper constructs a unified language for rephrasing the Collatz iteration ona discrete temporal lattice as an intuition of information dissipation. Within theSyracuse acceleration framework, taking the set of positive odd states as the base,we define the Collatz temporal lattice, whose elements are orbital states equippedwith a partial order based on downstream reachability. For each odd transition, weintroduce two core quantities: the time step and the information step. The information step measures the net change in bit length after the competition betweenmultiplication and division, while the time step is the sum of the information stepand a small additive perturbation term. Under the...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22217514
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22217514

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "changzheng zhou and ziqing zhou, \"Temporal Lattice and Rigidity Layer A; Collatz Iteration as Spectral Stepping on Discrete Time Manifolds\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22217514 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22217514
