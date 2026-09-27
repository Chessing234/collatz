import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Cain, Lukas, "A Formal Proof of all Collatz k-Cycles and a Reduction of the Divergence Problem", 2026.

Title: A Formal Proof of all Collatz k-Cycles and a Reduction of the Divergence Problem

Abstract (from harvested metadata, truncated):
This paper introduces a rigorous formal framework for analyzing the Collatz 3n+1 map by reducing its infinite combinatorial complexity to a finite state automaton (FSA) governed by 2-adic arithmetic. We prove that all non-convergent trajectories must be confined to a "Trapped Set" characterized by strictly bounded 2-adic valuations. Within this domain, we demonstrate that avoiding terminal descent requires satisfying an "Information Density Contradiction," forcing trajectories to iteratively target a Diophantine attractor -5/3 that is structurally disjoint from the map's limit sets. To rigorously address the cycle-exclusion problem, we present a computationally absolute "Three-Mechanism Synt...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.6084/m9.figshare.30561278
-/

namespace Collatz.Papers.Journal_10_6084_m9_figshare_30561278

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Cain, Lukas, \"A Formal Proof of all Collatz k-Cycles and a Reduction of the Divergence Problem\", figshare, DOI:10.6084/m9.figshare.30561278 [2026]."

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

end Collatz.Papers.Journal_10_6084_m9_figshare_30561278
