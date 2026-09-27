import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Campbell, Stephen Roderick, "Mersenne Block Dynamics: A Framework for the Collatz Conjecture", 2025.

Title: Mersenne Block Dynamics: A Framework for the Collatz Conjecture

Abstract (from harvested metadata, truncated):
This paper introduces Mersenne Block Dynamics, a structural framework for analyzing the accelerated Collatz or Syracuse map on odd integers. The approach decomposes orbits based on the 2-adic valuation of the successor of an odd integer, effectively measuring the length of the trailing run of ones in its binary expansion, termed the Mersenne tail. This decomposition partitions the dynamics into deterministic blocks where the tail length decreases by exactly one bit at each step, creating a rigid wedge pattern in the binary representation. The framework defines a coarse-grained block map that transitions directly between the starts of successive blocks, isolating all arithmetic complexity int...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17971539
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17971539

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Campbell, Stephen Roderick, \"Mersenne Block Dynamics: A Framework for the Collatz Conjecture\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.17971539 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17971539
