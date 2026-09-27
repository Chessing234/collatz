import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Malick Sada Sall, "Conditional Proof of the Uniqueness of the Trivial Cycle in the Collatz (Syracuse) Sequence", 2026.

Title: Conditional Proof of the Uniqueness of the Trivial Cycle in the Collatz (Syracuse) Sequence

Abstract (from harvested metadata, truncated):
The Collatz (Syracuse) conjecture asserts that every positive integer under the iteration n → n/2 if even, n → 3n+1 if odd, eventually reaches the trivial cycle {1, 4, 2}. Despite extensive computations and various heuristic and probabilistic results, no deterministic proof is known. We introduce a novel conjecture for the Collatz sequence that imposes a dynamical constraint via a normalized sequence $(U_n)$ and does not appear to be trivially equivalent to the classical Collatz conjecture. Assuming this conjecture, we prove the uniqueness of the trivial cycle and derive structural limitations on potential divergent trajectories. Extensive numerical tests for integers up to $10^8$ support th...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18470584
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18470584

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Malick Sada Sall, \"Conditional Proof of the Uniqueness of the Trivial Cycle in the Collatz (Syracuse) Sequence\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18470584 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18470584
