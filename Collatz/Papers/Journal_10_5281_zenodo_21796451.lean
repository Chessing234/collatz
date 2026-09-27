import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Aleh Kavalenka, "A TOPOLOGICAL PROOF OF THE COLLATZ CONJECTURE BY FINITE SEQUENTIAL GRAPH TRANSFORMATION", 2026.

Title: A TOPOLOGICAL PROOF OF THE COLLATZ CONJECTURE BY FINITE SEQUENTIAL GRAPH TRANSFORMATION

Abstract (from harvested metadata, truncated):
Abstract. In this paper, we present a complete, constructive proof of the Collatzconjecture (3n + 1 problem). The proof is based on the topological transformationof a provably strictly monotonically decreasing, infinite tree with a scaling factor ofK = 1.5 into the classical Collatz graph (K = 3). By establishing a sequential, locallyfinite reconstruction algorithm, it is proven that the tree property (acyclicity andglobal connectedness to the root 1) remains invariant in every single transformationstep. Infinite trajectories as well as the emergence of closed cycles are rigorouslyexcluded for all parameters K < 4.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21796451
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21796451

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Aleh Kavalenka, \"A TOPOLOGICAL PROOF OF THE COLLATZ CONJECTURE BY FINITE SEQUENTIAL GRAPH TRANSFORMATION\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21796451 [2026]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end Collatz.Papers.Journal_10_5281_zenodo_21796451
