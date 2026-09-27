import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Neel Alkoraishi, "A Coordinate Framework for the Collatz Map via Branch Decomposition", 2026.

Title: A Coordinate Framework for the Collatz Map via Branch Decomposition

Abstract (from harvested metadata, truncated):
I present a deterministic framework for analyzing the Collatz map via abranch decomposition using coordinates (x, k, y) and branch endpoints C(x, k).Every positive integer lies on a uniquely determined branch, while even integersare represented via powers of 2.Within each branch, the coordinate sum x + y strictly decreases under iter-ation of the Collatz map. Across branches, the directed acyclic graph (DAG) ofbranch endpoints defines a branch index I(C) that strictly decreases along everypath. Combining these two monotone quantities into a lexicographic LyapunovfunctionL(n) := (I(C), x + y)ensures global descent.Branch reparameterization at transitions is bounded, preventing unboundedgrowth that could otherwise block descent. Consequently, all trajectories even-tually reach the unique...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19519932
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19519932

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Neel Alkoraishi, \"A Coordinate Framework for the Collatz Map via Branch Decomposition\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19519932 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19519932
