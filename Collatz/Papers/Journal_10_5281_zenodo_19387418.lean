import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Michael Ross, "Loop Structure of Collatz-Type Functions 3x+n: A Conjugacy Theorem and Powers of Three", 2026.

Title: Loop Structure of Collatz-Type Functions 3x+n: A Conjugacy Theorem and Powers of Three

Abstract (from harvested metadata, truncated):
We record two elementary structural facts about the loop behavior of the Collatz-type maps x ↦ 3x+n for odd n, working with the odd-only reduced map. First, the net displacements around any cycle sum to zero; this is a pure arithmetic identity, and we note that inverse pairs — odd inputs whose displacements are equal in magnitude and opposite in sign — are one mechanism by which a cycle can realize the required cancellation. Second, and the main point, we prove a conjugacy identity f_n(nx) = n · f_1(x) valid for all odd n and odd x, and show that when n = 3^k a 3-adic confinement forces every orbit eventually onto the sublattice on which this identity is an exact rescaling of 3x+1. Consequen...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19387418
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19387418

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Michael Ross, \"Loop Structure of Collatz-Type Functions 3x+n: A Conjugacy Theorem and Powers of Three\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19387418 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19387418
