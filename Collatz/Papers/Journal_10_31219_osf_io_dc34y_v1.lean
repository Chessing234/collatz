import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Younghwan Yun, "A Structural Proof of the Collatz Conjecture via Injectivity and  Recursive Decay", 2025.

Title: A Structural Proof of the Collatz Conjecture via Injectivity and  Recursive Decay

Abstract (from harvested metadata, truncated):
We present a structural proof of the Collatz conjecture by rigorously analyzing the recursive mapping of odd integers. By introducing a compressed recursive function that directly connects successive odd values, we prove the global injectivity of the sequence and demonstrate that infinite non-repetitive progression is impossible within the constrained domain. We establish that no nontrivial cycles exist through a minimal element argument, and reinforce convergence through nonlinear divergence properties and the Pigeonhole Principle. Consequently, every sequence must inevitably intersect the canonical cycle (1 → 4 → 2 →1), thus conclusively demonstrating the validity of the Collatz conjecture...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.31219/osf.io/dc34y_v1
-/

namespace Collatz.Papers.Journal_10_31219_osf_io_dc34y_v1

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Younghwan Yun, \"A Structural Proof of the Collatz Conjecture via Injectivity and  Recursive Decay\", DOI:10.31219/osf.io/dc34y_v1 [2025]."

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

end Collatz.Papers.Journal_10_31219_osf_io_dc34y_v1
