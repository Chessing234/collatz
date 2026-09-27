import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eddie Chin, "The Collatz Conjecture via the Klein Bottle Manifold", 2026.

Title: The Collatz Conjecture via the Klein Bottle Manifold

Abstract (from harvested metadata, truncated):
We prove the Collatz conjecture: every positive integer eventually reaches 1 under the Collatz iteration T(n)=n/2 (n even) and T(n)=3n+1 (n odd). The proof has three parts. Part I establishes the Klein bottle structure K_C governing the Collatz dynamics. The Collatz fixed-point equation 3x+1=2^k·x has two canonical solutions: x=1 at k=2 (the Collatz fixed point) and x=1/5 at k=3 (the ramified prime of ℚ(√5), structurally inaccessible from positive integers). These are the roots of the Collatz characteristic quadratic Q_C=5x²−6x+1=(5x−1)(x−1). The involution w_C: x↦6/5−x swaps the two roots and has fixed locus x=3/5. Q_C is w_C-symmetric: Q_C(x)=Q_C(6/5−x) for all x, proved algebraically. The...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19375550
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19375550

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eddie Chin, \"The Collatz Conjecture via the Klein Bottle Manifold\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.19375550 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19375550
