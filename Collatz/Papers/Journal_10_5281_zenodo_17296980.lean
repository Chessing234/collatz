import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Peter, Romain, "A Renormalization Group Approach to the Collatz Conjecture: A Research Program", 2025.

Title: A Renormalization Group Approach to the Collatz Conjecture: A Research Program

Abstract (from harvested metadata, truncated):
The Collatz Conjecture has resisted proof by methods ranging from number theory to dynamical systems. This paper argues that previous failures stem from an inability to bridge the gap between the local, chaotic behavior of the Collatz map and its presumed simple global outcome. We propose a new research paradigm based on an analogy with the Renormalization Group (RG) in theoretical physics. Instead of tracking the orbit of a single integer, we study the flow on the space of the affine transformations that describe the dynamics over finite blocks of steps. We define an RG operator that iteratively ”zooms out,” composing transformations at a given scale to produce an effective theory at a larg...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.17296980
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_17296980

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Peter, Romain, \"A Renormalization Group Approach to the Collatz Conjecture: A Research Program\", Zenodo, DOI:10.5281/zenodo.17296980 [2025]."

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

end Collatz.Papers.Journal_10_5281_zenodo_17296980
