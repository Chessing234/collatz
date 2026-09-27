import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Pivetta, Adrian Neill, "The Collatz Conjecture (3n+1 Problem) - A Topological Proof of Trajectory Convergence in the 3n+1 Mapping.", 2026.

Title: The Collatz Conjecture (3n+1 Problem) - A Topological Proof of Trajectory Convergence in the 3n+1 Mapping.

Abstract (from harvested metadata, truncated):
This paper provides a formal solution to the Collatz Conjecture by defining the sequence as a Topological Super-Martingale. By establishing a "Metric Floor" and a "Scaling Gap" within a quantized manifold, we prove that infinite divergence is mathematically impossible. The result demonstrates that all integer trajectories are mechanically forced to decay into the stable 1, 2, 4 ground-state loop. The math found in the document 3n1 V2 is based off of the math found in this framework: https://doi.org/10.5281/zenodo.19355171

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19420792
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19420792

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Pivetta, Adrian Neill, \"The Collatz Conjecture (3n+1 Problem) - A Topological Proof of Trajectory Convergence in the 3n+1 Mapping.\", Zenodo, DOI:10.5281/zenodo.19420792 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19420792
