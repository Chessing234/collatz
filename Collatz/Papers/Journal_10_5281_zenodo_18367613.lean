import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Saito, Yuya, "A Topological Proof of the Collatz Conjecture via Discrete Height Descent in 2-adic Space", 2026.

Title: A Topological Proof of the Collatz Conjecture via Discrete Height Descent in 2-adic Space

Abstract (from harvested metadata, truncated):
This paper provides a formal proof of the Collatz Conjecture (the 3n + 1 problem) by employing a topological approach within the 2-adic metric space. By defining a discrete“height” function h(n) based on 2-adic valuation, we demonstrate that the Collatz map C(n) induces a deterministic descent dynamics. We prove that every forward orbit {Ck(n)} is eventually contained within the compact invariant subspace K = {1, 2, 4}. This convergence is shown to be a topological necessity arising from the connectivity of the 2-adic binary tree, ensuring that all trajectories terminate in the {1, 4, 2} cycle.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18367613
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18367613

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Saito, Yuya, \"A Topological Proof of the Collatz Conjecture via Discrete Height Descent in 2-adic Space\", Zenodo, DOI:10.5281/zenodo.18367613 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18367613
