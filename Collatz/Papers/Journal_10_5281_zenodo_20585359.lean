import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Belafsahi, Mourad, "A New Analytical Framework for the Collatz Conjecture Using Higher-Order Harmonic Series and Modular Decoupling", 2026.

Title: A New Analytical Framework for the Collatz Conjecture Using Higher-Order Harmonic Series and Modular Decoupling

Abstract (from harvested metadata, truncated):
This research note presents a novel analytical approach to the Collatz (3n+1) conjecture by mapping its dynamical behavior onto inverse higher-order harmonic series. Instead of traditionally tracking individual trajectories, this framework freezes the temporal dynamics into a spatial structure using modular arithmetic (mod 9). We define a single unified algebraic map and construct bounded k-th order fractional series. This framework proves that regardless of the peak expansion of a trajectory, the resulting infinite series converges predictably due to an absolute structural attractor rooted at the closed-loop cycle {4, 2, 1}.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20585359
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20585359

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Belafsahi, Mourad, \"A New Analytical Framework for the Collatz Conjecture Using Higher-Order Harmonic Series and Modular Decoupling\", Zenodo, DOI:10.5281/zenodo.20585359 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_20585359
