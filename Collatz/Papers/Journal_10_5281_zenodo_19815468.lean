import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rudomanov Sergey, "The Collatz Conjecture as a Dynamical System on a Möbius Strip", 2026.

Title: The Collatz Conjecture as a Dynamical System on a Möbius Strip

Abstract (from harvested metadata, truncated):
This paper proposes a novel topological interpretation of the Collatz conjecturethrough the geometry of the M¨obius strip. We introduce an extended state space(n, σ), where σ ∈ {0, 1} represents the “side” of the strip, which flips at each oddstep. We prove that the extended map C : (n, σ) → (f(n), σ ⊕ (n mod 2)) has aunique periodic orbit of length 6, corresponding to two full rotations around theM¨obius strip.Numerical experiments for n = 1, 3, 7, 27 confirm the theoreticalfindings. A 3D visualization of trajectories on the M¨obius strip surface is presented,clearly demonstrating the transition from chaotic motion to perfect periodicity.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19815468
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19815468

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rudomanov Sergey, \"The Collatz Conjecture as a Dynamical System on a Möbius Strip\", Zenodo, DOI:10.5281/zenodo.19815468 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19815468
