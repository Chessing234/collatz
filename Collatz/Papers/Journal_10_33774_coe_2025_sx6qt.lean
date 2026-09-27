import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Kevin Nwanozie, "Finite-Depth Translation Symmetries on Arithmetic Progressions for the 3n+1 Map", 2025.

Title: Finite-Depth Translation Symmetries on Arithmetic Progressions for the 3n+1 Map

Abstract (from harvested metadata, truncated):
For any positive integer N and any finite depth m we construct explicit arithmetic progressions (N + (3^k *2^t)) on which the (3n+1) map exhibits exact translation symmetry for the first m iterations. This symmetry provides an algebraic characterization of the well-known periodicity of parity sequences and clarifies the relationship between modular constraints and dynamical regularity in the Collatz problem. We show that infinite-depth translation symmetry occurs precisely when N converges to the 1-2 cycle. All results are unconditional, constructive, and provide a clean dynamical reformulation of classical modular properties.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.33774/coe-2025-sx6qt
-/

namespace Collatz.Papers.Journal_10_33774_coe_2025_sx6qt

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Kevin Nwanozie, \"Finite-Depth Translation Symmetries on Arithmetic Progressions for the 3n+1 Map\", DOI:10.33774/coe-2025-sx6qt [2025]."

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

end Collatz.Papers.Journal_10_33774_coe_2025_sx6qt
