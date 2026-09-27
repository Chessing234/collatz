import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Dyachenko, Eduard, "Structural prohibition of macro-cycles in the Collatz conjecture: projective matrix dynamics and palindromic symmetry", 2026.

Title: Structural prohibition of macro-cycles in the Collatz conjecture: projective matrix dynamics and palindromic symmetry

Abstract (from harvested metadata, truncated):
The normalized odd Collatz map is analyzed as a discrete dynamical system in the ring of 2-adic integers. It is proved that the existence of periodic macro-cycles is equivalent to the solvability of an overdetermined Diophantine system governed by an ensemble of projective $2 \times 2$ matrices. The bidirectional phase invariance of this matrix ensemble strictly requires the bitwise palindromic symmetry of local 2-adic configurations. It is shown that for cores of width $L \ge 9$, the fundamental incommensurability between left-sided multiplicative expansion and right-sided additive truncation deterministically breaks this symmetry. Within the kinematic corridor of the orbit, this structural...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19064954
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19064954

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Dyachenko, Eduard, \"Structural prohibition of macro-cycles in the Collatz conjecture: projective matrix dynamics and palindromic symmetry\", Zenodo, DOI:10.5281/zenodo.19064954 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19064954
