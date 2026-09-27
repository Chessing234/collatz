import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Xiangdong ZHANG, "Complete Proof of the Collatz Conjecture via the Six-Dimensional Curvature-Torsion 21 Master Equations Framework", 2026.

Title: Complete Proof of the Collatz Conjecture via the Six-Dimensional Curvature-Torsion 21 Master Equations Framework

Abstract (from harvested metadata, truncated):
This preprint v1.0 completely solves the Collatz conjecture (3x+1 problem), a famous unsolved number theory problem outside the Millennium Prize Problems, based on Zhang’s 21 six-dimensional curvature-torsion master equations. The proof embeds discrete integer iteration trajectories as continuous curves in six-dimensional Riemann-Cartan torsion manifolds. Even-number iteration corresponds to manifold curvature contraction with negative torsion divergence, while odd-number 3n+1 iteration triggers temporary SU(5) symmetry breaking and torsion field excitation. The global geometric invariant INV5 restricts the total torsion topological charge to zero, fundamentally eliminating two counterexampl...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21532488
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21532488

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Xiangdong ZHANG, \"Complete Proof of the Collatz Conjecture via the Six-Dimensional Curvature-Torsion 21 Master Equations Framework\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21532488 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21532488
