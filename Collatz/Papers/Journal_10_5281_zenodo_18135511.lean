import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Daniel Augusto Jorge Zafaranich, "A Structural Resolution of the Collatz Problem via Dyadic Rigidity and Archimedean Realizability", 2026.

Title: A Structural Resolution of the Collatz Problem via Dyadic Rigidity and Archimedean Realizability

Abstract (from harvested metadata, truncated):
This work presents a structural resolution of the Collatz problem based entirely on exact arithmetic considerations.By restricting the dynamics to odd integers and reformulating the iteration in a natural index space, the Collatz map is expressed as an affine normalization process governed by dyadic valuation data. Every finite segment of an odd Collatz orbit admits a complete and exact algebraic encoding determined by explicit valuation information. At the same time, the dyadic valuation structure is rigid: at each depth there exists a unique admissible congruence class, and sufficiently deep classes are strictly non-invariant under the dynamics. As a result, indefinite concentration at large dyadic depths is structurally impossible. The decisive obstruction to infinite behavior is...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18135511
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18135511

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Daniel Augusto Jorge Zafaranich, \"A Structural Resolution of the Collatz Problem via Dyadic Rigidity and Archimedean Realizability\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18135511 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_18135511
