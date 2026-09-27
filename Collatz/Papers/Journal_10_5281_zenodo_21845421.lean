import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for changzheng zhou and ziqing zhou, "Collatz Constraint Network D: Arithmetic-Energy Barriers, Hopf Fibration under Scalpel Coordinates, and the Fractal Uncertainty Principle for Odd Cycles of the Collatz Map", 2026.

Title: Collatz Constraint Network D: Arithmetic-Energy Barriers, Hopf Fibration under Scalpel Coordinates, and the Fractal Uncertainty Principle for Odd Cycles of the Collatz Map

Abstract (from harvested metadata, truncated):
This paper embeds the mixing structure of the odd steps of the Collatz mapinto scalpel coordinates centred at the binary fixed point α = −1/3, and encodesodd orbits into a finite set of directions on the unit circle via the Hopf fibration.After rigorously calibrating the local invariant nature of the scalpel depth and theone-dimensional geometric rigidity of the direction set, combined with sum-productestimates from additive combinatorics and the fractal uncertainty principle, a conditional theorem on the viscous decay of projection measures is established. Theanalysis shows that the nearly arithmetic progression structure of small arcs lies inthe critical regime of sum-product estimates, an...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.21845421
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_21845421

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "changzheng zhou and ziqing zhou, \"Collatz Constraint Network D: Arithmetic-Energy Barriers, Hopf Fibration under Scalpel Coordinates, and the Fractal Uncertainty Principle for Odd Cycles of the Collatz Map\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.21845421 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_21845421
