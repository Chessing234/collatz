import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for changzheng zhou and ziqing zhou, "Temporal Lattice and Rigidity Layer E; Constraint Saturation and Computational Complexity Phase Transition– The Decision Boundary of Collatz", 2026.

Title: Temporal Lattice and Rigidity Layer E; Constraint Saturation and Computational Complexity Phase Transition– The Decision Boundary of Collatz

Abstract (from harvested metadata, truncated):
This paper provides a conditional characterization of the decision boundaryassociated with the Collatz conjecture within the hierarchical framework of temporal geometry and structural rigidity. It does not seek an unconditional proof,but rather establishes a set of testable structural criteria. The core work is dividedinto two levels. First, under the joint assumptions of positive spectral gap and theG2 rigidity information compression ratio, combined with the classical numbertheoretic assumption that the Collatz map has no nontrivial cycles, we derive aconditional conclusion that the orbit reaches the constraint saturation point in finite steps; this conclusion rules out divergent orbits, b...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22245000
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22245000

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "changzheng zhou and ziqing zhou, \"Temporal Lattice and Rigidity Layer E; Constraint Saturation and Computational Complexity Phase Transition– The Decision Boundary of Collatz\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22245000 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_22245000
