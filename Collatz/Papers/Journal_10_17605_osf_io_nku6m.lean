import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mendoza, José Manuel Briceño, "Demonstration of the Collatz Conjecture using Infinite Series Binary Trees in Functional Spaces (ISBT-FS)", 2026.

Title: Demonstration of the Collatz Conjecture using Infinite Series Binary Trees in Functional Spaces (ISBT-FS)

Abstract (from harvested metadata, truncated):
This work presents the demonstration of the Collatz Conjecture using the Infinite Series Binary Tree in Functional Spaces (ISBT-FS) structure. By projecting the Collatz function onto a binary decision tree, the mechanics by which numerical sets shift through recursion levels are demonstrated, establishing absolute convergence towards the (4, 2, 1) cycle. The model shows that the dynamic flow of numerical sets is strictly contractive towards the system's core, identifying the fundamental state 1 as the sole universal attractor.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.17605/osf.io/nku6m
-/

namespace Collatz.Papers.Journal_10_17605_osf_io_nku6m

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mendoza, José Manuel Briceño, \"Demonstration of the Collatz Conjecture using Infinite Series Binary Trees in Functional Spaces (ISBT-FS)\", OSF Registries, DOI:10.17605/osf.io/nku6m [2026]."

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

end Collatz.Papers.Journal_10_17605_osf_io_nku6m
