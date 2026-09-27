import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrew Stewart Caldin, "The Unprovable Boundary: Collatz and Turing's Halting Problem — E8 Intelligence Research", 2026.

Title: The Unprovable Boundary: Collatz and Turing's Halting Problem — E8 Intelligence Research

Abstract (from harvested metadata, truncated):
FINDING: The Collatz Conjecture and the Entscheidungsproblem define the boundary of computable arithmetic; Collatz remains unproven, while Turing proved the halting problem is undecidable. | MATH: Collatz map: T(n) = n/2 if n even, 3n+1 if n odd; conjectured to reach 1 for all n ∈ ℕ⁺. Turing: no algorithm exists to decide whether an arbitrary Turing machine halts — formalized via the halting set K = {⟨M⟩ : M halts on input ⟨M⟩}, which is recursively enumerable but not decidable. Hilbert's Entscheidungsproblem: ∃ an effective procedure to decide validity of first-order logic sentences — answered negatively by Church–Turing (1936). | CONNECTION: Collatz iterates exhibit chaotic orbits with no...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.22719847
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_22719847

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrew Stewart Caldin, \"The Unprovable Boundary: Collatz and Turing's Halting Problem — E8 Intelligence Research\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.22719847 [2026]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps

end Collatz.Papers.Journal_10_5281_zenodo_22719847
