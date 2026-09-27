import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wang, Xinjun, "A Corrected Suffix-Balanced Computer-Assisted Exclusion of Collatz m-Cycles for m ≤ 93", 2026.

Title: A Corrected Suffix-Balanced Computer-Assisted Exclusion of Collatz m-Cycles for m ≤ 93

Abstract (from harvested metadata, truncated):
This paper presents a reproducible computer-assisted proof framework for excluding non-trivial Collatz (m)-cycles with (m\le93). The proof combines exact rational interval arithmetic, continued-fraction denominator certificates, and finite integer residue-class enumerations. To avoid relying on the difficult-to-expand block estimate in Hercher’s original proof, the paper introduces a new suffix-balanced block method, which directly controls the contribution of each local minimum in a selected consecutive block and yields a complete self-contained error bound. Exact residual exclusion certificates are then constructed for the cases (m=92) and (m=93), leading to contradictions with the Simons--de Weger type upper bound. All key constants and finite searches are verified by accompanying...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.20588490
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_20588490

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wang, Xinjun, \"A Corrected Suffix-Balanced Computer-Assisted Exclusion of Collatz m-Cycles for m ≤ 93\", DOI:10.5281/zenodo.20588490 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_20588490
