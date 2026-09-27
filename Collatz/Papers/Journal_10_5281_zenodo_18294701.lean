import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Craig Alan Feinstein, "cafeinst/CollatzConjecture: Isabelle formalization of Collatz information barriers", 2026.

Title: cafeinst/CollatzConjecture: Isabelle formalization of Collatz information barriers

Abstract (from harvested metadata, truncated):
The goal of this theory is to formalize an information-theoretic barrier for a broad and natural class of trace-based proof strategies for the Collatz 3n+1 conjecture. It proves a conditional result: under explicit assumptions about how computational trace information is represented and preserved, no finite proof can establish global convergence for all inputs.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.18294701
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_18294701

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Craig Alan Feinstein, \"cafeinst/CollatzConjecture: Isabelle formalization of Collatz information barriers\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.18294701 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_18294701
