import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Jacques Arsac, "Algorithmes pour vérifier la conjecture de Syracuse", 1987.

Title: Algorithmes pour vérifier la conjecture de Syracuse

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.1051/ita/1987210100031/pdf
-/

namespace Collatz.Papers.Journal_10_1051_ita_1987210100031_pdf

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Jacques Arsac, \"Algorithmes pour vérifier la conjecture de Syracuse\", Springer Link (Chiba Institute of Technology), DOI:10.1051/ita/1987210100031/pdf [1987]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_1051_ita_1987210100031_pdf
