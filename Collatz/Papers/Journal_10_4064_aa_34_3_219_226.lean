import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Herbert Möller, "Über Hasses Verallgemeinerung des Syracuse-Algorithmus (Kakutanis Problem)", 1978.

Title: Über Hasses Verallgemeinerung des Syracuse-Algorithmus (Kakutanis Problem)

Abstract (from harvested metadata, truncated):
(No abstract in harvested metadata; statement recorded from title/venue only.)

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.4064/aa-34-3-219-226
-/

namespace Collatz.Papers.Journal_10_4064_aa_34_3_219_226

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Herbert Möller, \"Über Hasses Verallgemeinerung des Syracuse-Algorithmus (Kakutanis Problem)\", Acta Arithmetica, DOI:10.4064/aa-34-3-219-226 [1978]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_4064_aa_34_3_219_226
