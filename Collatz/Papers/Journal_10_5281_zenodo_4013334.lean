import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Eduard Dyachenko, "A proof of the Collatz conjecture and connection of intervals based on ``tetrada''.", 2020.

Title: A proof of the Collatz conjecture and connection of intervals based on ``tetrada''.

Abstract (from harvested metadata, truncated):
This paper proposes be reveal the mechanism underlying systems of numbers, which suggests the existence of the Collatz conjecture (transformation) and as result a proof of the Collatz conjecture, also known as the 3x+1 problem. To determine the underlying mechanism of the Collatz conjecture, I convert the recursive-conditional Collatz transformation to a system of recursive linear transformations. Our study reveals a hidden “mechanism'' in numerical systems based on the fractional bases \( \frac{2^a}{3}\)and \( \frac{4}{3}\). It should be noted that the method of numeral systems of rational bases appeared as a result of the transition from “recursive destruction'' to “recursive conservation'...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.4013334
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_4013334

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Eduard Dyachenko, \"A proof of the Collatz conjecture and connection of intervals based on ``tetrada''.\", Zenodo (CERN European Organization for Nuclear Research), DOI:10.5281/zenodo.4013334 [2020]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_5281_zenodo_4013334
