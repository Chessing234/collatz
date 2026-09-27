import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for baoyuan duan, "A Solution of The Collatz Conjecture Problem", 2023.

Title: A Solution of The Collatz Conjecture Problem

Abstract (from harvested metadata, truncated):
Build a special identical equation, use its calculation characters to prove and search for solution of any odd converging to 1 equation through (*3+1)/2^k operation, and get a solution for this equation, which is exactly same with that got from calculating directly. Then give a specific example to verify. Thus prove the Collatz Conjecture is true. Furthermore, analysis the even and odd sequences produced by iteration calculation during the procedure of searching for solution, build a weight function model, prove it decrease progressively to 0, build another complement weight function model, prove it increase to its convergence state. Indicate that this kind of iteration calculation has determined direction, and gradually regularly converges.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.20944/preprints202301.0541.v2
-/

namespace Collatz.Papers.Journal_10_20944_preprints202301_0541_v2

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "baoyuan duan, \"A Solution of The Collatz Conjecture Problem\", Preprints.org, DOI:10.20944/preprints202301.0541.v2 [2023]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_20944_preprints202301_0541_v2
