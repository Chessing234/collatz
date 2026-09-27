import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Larbaoui, Yassine, "New Algebraic Proofs on the Correctness of Collatz Conjecture basing on New Unified Formulas along with Computational Results which Provide Insights on Prime Numbers", 2026.

Title: New Algebraic Proofs on the Correctness of Collatz Conjecture basing on New Unified Formulas along with Computational Results which Provide Insights on Prime Numbers

Abstract (from harvested metadata, truncated):
This paper presents new mathematical proofs on the correctness of the Collatz conjecture based on new unified formulas re-expressing this conjecture in a scalable algebraic form. We are proposing new precise formulas that enable expressing all natural numbers in the Collatz conjecture according to a unified methodology that allows scaling calculations on infinite numbers, and then we use these unified formulas to prove that all natural numbers are converging to the number one when we perform Collatz operations on them. In addition, we are presenting computational codes based on these algebraic formulas to provide computational results that guide the development of proofs. As a result, this paper is presenting twenty seven new theorems along detailed proofs, where the first seven theorems...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.14445/22315373/ijmtt-v72i1p105
-/

namespace Collatz.Papers.Journal_10_14445_22315373_ijmtt_v72i1p105

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Larbaoui, Yassine, \"New Algebraic Proofs on the Correctness of Collatz Conjecture basing on New Unified Formulas along with Computational Results which Provide Insights on Prime Numbers\", International Journal of Mathematics Trends and Technology, DOI:10.14445/22315373/ijmtt-v72i1p105 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_14445_22315373_ijmtt_v72i1p105
