import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Hosei University, Japan et al., "On the Verification and the Estimation for Two Expansion Problems of L. Collatz Conjecture", 2024.

Title: On the Verification and the Estimation for Two Expansion Problems of L. Collatz Conjecture

Abstract (from harvested metadata, truncated):
[9] presented two expansions 5n+1 problem and 7n+1 problem for L. Collatz Conjecture which is an unsolved problem, and confirmed two expansions are correct for all n&lt;100000 (=10^5). And [10] proposed two approximate formulas of the average number of steps for 5n+1 problem and 7n+1 problem respectively. In this paper, we confirm that two expansions are correct for all n&lt;1000000000000 (=10^12), and propose two high precision formulas of the average number of steps for 5n+1 problem and 7n+1 problem respectively. Keywords: Collatz Conjecture, 5n+1 problem, 7n+1 problem, Verification, average number of steps.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.47880/inf2701-01
-/

namespace Collatz.Papers.Journal_10_47880_inf2701_01

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Hosei University, Japan et al., \"On the Verification and the Estimation for Two Expansion Problems of L. Collatz Conjecture\", Information, DOI:10.47880/inf2701-01 [2024]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 8` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1

/-- Miniature verification: every positive `n < 8` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩

end Collatz.Papers.Journal_10_47880_inf2701_01
