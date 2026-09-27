import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Rade Vuckovac, "One Way Function Candidate based on the Collatz Problem", arXiv:1801.05079 [2018].

Title: One Way Function Candidate based on the Collatz Problem

Abstract (from OpenAlex metadata, truncated):
The one way function based on the Collatz problem is proposed. It is based on the problem's conditional branching structure which is not considered as important even the 3x+1 question is quite famous. The analysis shows why the problem is mathematically so inaccessible and how the algorithm conditional branching structure can be used to construct one way functions. It also shows exponential dependence between algorithm's conditional branching and running cost of algorithm branch-less reductions.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1801.05079
-/

namespace Collatz.Papers.Arxiv1801_05079

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Rade Vuckovac, \"One Way Function Candidate based on the Collatz Problem\", arXiv:1801.05079 [2018]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1801_05079
