import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Roy Burson, "On the Distribution of the First Point of Coalescence for some Collatz Trajectories", arXiv:2005.09456 [2020].

Title: On the Distribution of the First Point of Coalescence for some Collatz Trajectories

Abstract (from OpenAlex metadata, truncated):
This paper is a numerical evaluation of some trajectories of the Collatz function. Specifically, I assess the coalescence points of each integer $n\equiv 0 (\bmod{2})$ and $n\equiv 2(\bmod{3})$ through a sophisticated algorithm that has been developed to test on any different modulus classes. The data discovered illustrate that the distribution of the first point of coalescence is closely related to the solutions of some exponential diophantine equation. Afterwards, I show that the first point of coalescence of the integers $n$ and $3n+2$ appear to tend to an expected value of $4/5n$. When the algorithm was pushed to its peak estimation it has been discovered that the expected value begins to deviate from the initial estimation of $4/5n$. The first point of coalescence of the integers $n$ and $3n+2$ appear eradicate from a "step by step" point of view but from a topological point of view

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2005.09456
-/

namespace Collatz.Papers.Arxiv2005_09456

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Roy Burson, \"On the Distribution of the First Point of Coalescence for some Collatz Trajectories\", arXiv:2005.09456 [2020]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2005_09456
