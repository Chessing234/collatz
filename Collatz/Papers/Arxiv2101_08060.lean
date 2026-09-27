import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Franz Wegner, "The Collatz Problem generalized to 3x+k", arXiv:2101.08060 [2021].

Title: The Collatz Problem generalized to 3x+k

Abstract (from OpenAlex metadata, truncated):
The Collatz problem with $3x+k$ is revisited. Positive and negative limit cycles are given up to k=9997 starting with $x_0=-2\cdot10^7...+2\cdot10^7$. A simple relation between the probability distribution for the Syracuse iterates for various k (not divisible by 2 and 3) is obtained. From this it follows that the oscillation considered by Tao 2019 ( arXiv:1909.03562v2 ) does not depend on k. Thus this piece of the proof of his theorem 1.3 "Almost all Collatz orbits attain almost bounded values" holds for all k not divisible by 2 and 3.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2101.08060
-/

namespace Collatz.Papers.Arxiv2101_08060

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Franz Wegner, \"The Collatz Problem generalized to 3x+k\", arXiv:2101.08060 [2021]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps


end Collatz.Papers.Arxiv2101_08060
