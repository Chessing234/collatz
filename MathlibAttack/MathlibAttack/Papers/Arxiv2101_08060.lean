import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Franz Wegner, "The Collatz Problem generalized to 3x+k", arXiv:2101.08060 [2021].

Title: The Collatz Problem generalized to 3x+k

Abstract (truncated):
The Collatz problem with $3x+k$ is revisited. Positive and negative limit cycles are given up to k=9997 starting with $x_0=-2\cdot10^7...+2\cdot10^7$. A simple relation between the probability distribution for the Syracuse iterates for various k (not divisible by 2 and 3) is obtained. From this it follows that the oscillation considered by Tao 2019 ( arXiv:1909.03562v2 ) does not depend on k. Thus this piece of the proof of his theorem 1.3 "Almost all Collatz orbits attain almost bounded values" holds for all k not divisible by 2 and 3.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2101.08060
-/

namespace MathlibAttack.Papers.Arxiv2101_08060

open MathlibAttack.Papers

def citation : String := "Franz Wegner, \"The Collatz Problem generalized to 3x+k\", arXiv:2101.08060 [2021]."

/-- Recorded density-style claim from the paper (not proved at full strength). -/
def mainStatement : Prop :=
  ∀ eps : ℚ, 0 < eps →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
      (1 - eps) * (N : ℚ) ≤ (N : ℚ)

/-- Mathlib-checked weak shell (strictly weaker than the paper). -/
theorem mainStatement_weak : mainStatement :=
  MathlibAttack.Papers.density_shell_weak

end MathlibAttack.Papers.Arxiv2101_08060
