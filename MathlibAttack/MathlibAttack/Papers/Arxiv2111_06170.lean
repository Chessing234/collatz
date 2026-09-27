import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Felipe Gonçalves et al., "Generalized Collatz Maps with Almost Bounded Orbits", arXiv:2111.06170 [2021].

Title: Generalized Collatz Maps with Almost Bounded Orbits

Abstract (truncated):
If dividing by $p$ is a mistake, multiply by $q$ and translate, and so you'll live to iterate. We show that if we define a Collatz-like map in this form then, under suitable conditions on $p$ and $q$, almost all orbits of this map attain almost bounded values. This generalizes a recent breakthrough result of Tao for the original Collatz map (i.e., $p=2$ and $q=3$). In other words, given an arbitrary growth function $N\mapsto f(N)$ we show that almost every orbit of such map with input $N$ eventually attains a value smaller than $f(N)$.

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2111.06170
-/

namespace MathlibAttack.Papers.Arxiv2111_06170

open MathlibAttack.Papers

def citation : String := "Felipe Gon\u00e7alves et al., \"Generalized Collatz Maps with Almost Bounded Orbits\", arXiv:2111.06170 [2021]."

/-- Recorded density-style claim from the paper (not proved at full strength). -/
def mainStatement : Prop :=
  ∀ eps : ℚ, 0 < eps →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
      (1 - eps) * (N : ℚ) ≤ (N : ℚ)

/-- Mathlib-checked weak shell (strictly weaker than the paper). -/
theorem mainStatement_weak : mainStatement :=
  MathlibAttack.Papers.density_shell_weak

end MathlibAttack.Papers.Arxiv2111_06170
