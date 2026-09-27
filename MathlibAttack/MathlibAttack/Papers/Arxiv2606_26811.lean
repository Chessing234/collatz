import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Weicheng Fu et al., "Emergence of Gamma-Type Upward-Phase Statistics in the Collatz Map: An Effective Poisson Process Mechanism", arXiv:2606.26811 [2026].

Title: Emergence of Gamma-Type Upward-Phase Statistics in the Collatz Map: An Effective Poisson Process Mechanism

Abstract (truncated):
The Collatz map is a simple deterministic transformation whose orbit structure remains highly nontrivial. A recent direction-phase decomposition partitions each orbit into upward and downward steps, and numerical observations indicate that the number of upward phases, $N_{\uparrow}$, follows an approximate Gamma distribution. In this work, we provide a mechanistic explanation for this statistical regularity by modeling the occurrence of upward phases in the odd-compressed, or Syracuse, version of the Collatz map as a homogeneous Poisson process. From the mean-field logarithmic balance and the geometric distribution of $2$-adic valuations, we derive closed-form expressions for the Gamma parameters: the scale parameter $θ= 2/(2-\log_2 3)^2 \approx 11.61$ is constant, whereas the shape parameter $K$ grows logarithmically with the maximal initial value $X_0=2L+1$. We also analyze the closure

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2606.26811
-/

namespace MathlibAttack.Papers.Arxiv2606_26811

open MathlibAttack.Papers

def citation : String := "Weicheng Fu et al., \"Emergence of Gamma-Type Upward-Phase Statistics in the Collatz Map: An Effective Poisson Process Mechanism\", arXiv:2606.26811 [2026]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2606_26811
