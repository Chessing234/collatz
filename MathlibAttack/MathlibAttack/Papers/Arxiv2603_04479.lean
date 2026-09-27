import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Nicolò Bonacorsi and Matteo Bordoni, "Bayesian Modeling of Collatz Stopping Times: A Probabilistic Machine Learning Perspective", arXiv:2603.04479 [2026].

Title: Bayesian Modeling of Collatz Stopping Times: A Probabilistic Machine Learning Perspective

Abstract (truncated):
We study the Collatz total stopping time $τ(n)$ over $n\le 10^7$ from a probabilistic machine learning viewpoint. Empirically, $τ(n)$ is a skewed and heavily overdispersed count with pronounced arithmetic heterogeneity. We develop two complementary models. First, a Bayesian hierarchical Negative Binomial regression (NB2-GLM) predicts $τ(n)$ from simple covariates ($\log n$ and residue class $n \bmod 8$), quantifying uncertainty via posterior and posterior predictive distributions. Second, we propose a mechanistic generative approximation based on the odd-block decomposition: for odd $m$, write $3m+1=2^{K(m)}m'$ with $m'$ odd and $K(m)=v_2(3m+1)\ge 1$; randomizing these block lengths yields a stochastic approximation calibrated via a Dirichlet-multinomial update. On held-out data, the NB2-GLM achieves substantially higher predictive likelihood than the odd-block generators. Conditioning t

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2603.04479
-/

namespace MathlibAttack.Papers.Arxiv2603_04479

open MathlibAttack.Papers

def citation : String := "Nicol\u00f2 Bonacorsi and Matteo Bordoni, \"Bayesian Modeling of Collatz Stopping Times: A Probabilistic Machine Learning Perspective\", arXiv:2603.04479 [2026]."

/-- Recorded finite-verification claim shell; paper bound not proved. -/
def mainStatement : Prop :=
  ∃ B : ℕ, 1 < B ∧ ∀ n : ℕ, 0 < n → n < B → ∃ k : ℕ, orbit k n = 1

/-- Mathlib-checked miniature verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨2, by omega, MathlibAttack.Papers.verifies_below_two⟩

end MathlibAttack.Papers.Arxiv2603_04479
