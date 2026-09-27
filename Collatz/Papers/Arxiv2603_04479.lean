import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Nicolò Bonacorsi and Matteo Bordoni, "Bayesian Modeling of Collatz Stopping Times: A Probabilistic Machine Learning Perspective", arXiv:2603.04479 [2026].

Title: Bayesian Modeling of Collatz Stopping Times: A Probabilistic Machine Learning Perspective

Abstract (from OpenAlex metadata, truncated):
We study the Collatz total stopping time $τ(n)$ over $n\le 10^7$ from a probabilistic machine learning viewpoint. Empirically, $τ(n)$ is a skewed and heavily overdispersed count with pronounced arithmetic heterogeneity. We develop two complementary models. First, a Bayesian hierarchical Negative Binomial regression (NB2-GLM) predicts $τ(n)$ from simple covariates ($\log n$ and residue class $n \bmod 8$), quantifying uncertainty via posterior and posterior predictive distributions. Second, we propose a mechanistic generative approximation based on the odd-block decomposition: for odd $m$, write $3m+1=2^{K(m)}m'$ with $m'$ odd and $K(m)=v_2(3m+1)\ge 1$; randomizing these block lengths yields a stochastic approximation calibrated via a Dirichlet-multinomial update. On held-out data, the NB2-GLM achieves substantially higher predictive likelihood than the odd-block generators. Conditioning the block-length distribution on $m\bmod 8$ markedly improves the generator's distributional fit, ind

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2603.04479
-/

namespace Collatz.Papers.Arxiv2603_04479

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Nicol\u00f2 Bonacorsi and Matteo Bordoni, \"Bayesian Modeling of Collatz Stopping Times: A Probabilistic Machine Learning Perspective\", arXiv:2603.04479 [2026]."

/-- Recorded main claim shell (verification); paper bound not proved here.
A checked miniature verification for `n < 2` is given below. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature verification: every positive `n < 2` reaches `1`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv2603_04479
