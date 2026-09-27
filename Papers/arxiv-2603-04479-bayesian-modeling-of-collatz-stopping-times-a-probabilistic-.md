# arxiv-2603-04479-bayesian-modeling-of-collatz-stopping-times-a-probabilistic-

Citation: Nicolò Bonacorsi and Matteo Bordoni, "Bayesian Modeling of Collatz Stopping Times: A Probabilistic Machine Learning Perspective", arXiv:2603.04479 [2026].

Authors: Nicolò Bonacorsi, Matteo Bordoni

arXiv: [2603.04479](https://arxiv.org/abs/2603.04479)

Year: 2026

Classification: verification

Abstract:

We study the Collatz total stopping time $τ(n)$ over $n\le 10^7$ from a probabilistic machine learning viewpoint. Empirically, $τ(n)$ is a skewed and heavily overdispersed count with pronounced arithmetic heterogeneity. We develop two complementary models. First, a Bayesian hierarchical Negative Binomial regression (NB2-GLM) predicts $τ(n)$ from simple covariates ($\log n$ and residue class $n \bmod 8$), quantifying uncertainty via posterior and posterior predictive distributions. Second, we propose a mechanistic generative approximation based on the odd-block decomposition: for odd $m$, write $3m+1=2^{K(m)}m'$ with $m'$ odd and $K(m)=v_2(3m+1)\ge 1$; randomizing these block lengths yields a stochastic approximation calibrated via a Dirichlet-multinomial update. On held-out data, the NB2-GLM achieves substantially higher predictive likelihood than the odd-block generators. Conditioning the block-length distribution on $m\bmod 8$ markedly improves the generator's distributional fit, ind

Lean file: `Collatz/Papers/Arxiv2603_04479.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
