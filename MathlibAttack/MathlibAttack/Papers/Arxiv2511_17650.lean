import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Alegría, Francisco et al., "A note on two Collatz evolution flows", arXiv:2511.17650 [2025].

Title: A note on two Collatz evolution flows

Abstract (truncated):
Two evolution models based on the generalized Collatz operator are introduced. These models are characterized by coefficients $α$ and $β$ in the Collatz dynamics, and are suitably defined. Here, $α=β=1$, and $α=3$, $β=1$ correspond to the Nollatz and classical Collatz operators, respectively. In general, the first evolution model is a continuum, Fourier side based, motivated by the Cubic Szegő operator of Gérard and Grellier. The second evolution considers discrete time derivatives of the Collatz orbits. In this paper we describe the evolution of both models, with particular emphasis on dynamical properties. For the first one, it is proved local and global existence in the space $L^2(\mathbb T)$, and a one-to-one characterization of the existence of nontrivial periodic and unbounded orbits of the Collatz mapping in terms of particular set of solutions of this continuous Collatz flow. For

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2511.17650
-/

namespace MathlibAttack.Papers.Arxiv2511_17650

open MathlibAttack.Papers

def citation : String := "Alegr\u00eda, Francisco et al., \"A note on two Collatz evolution flows\", arXiv:2511.17650 [2025]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2511_17650
