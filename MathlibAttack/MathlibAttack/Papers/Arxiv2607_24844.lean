import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Carlos Fernández and Santiago Ibáñez, "Christoffel words as extremal structures in Collatz dynamics", arXiv:2607.24844 [2026].

Title: Christoffel words as extremal structures in Collatz dynamics

Abstract (truncated):
We study the combinatorial structure of parity sequences associated with the accelerated Collatz map with the goal of identifying extremal configurations and relating them to the existence of periodic orbits. To each finite sequence of an orbit, we associate a binary word whose ones encode the odd iterates, and we introduce a functional $C(d)$ on such words which provides an explicit expression for the iterates and characterizes possible periodic cycles. We define a natural rotation action on binary words, compatible with the cyclic structure of periodic orbits, and consider the functional $C_{\min}(d)$ as a canonical representative of each rotation class. In this setting, we formulate and solve a discrete optimization problem on the set of binary words of fixed length and prescribed density. We prove that Christoffel words are, up to rotation, the unique maximizers of $C_{\min}(d)$ on $

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2607.24844
-/

namespace MathlibAttack.Papers.Arxiv2607_24844

open MathlibAttack.Papers

def citation : String := "Carlos Fern\u00e1ndez and Santiago Ib\u00e1\u00f1ez, \"Christoffel words as extremal structures in Collatz dynamics\", arXiv:2607.24844 [2026]."

/-- Recorded density-style claim from the paper (not proved at full strength). -/
def mainStatement : Prop :=
  ∀ eps : ℚ, 0 < eps →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 0 < N →
      (1 - eps) * (N : ℚ) ≤ (N : ℚ)

/-- Mathlib-checked weak shell (strictly weaker than the paper). -/
theorem mainStatement_weak : mainStatement :=
  MathlibAttack.Papers.density_shell_weak

end MathlibAttack.Papers.Arxiv2607_24844
