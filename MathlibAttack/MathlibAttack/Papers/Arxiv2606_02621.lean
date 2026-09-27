import MathlibAttack.Papers.Core

/-!
Mathlib-backed Lean notes for Manuel-Alejandro Reyes Jiménez, "A Fibonacci theorem for Collatz trajectories via modular graph structure", arXiv:2606.02621 [2026].

Title: A Fibonacci theorem for Collatz trajectories via modular graph structure

Abstract (truncated):
Let $T(n)=n/2$ if $n$ is even and $T(n)=(3n+1)/2$ if $n$ is odd. We prove that for each $m\ge1$, exactly $F(m+1)$ odd integers in $\{1,\ldots,2^m\}$ have the property that their orbit under $T$ avoids the residue class $4\pmod6$ during steps $2,\ldots,m$, where $F(m+1)$ is the $(m+1)$-th Fibonacci number; the proportion decays at rate $(φ/2)^m$, $φ=(1+\sqrt{5})/2$. The proof uses the directed graph $G$ of Collatz transitions modulo $6$ and its unique absorbing strongly connected component $G'=G[\{1,2,4,5\}]$. Removing vertex $4$ from $G'$ yields a subgraph of spectral radius $φ$, against $ρ(G')=2$; the Fibonacci count follows from this spectral gap. We construct an explicit bijection $Ψ_m:\{1,\ldots,6\cdot2^m\}\to\mathcal{P}_m(G)$ onto the directed paths of length $m$ in $G$. We further show that no vertex of $G'$ is dispensable: removing any single vertex reduces the spectral radius str

Uses Mathlib (`ℚ`, `omega`, positivity-style facts via Core).
Status: `mainStatement` records the paper claim; only named lemmas are proved.
Source: https://arxiv.org/abs/2606.02621
-/

namespace MathlibAttack.Papers.Arxiv2606_02621

open MathlibAttack.Papers

def citation : String := "Manuel-Alejandro Reyes Jim\u00e9nez, \"A Fibonacci theorem for Collatz trajectories via modular graph structure\", arXiv:2606.02621 [2026]."

/-- Recorded cycle-exclusion shell (paper theorem not proved). -/
def mainStatement : Prop :=
  ∀ n : ℕ, 1 < n → ∀ k : ℕ, 0 < k → orbit k n = n →
    ∃ j : ℕ, j ≤ k ∧ orbit j n = 1

/-- Checked: the trivial 1-cycle returns. -/
theorem orbit_one_cycle : orbit 3 1 = 1 :=
  MathlibAttack.Papers.orbit_one_returns

end MathlibAttack.Papers.Arxiv2606_02621
