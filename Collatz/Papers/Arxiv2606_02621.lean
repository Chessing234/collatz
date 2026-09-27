import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Manuel-Alejandro Reyes Jiménez, "A Fibonacci theorem for Collatz trajectories via modular graph structure", arXiv:2606.02621 [2026].

Title: A Fibonacci theorem for Collatz trajectories via modular graph structure

Abstract (from OpenAlex metadata, truncated):
Let $T(n)=n/2$ if $n$ is even and $T(n)=(3n+1)/2$ if $n$ is odd. We prove that for each $m\ge1$, exactly $F(m+1)$ odd integers in $\{1,\ldots,2^m\}$ have the property that their orbit under $T$ avoids the residue class $4\pmod6$ during steps $2,\ldots,m$, where $F(m+1)$ is the $(m+1)$-th Fibonacci number; the proportion decays at rate $(φ/2)^m$, $φ=(1+\sqrt{5})/2$. The proof uses the directed graph $G$ of Collatz transitions modulo $6$ and its unique absorbing strongly connected component $G'=G[\{1,2,4,5\}]$. Removing vertex $4$ from $G'$ yields a subgraph of spectral radius $φ$, against $ρ(G')=2$; the Fibonacci count follows from this spectral gap. We construct an explicit bijection $Ψ_m:\{1,\ldots,6\cdot2^m\}\to\mathcal{P}_m(G)$ onto the directed paths of length $m$ in $G$. We further show that no vertex of $G'$ is dispensable: removing any single vertex reduces the spectral radius strictly below $2$, with hierarchy $1<\sqrt{2}<φ<2$. In particular, every positive cycle of $T$ must vi

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2606.02621
-/

namespace Collatz.Papers.Arxiv2606_02621

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Manuel-Alejandro Reyes Jim\u00e9nez, \"A Fibonacci theorem for Collatz trajectories via modular graph structure\", arXiv:2606.02621 [2026]."

/-- Recorded main claim shell (cycle); not proved.
States that any accelerated return to `n > 1` has already visited `1`. -/
def mainStatement : Prop :=
  ∀ n : Nat, n > 1 → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial 1-cycle returns to 1. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2606_02621
