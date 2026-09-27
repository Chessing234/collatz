import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Maxwell C. Siegel, "Syracuse Random Variables and the Periodic Points of Collatz-type maps", arXiv:2007.15936 [2020].

Title: Syracuse Random Variables and the Periodic Points of Collatz-type maps

Abstract (from OpenAlex metadata, truncated):
Let $p$ be an odd prime, and consider the map $H_{p}$ which sends an integer $x$ to either $\frac{x}{2}$ or $\frac{px+1}{2}$ depending on whether $x$ is even or odd. The values at $x=0$ of arbitrary composition sequences of the maps $\frac{x}{2}$ and $\frac{px+1}{2}$ can be parameterized over the $2$-adic integers ($\mathbb{Z}_{2}$) leading to a continuous function from $\mathbb{Z}_2$ to $\mathbb{Z}_p$ which the author calls the numen of $H_{p}$, denoted $\chi_p$; the $p=3$ case turns out to be an alternative version of the Syracuse Random Variables constructed by Tao [arXiv:1909.03562]. This paper establishes the Correspondence Theorem, which shows that an odd integer $\omega$ is a periodic point of $H_p$ if and only if $\omega=\chi_{p}\left(n\right)/\left(1-r_{p}\left(n\right)\right)$ for some integer $n\geq1$, where $r_{p}\left(n\right) = p^{\#_{1}\left(n\right)} / 2^{\lambda\left(n\r

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2007.15936
-/

namespace Collatz.Papers.Arxiv2007_15936

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Maxwell C. Siegel, \"Syracuse Random Variables and the Periodic Points of Collatz-type maps\", arXiv:2007.15936 [2020]."

/-- Recorded nontrivial-cycle exclusion shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ n : Nat, 1 < n → ∀ k : Nat, 0 < k → Collatz.orbit k n = n →
    ∃ j : Nat, j ≤ k ∧ Collatz.orbit j n = 1

/-- Checked: the trivial cycle through `1` returns after three steps. -/
theorem orbit_one_returns : Collatz.orbit 3 1 = 1 :=
  (Collatz.Papers.MathlibCopied.trivial_cycle).1

theorem step_branches_on_cycle :
    Collatz.step 1 = 4 ∧ Collatz.step 4 = 2 ∧ Collatz.step 2 = 1 := by
  have h := Collatz.Papers.MathlibCopied.trivial_cycle
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩


end Collatz.Papers.Arxiv2007_15936
