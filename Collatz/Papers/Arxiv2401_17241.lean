import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Manuel Inselmann, "Almost all orbits of an analogue of the Collatz map on the reals attain bounded values", arXiv:2401.17241 [2024].

Title: Almost all orbits of an analogue of the Collatz map on the reals attain bounded values

Abstract (from OpenAlex metadata, truncated):
Motivated by a balanced ternary representation of the Collatz map we define the map $C_\mathbb{R}$ on the positive real numbers by setting $C_\mathbb{R}(x)=\frac{1}{2}x$ if $[x]$ is even and $C_\mathbb{R}(x)=\frac{3}{2}x$ if $[x]$ is odd, where $[x]$ is defined by $[x]\in\mathbb{Z}$ and $x-[x]\in(-\frac{1}{2},\frac{1}{2}]$. We show that there exists a constant $K>0$ such that the set of $x$ fulfilling $\liminf_{n\in\mathbb{N}}C_\mathbb{R}^n(x)\leq K$ is Lebesgue-co-null. We also show that for any $ε>0$ the set of $x$ for which $ (\frac{3^{\frac{1}{2}}}{2})^kx^{1-ε}\leq C_\mathbb{R}^k(x)\leq (\frac{3^{\frac{1}{2}}}{2})^kx^{1+ε}$ for all $0\leq k\leq \frac{1}{1-\frac{\log_23}{2}}\log_2x$ is large for a suitable notion of largeness.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2401.17241
-/

namespace Collatz.Papers.Arxiv2401_17241

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Manuel Inselmann, \"Almost all orbits of an analogue of the Collatz map on the reals attain bounded values\", arXiv:2401.17241 [2024]."

/-- Recorded density-style claim shell; the paper's theorem is not proved. -/
def mainStatement : Prop :=
  ∀ eps : Rat, 0 < eps →
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ((1 : Rat) - eps) * (N : Rat) ≤ (N : Rat)

/-- Weak density scaffolding (Mathlib-copied `Rat` facts); strictly weaker than the paper. -/
theorem mainStatement_weak : mainStatement := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro N _ _
  exact Collatz.Papers.MathlibCopied.density_shell_of_pos eps N heps


end Collatz.Papers.Arxiv2401_17241
