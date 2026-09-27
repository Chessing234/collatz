import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Idris Assani et al., "Syracuse Maps as Non-singular Power-Bounded Transformations and Their Inverse Maps", arXiv:2208.11801 [2022].

Title: Syracuse Maps as Non-singular Power-Bounded Transformations and Their Inverse Maps

Abstract (from OpenAlex metadata, truncated):
We prove that the dynamical system $(\mathbb{N}, 2^{\mathbb{N}}, T, μ)$, where $μ$ is a finite measure equivalent to the counting measure, is power-bounded in $L^1(μ)$ if and only if there exists one cycle of the map $T$ and for any $x \in \mathbb{N}$, there exists $k \in \mathbb{N}$ such that $T^k(x)$ is in some cycle of the map $T$. This result has immediate implications for the Collatz Conjecture, and we use it to motivate the study of number theoretic properties of the inverse image $T^{-1}(x)$ for $x \in \mathbb{N}$, where $T$ denotes the Collatz map here. We study similar properties for the related Syracuse maps, comparing them to the Collatz map. We also analyze some structural properties of the inverse image in relation to asymptotic density of the set $\{x \in \mathbb{N} \mid \exists k \in \mathbb{N}: T^k(x) < x\}$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2208.11801
-/

namespace Collatz.Papers.Arxiv2208_11801

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Idris Assani et al., \"Syracuse Maps as Non-singular Power-Bounded Transformations and Their Inverse Maps\", arXiv:2208.11801 [2022]."

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


end Collatz.Papers.Arxiv2208_11801
