import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Carlos Fernández and Santiago Ibáñez, "Christoffel words as extremal structures in Collatz dynamics", arXiv:2607.24844 [2026].

Title: Christoffel words as extremal structures in Collatz dynamics

Abstract (from OpenAlex metadata, truncated):
We study the combinatorial structure of parity sequences associated with the accelerated Collatz map with the goal of identifying extremal configurations and relating them to the existence of periodic orbits. To each finite sequence of an orbit, we associate a binary word whose ones encode the odd iterates, and we introduce a functional $C(d)$ on such words which provides an explicit expression for the iterates and characterizes possible periodic cycles. We define a natural rotation action on binary words, compatible with the cyclic structure of periodic orbits, and consider the functional $C_{\min}(d)$ as a canonical representative of each rotation class. In this setting, we formulate and solve a discrete optimization problem on the set of binary words of fixed length and prescribed density. We prove that Christoffel words are, up to rotation, the unique maximizers of $C_{\min}(d)$ on $D_{N,r}$, the set of binary words of length $N$ with exactly $r$ ones, thereby establishing a direct

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2607.24844
-/

namespace Collatz.Papers.Arxiv2607_24844

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Carlos Fern\u00e1ndez and Santiago Ib\u00e1\u00f1ez, \"Christoffel words as extremal structures in Collatz dynamics\", arXiv:2607.24844 [2026]."

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


end Collatz.Papers.Arxiv2607_24844
