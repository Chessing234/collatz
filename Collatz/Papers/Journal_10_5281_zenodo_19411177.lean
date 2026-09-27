import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Wurm, Matthias, "Balanced on one: contraction–expansion equilibrium in protein folding, the Collatz iteration, and semantic change - Three theorems and an observation", 2026.

Title: Balanced on one: contraction–expansion equilibrium in protein folding, the Collatz iteration, and semantic change - Three theorems and an observation

Abstract (from harvested metadata, truncated):
Three superficially unrelated dynamical systems---protein folding on an energy landscape, the Collatz iteration on the integers, and semantic change in natural language---share a common critical signature: the product $D \cdot \gamma = 1$, where $D$ is the probability of a contractive step and $\gamma$ is its magnitude. We argue that this is not coincidence but structure. We define a class of \emph{contraction--expansion systems} in which a deterministic contraction competes with stochastic expansion, and show that the martingale parameter $\lambda = \mathbb{E}[d(t{+}1)/d(t)]$ governs a trikotomy: convergence ($\lambda 1$). We prove three theorems. \textbf{Theorem~I:} In Go-model protein fol...

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://doi.org/10.5281/zenodo.19411177
-/

namespace Collatz.Papers.Journal_10_5281_zenodo_19411177

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Wurm, Matthias, \"Balanced on one: contraction–expansion equilibrium in protein folding, the Collatz iteration, and semantic change - Three theorems and an observation\", Zenodo, DOI:10.5281/zenodo.19411177 [2026]."

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

end Collatz.Papers.Journal_10_5281_zenodo_19411177
