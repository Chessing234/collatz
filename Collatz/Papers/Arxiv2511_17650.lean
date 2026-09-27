import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Alegría, Francisco et al., "A note on two Collatz evolution flows", arXiv:2511.17650 [2025].

Title: A note on two Collatz evolution flows

Abstract (from OpenAlex metadata, truncated):
Two evolution models based on the generalized Collatz operator are introduced. These models are characterized by coefficients $α$ and $β$ in the Collatz dynamics, and are suitably defined. Here, $α=β=1$, and $α=3$, $β=1$ correspond to the Nollatz and classical Collatz operators, respectively. In general, the first evolution model is a continuum, Fourier side based, motivated by the Cubic Szegő operator of Gérard and Grellier. The second evolution considers discrete time derivatives of the Collatz orbits. In this paper we describe the evolution of both models, with particular emphasis on dynamical properties. For the first one, it is proved local and global existence in the space $L^2(\mathbb T)$, and a one-to-one characterization of the existence of nontrivial periodic and unbounded orbits of the Collatz mapping in terms of particular set of solutions of this continuous Collatz flow. For the discrete part, a sort of discrete energy is introduced. This energy has the property of being c

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2511.17650
-/

namespace Collatz.Papers.Arxiv2511_17650

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Alegr\u00eda, Francisco et al., \"A note on two Collatz evolution flows\", arXiv:2511.17650 [2025]."

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


end Collatz.Papers.Arxiv2511_17650
