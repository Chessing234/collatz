import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Siegel, Maxwell C., "The Hydra Map and Numen Formalisms for Collatz-Type Problems", arXiv:2601.17030 [2026].

Title: The Hydra Map and Numen Formalisms for Collatz-Type Problems

Abstract (from OpenAlex metadata, truncated):
This paper details a generalization of the formalism presented in the author's 2024 paper, "The Collatz Conjecture and Non-Archimedean Spectral Theory - Part I - Arithmetic Dynamical Systems and Non-Archimedean Value Distribution Theory", to the case of Hydra maps on the ring of integers $\mathcal{O}_{K}$ of a global field $K$. In addition to recounting these definitions, background material is presented for the necessary standard material in algebraic number theory and integration and Fourier analysis with respect to the $p$-adic Haar measure. This paper is meant to serve as a technical manual for use of Hydra maps and numens in future research.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/2601.17030
-/

namespace Collatz.Papers.Arxiv2601_17030

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Siegel, Maxwell C., \"The Hydra Map and Numen Formalisms for Collatz-Type Problems\", arXiv:2601.17030 [2026]."

/-- Recorded main claim shell (generalization); the paper's theorem is not proved here.
This placeholder is the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv2601_17030
