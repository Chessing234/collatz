import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Heinz Ebert, "A Graph Theoretical Approach to the Collatz Problem", arXiv:1905.07575 [2019].

Title: A Graph Theoretical Approach to the Collatz Problem

Abstract (from OpenAlex metadata, truncated):
Andrei et al. have shown in 2000 that the graph $\boldsymbol{\mathrm{C}}$ of the Collatz function starting with root $8$ after the initial loop is an infinite binary tree $\boldsymbol{A}(8)$. According to their result they gave a reformulated version of the Collatz conjecture: the vertex set $V(\boldsymbol{A}(8))=\mathbb{Z}^+$. In this paper an inverse Collatz function $\overrightarrow{C}$ with eliminated initial loop is used as generating function of a Collatz graph ${\boldsymbol{\mathrm{C}}}_{\overrightarrow{C}}$. This graph can be considered as the union of one forest that stems from sequences of powers of 2 with odd start values and a second forest that is based on branch values $y=6k+4$ where two Collatz sequences meet. A proof that the graph ${\boldsymbol{\mathrm{C}}}_{\overrightarrow{C}}(1)$ is an infinite binary tree $\boldsymbol{A}_{\overrightarrow{C}}$ with vertex set $V({\bold

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1905.07575
-/

namespace Collatz.Papers.Arxiv1905_07575

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Heinz Ebert, \"A Graph Theoretical Approach to the Collatz Problem\", arXiv:1905.07575 [2019]."

/-- Recorded claim shell (structural); the paper's theorem is not proved.
Placeholder equals the standard Collatz conjecture proposition. -/
def mainStatement : Prop := Collatz.CollatzConjecture

/-- Checked bridge facts only. -/
theorem step_one_eq : Collatz.step 1 = 4 := Collatz.step_one

theorem step_two_eq : Collatz.step 2 = 1 := Collatz.step_two

/-- Checked: every power of two reaches `1` (Mathlib-copied parity/division facts). -/
theorem powers_of_two_reach_one (k : Nat) :
    ∃ t : Nat, Collatz.orbit t (2 ^ k) = 1 :=
  Collatz.Papers.MathlibCopied.orbit_pow_two_reaches_one k

end Collatz.Papers.Arxiv1905_07575
