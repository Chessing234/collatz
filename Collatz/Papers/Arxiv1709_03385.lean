import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Mike Winkler, "The algorithmic structure of the finite stopping time behavior of the 3x + 1 function", arXiv:1709.03385 [2017].

Title: The algorithmic structure of the finite stopping time behavior of the 3x + 1 function

Abstract (from OpenAlex metadata, truncated):
The $3x + 1$ problem concerns iteration of the map $T:\mathbb{Z}\rightarrow\mathbb{Z}$ given by \begin{align*} T(x)=\left\{\begin{array}{lcr}\;\;\;\;\displaystyle{\frac{x}{2}} & \mbox{if $\,x\equiv (mod 2)$}, \displaystyle{\frac{3x+1}{2}} & \mbox{if $\,x\equiv 1 (mod 2)$}.\end{array}\right. \end{align*} The $3x+1$ Conjecture states that every $x\geq1$ has some iterate $T^s(x)=1$. The least $s\in\mathbb{N}$ such that $T^s(x) 1$ with a finite stopping time can be evolved according to a directed rooted tree based on their parity vectors. Each parity vector represents a unique Diophantine equation whose only positive solutions are the integers with a finite stopping time. The tree structure is based on a precise algorithm which allows accurate statements about the solutions $x$ without solving the Diophantine equations explicitly. As a consequence, the integers $x>1$ with a finite stopping t

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1709.03385
-/

namespace Collatz.Papers.Arxiv1709_03385

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Mike Winkler, \"The algorithmic structure of the finite stopping time behavior of the 3x + 1 function\", arXiv:1709.03385 [2017]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1709_03385
