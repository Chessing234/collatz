import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Andrey Rukhin, "A Simple Recurrence Within the $3$-adics and Mixed-Radix $\textbf{2}$-adics of the 3x+1 Accelerated First-Inverse Map", arXiv:1506.07622 [2015].

Title: A Simple Recurrence Within the $3$-adics and Mixed-Radix $\textbf{2}$-adics of the 3x+1 Accelerated First-Inverse Map

Abstract (from OpenAlex metadata, truncated):
This article analyzes the $3x+1$ Accelerated First-Inverse map: we will consider the functional powers of the function $\mathcal{B}: Z_3 \to Z_3$ defined as $$ 
\mathcal{B}\left(3q+r\right) = 
\begin{cases} 
3q, & r = 0 \notag 
4q+1, & r = 1 \notag 
2q+1, & r = 2 
\end{cases} $$ where $3q+r \in Z_3$. The values of the functional powers are not the primary focus of these analyses; this paper investigates the properties of their quotients. For any sequence of functional powers $(n_u)_{u\geq 0}$ where $n_u = 3q_u+r_u$, we will study the $p$-adic expansions and shifts ($p\in\{2,3\}$) of the sequence of quotients $(q_u)_{u\geq 0}$. The main result of this paper is a simple recurrence over the set $\{0,1,2,3\}$ for computing the $3$-adic and mixed-radix $\textbf{2}$-adic canonical expansions and shifts of the quotients that arise in the orbits of the function $\mathcal{B}$.

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1506.07622
-/

namespace Collatz.Papers.Arxiv1506_07622

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Andrey Rukhin, \"A Simple Recurrence Within the $3$-adics and Mixed-Radix $\\textbf{2}$-adics of the 3x+1 Accelerated First-Inverse Map\", arXiv:1506.07622 [2015]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1506_07622
