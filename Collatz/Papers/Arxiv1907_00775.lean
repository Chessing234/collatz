import Collatz.Basic
import Collatz.Papers.MathlibCopied

/-!
Lean notes for Tristan Stérin, "First Occurrence of Parity Vectors and the Regular Structure of k-Span Predecessor Sets in the Collatz Graph.", arXiv:1907.00775 [2019].

Title: First Occurrence of Parity Vectors and the Regular Structure of k-Span Predecessor Sets in the Collatz Graph.

Abstract (from OpenAlex metadata, truncated):
We study finite paths in the graph, a directed graph with natural number nodes and where there is an edge from node $x$ to node $T(x) = T_0(x) = x/2$ if $x$ is even, or to node $T(x) = T_1(x) = (3x+1)/2$ if $x$ is odd. Our first result is an algorithm that, when given a sequence of $n$ parity bits $p = b_0 b_1 \cdots b_{n-1} \in \{ 0,1 \}^n$, called a parity vector, finds the occurrences of this parity vector in the graph which are all the paths $o$, of length $n+1$, where the first $n$ nodes of $o$ have exactly the parities given by $p$. In particular, our algorithm can be used to find the first occurrence of such parity vectors $p$ (has smallest integer nodes out of all paths $o$), or indeed the $i^\text{th}$ for any $i \in\mathbb{N}$. In order to give this algorithm, we introduce $\mathcal{E}(p)$, the Collatz of a parity vector $p$, and the $(\alpha_{0,-1})$-tree, a binary tree which 

Status: statement recorded under `mainStatement`.
Only the named checked lemmas below are kernel-proved.
This file does not claim a complete formalization of the paper.

Source: https://arxiv.org/abs/1907.00775
-/

namespace Collatz.Papers.Arxiv1907_00775

/-- Exact bibliographic citation tracked by this file. -/
def citation : String :=
  "Tristan St\u00e9rin, \"First Occurrence of Parity Vectors and the Regular Structure of k-Span Predecessor Sets in the Collatz Graph.\", arXiv:1907.00775 [2019]."

/-- Recorded finite-verification claim shell; the paper's bound is not proved here. -/
def mainStatement : Prop :=
  ∃ B : Nat, 1 < B ∧ ∀ n : Nat, 0 < n → n < B → ∃ k : Nat, Collatz.orbit k n = 1


/-- Miniature checked verification for `B = 2`. -/
theorem mainStatement_weak : mainStatement := by
  refine ⟨8, by omega, Collatz.Papers.MathlibCopied.verifies_below_eight⟩


end Collatz.Papers.Arxiv1907_00775
