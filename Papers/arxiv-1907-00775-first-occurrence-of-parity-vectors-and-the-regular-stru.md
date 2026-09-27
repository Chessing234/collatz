# arxiv-1907-00775-first-occurrence-of-parity-vectors-and-the-regular-stru

Citation: Tristan Stérin, "First Occurrence of Parity Vectors and the Regular Structure of k-Span Predecessor Sets in the Collatz Graph.", arXiv:1907.00775 [2019].

Authors: Tristan Stérin

arXiv: [1907.00775](https://arxiv.org/abs/1907.00775)

Year: 2019

Classification: verification

Abstract:

We study finite paths in the graph, a directed graph with natural number nodes and where there is an edge from node $x$ to node $T(x) = T_0(x) = x/2$ if $x$ is even, or to node $T(x) = T_1(x) = (3x+1)/2$ if $x$ is odd. Our first result is an algorithm that, when given a sequence of $n$ parity bits $p = b_0 b_1 \cdots b_{n-1} \in \{ 0,1 \}^n$, called a parity vector, finds the occurrences of this parity vector in the graph which are all the paths $o$, of length $n+1$, where the first $n$ nodes of $o$ have exactly the parities given by $p$. In particular, our algorithm can be used to find the first occurrence of such parity vectors $p$ (has smallest integer nodes out of all paths $o$), or indeed the $i^\text{th}$ for any $i \in\mathbb{N}$. In order to give this algorithm, we introduce $\mathcal{E}(p)$, the Collatz of a parity vector $p$, and the $(\alpha_{0,-1})$-tree, a binary tree which 

Lean file: `Collatz/Papers/Arxiv1907_00775.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
