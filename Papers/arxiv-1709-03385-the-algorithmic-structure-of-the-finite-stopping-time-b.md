# arxiv-1709-03385-the-algorithmic-structure-of-the-finite-stopping-time-b

Citation: Mike Winkler, "The algorithmic structure of the finite stopping time behavior of the 3x + 1 function", arXiv:1709.03385 [2017].

Authors: Mike Winkler

arXiv: [1709.03385](https://arxiv.org/abs/1709.03385)

Year: 2017

Classification: verification

Abstract:

The $3x + 1$ problem concerns iteration of the map $T:\mathbb{Z}\rightarrow\mathbb{Z}$ given by \begin{align*} T(x)=\left\{\begin{array}{lcr}\;\;\;\;\displaystyle{\frac{x}{2}} & \mbox{if $\,x\equiv (mod 2)$}, \displaystyle{\frac{3x+1}{2}} & \mbox{if $\,x\equiv 1 (mod 2)$}.\end{array}\right. \end{align*} The $3x+1$ Conjecture states that every $x\geq1$ has some iterate $T^s(x)=1$. The least $s\in\mathbb{N}$ such that $T^s(x) 1$ with a finite stopping time can be evolved according to a directed rooted tree based on their parity vectors. Each parity vector represents a unique Diophantine equation whose only positive solutions are the integers with a finite stopping time. The tree structure is based on a precise algorithm which allows accurate statements about the solutions $x$ without solving the Diophantine equations explicitly. As a consequence, the integers $x>1$ with a finite stopping t

Lean file: `Collatz/Papers/Arxiv1709_03385.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
