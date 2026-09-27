# arxiv-2503-00929-the-collatz-conjecture-a-graph-theoretic-structural-pro

Citation: Amarachukwu Nwankpa, "The Collatz Conjecture: A Graph-Theoretic Structural Proof", arXiv:2503.00929 [2025].

Authors: Amarachukwu Nwankpa

arXiv: [2503.00929](https://arxiv.org/abs/2503.00929)

Year: 2025

Classification: cycle

Abstract:

This paper presents a structural proof of the Collatz Conjecture by demonstrating that the Collatz map operates within a finite structural framework. We formalize this framework as a \textbf{17-state Finite State Machine (FSM)} derived directly from the modular properties and integer partitions intrinsic to the Collatz function. The core of the proof lies in a rigorous graph-theoretic analysis of this FSM. We prove that all states representing integers not in the terminal cycle $\{1, 2, 4\}$ form a single \emph{Strongly Connected Component} (SCC), and that this SCC possesses a \emph{unique exit transition} leading irreversibly to the states corresponding to the terminal cycle. By the fundamental properties of finite directed graphs, these structural invariants guarantee that any trajectory---represented as a path through the FSM---must reach the unique terminal cycle in finitely many ste

Lean file: `Collatz/Papers/Arxiv2503_00929.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
