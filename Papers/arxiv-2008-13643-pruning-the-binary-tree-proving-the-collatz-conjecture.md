# arxiv-2008-13643-pruning-the-binary-tree-proving-the-collatz-conjecture

Citation: Jan Kleinnijenhuis and Alissa M. Kleinnijenhuis, "Pruning the binary tree, proving the Collatz conjecture", arXiv:2008.13643 [2020].

Authors: Jan Kleinnijenhuis, Alissa M. Kleinnijenhuis

arXiv: [2008.13643](https://arxiv.org/abs/2008.13643)

Year: 2020

Classification: density

Abstract:

The yet unproven Collatz conjecture maintains that repeatedly connecting even numbers n to n/2, and odd n to 3n+1, connects all natural numbers to a single tree with 1 as its root. Pruning ever more numbers from this tree until the density of pruned numbers relative to the natural numbers is arbitrarily close to 100% would prove that all numbers belonged to the tree. Preliminarily, numbers divisible by 2 or 3 are pruned. A binary tree is reconnected that forks at each number towards an ``upward'' and a ``rightward'' number. Next, intermediate rightward numbers, upward numbers with a rightward parent, with a rightward grandparent, etcetera, are pruned, which accrues the density of pruned numbers arbitrarily close to 100%. This proves the Collatz conjecture.

Lean file: `Collatz/Papers/Arxiv2008_13643.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-b (2026-09-15)
