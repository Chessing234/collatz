# arxiv-1301-3125-cellular-automata-to-more-efficiently-compute-the-colla

Citation: Sitan Chen, "Cellular Automata to More Efficiently Compute the Collatz Map", arXiv:1301.3125 [2013].

Authors: Sitan Chen

arXiv: [1301.3125](https://arxiv.org/abs/1301.3125)

Year: 2013

Classification: verification

Abstract:

The Collatz, or 3x+1, Conjecture claims that for every positive integer n, there exists some k such that T^k(n)=1, where T is the Collatz map. We present three cellular automata (CA) that transform the global problem of mimicking the Collatz map in bases 2, 3, and 4 into a local one of transforming the digits of iterates. The CAs streamline computation first by bypassing calculation of certain parts of trajectories: the binary CA bypasses division by two altogether. In addition, they allow for multiple trajectories to be calculated simultaneously, representing both a significant improvement upon existing sequential methods of computing the Collatz map and a demonstration of the efficacy of using a massively parallel approach with cellular automata to tackle iterative problems like the Collatz Conjecture.

Lean file: `Collatz/Papers/Arxiv1301_3125.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
