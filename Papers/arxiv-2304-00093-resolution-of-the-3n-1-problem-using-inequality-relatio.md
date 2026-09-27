# arxiv-2304-00093-resolution-of-the-3n-1-problem-using-inequality-relatio

Citation: Gaurav Goyal, "Resolution of the 3n+1 Problem Using Inequality Relation Between Indices of 2 and 3", arXiv:2304.00093 [2023].

Authors: Gaurav Goyal

arXiv: [2304.00093](https://arxiv.org/abs/2304.00093)

Year: 2023

Classification: verification

Abstract:

Collatz conjecture states that an integer $n$ reduces to $1$ when certain simple operations are applied to it. Mathematically, the Collatz function is written as $f^k(n) = \frac{3^kn + C}{2^{z}}$, where $z, k, C \geq 1$. Suppose the integer $n$ violates Collatz conjecture by reappearing as $2^in$, where $i \geq 1$, then the equation modifies to $n \left(1 - \frac{3^k}{2^{z}2^i}\right) = \frac{C}{2^{z}2^i}$. The article takes an elementary approach to this problem by calculating the bounds on the values of $\frac{C}{2^{z}2^i}$ and $1 - \frac{3^k}{2^{z}2^i}$. Correspondingly, an upper limit on the integer $n$ is placed that can re-appear in the sequence. The integer $n$ lies in the $(-\infty, 5)$ range, and the limit on the number of odd steps is $k < 3$. Finally, it is shown that no integer chain exists that does not lead to 1.

Lean file: `Collatz/Papers/Arxiv2304_00093.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
