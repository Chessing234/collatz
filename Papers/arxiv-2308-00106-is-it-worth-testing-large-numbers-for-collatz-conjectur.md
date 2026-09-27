# arxiv-2308-00106-is-it-worth-testing-large-numbers-for-collatz-conjectur

Citation: Gaurav Goyal, "Is It Worth Testing Large Numbers for Collatz Conjecture?", arXiv:2308.00106 [2023].

Authors: Gaurav Goyal

arXiv: [2308.00106](https://arxiv.org/abs/2308.00106)

Year: 2023

Classification: verification

Abstract:

Starting with a positive odd integer $n$, apply a function $f(n)$ repetitively such that $f(n) = 3n + 1$ if $n \not\equiv 0 (\text{mod}\:2)$ or $f(n) = n/2$ if $n \equiv 0 (\text{mod}\:2)$. Let the sequence of all the odd integers obtained form an orbit $n, f^1(n) , f^2(n), \ldots, f^k(n), f^{k + 1}(n)$. The $k^{th}$ odd integer is written as $f^k(n) = (3^k + \mathbf{B(k)})/2^{\mathbf{z(k)}}$ where $\mathbf{B(k)}$ is the collection of terms without the coefficient $n$. We show that when $1 - \mathbf{B(k)}/(2^{\mathbf{z(k)}} n) \approx 1$, the condition for unbounded orbit is given by OEIS A022921. Further, if there exists at least one orbit for which $f^{k + 1}(n) = n$ when $(k + 1) < 3$, we show that there exists no orbit with $k + 1 > 3$ for which $f^{k + 1}(n) = n$. The final result is that the odd integers that can violate the Collatz conjecture are smaller than 5.

Lean file: `Collatz/Papers/Arxiv2308_00106.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
