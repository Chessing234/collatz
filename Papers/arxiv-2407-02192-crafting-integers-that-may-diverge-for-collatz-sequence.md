# arxiv-2407-02192-crafting-integers-that-may-diverge-for-collatz-sequence

Citation: Gaurav Goyal, "Crafting Integers That ‘May’ Diverge for Collatz Sequence", arXiv:2407.02192 [2024].

Authors: Gaurav Goyal

arXiv: [2407.02192](https://arxiv.org/abs/2407.02192)

Year: 2024

Classification: cycle

Abstract:

Let an odd integer be represented as $\sum \limits_{n > m} 2^n + 2^m - 1$ for $m \geq 1$. To transform $2^m - 1$ according to the Collatz rules, the $3x + 1$ step is applied, resulting in the even integer $2^{m + 1} + 2^m - 2$. This even integer, being exactly once divisible by 2, becomes the next odd integer $2^m + 2^{m - 1} - 1$. This represents the growth phase, as exactly one even step follows an odd step. However, while the overall value of the integer increases, terms with decreasing indices are generated after each odd-even cycle. After $m$ such cycles, a term $2^{m - m}$ (which equals 1) is generated, canceling the negative 1. Additional even steps are then performed until the integer becomes odd again, which occurs when the next smallest index becomes zero. The positive 1 thus obtained is written as $2^1 - 1$. If uninterrupted, the term $2^1 - 1$ has the trivial cycle $2^1 - 1 \

Lean file: `Collatz/Papers/Arxiv2407_02192.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
