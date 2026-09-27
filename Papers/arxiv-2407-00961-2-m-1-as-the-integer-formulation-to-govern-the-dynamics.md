# arxiv-2407-00961-2-m-1-as-the-integer-formulation-to-govern-the-dynamics

Citation: Gaurav Goyal, "$2^m - 1$ as the Integer Formulation to Govern the Dynamics of Collatz-Type Sequences", arXiv:2407.00961 [2024].

Authors: Gaurav Goyal

arXiv: [2407.00961](https://arxiv.org/abs/2407.00961)

Year: 2024

Classification: generalization

Abstract:

It has been discovered that representing odd integers as modified binary expressions of the form $\sum \limits_{n > m}2^n + 2^m - 1$ for $m \geq 1$ helps in understanding the dynamics of Collatz-type sequences. Starting with the original Collatz sequence $3x + 1$, it is found that when the odd step is applied to an odd integer $\sum \limits_{n > m}2^n + 2^m - 1$, an even integer $3\left(\sum \limits_{n > m}2^{n}\right) + 2^{m + 1} + 2^m - 2$ is obtained, which is exactly once divisible by 2, unless the lowest index reduces to zero. This implies that the sequence alternates between odd and even steps $m$ times. This governs the dynamics of the Collatz-type sequences because the value of $m$ determines the number of times the integer can be divided by 2 in each even step. A shortcut method is developed based on this dynamics that states that the even integer after $m$ odd-even steps are co

Lean file: `Collatz/Papers/Arxiv2407_00961.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
