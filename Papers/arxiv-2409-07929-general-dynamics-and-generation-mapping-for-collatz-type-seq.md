# arxiv-2409-07929-general-dynamics-and-generation-mapping-for-collatz-type-seq

Citation: Gaurav Goyal, "General Dynamics and Generation Mapping for Collatz-type Sequences", arXiv:2409.07929 [2024].

Authors: Gaurav Goyal

arXiv: [2409.07929](https://arxiv.org/abs/2409.07929)

Year: 2024

Classification: cycle

Abstract:

Let an odd integer \(\mathcal{X}\) be expressed as $\left\{\sum\limits_{M > m}b_M2^M\right\}+2^m-1,$ where $b_M\in\{0,1\}$ and $2^m-1$ is referred to as the Governor. In Collatz-type functions, a high index Governor is eventually reduced to $2^1-1$. For the $3\mathcal{Z}+1$ sequence, the Governor occurring in the Trivial cycle is $2^1-1$, while for the $5\mathcal{Z}+1$ sequence, the Trivial Governors are $2^2-1$ and $2^1-1$. Therefore, in these specific sequences, the Collatz function reduces the Governor $2^m - 1$ to the Trivial Governor $2^{\mathcal{T}} - 1$. Once this Trivial Governor is reached, it can evolve to a higher index Governor through interactions with other terms. This feature allows $\mathcal{X}$ to reappear in a Collatz-type sequence, since $2^m - 1 = 2^{m - 1} + \cdots + 2^{\mathcal{T} + 1} + 2^{\mathcal{T}}+(2^{\mathcal{T}}-1).$ Thus, if $\mathcal{X}$ reappears, at least one odd ancestor of $\left\{\sum\limits_{M > m}b_M2^M\right\}+2^{m-1}+\cdots+2^{\mathcal{T}+1}+2^{

Lean file: `Collatz/Papers/Arxiv2409_07929.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
