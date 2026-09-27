# arxiv-2606-02621-a-fibonacci-theorem-for-collatz-trajectories-via-modular-gra

Citation: Manuel-Alejandro Reyes Jiménez, "A Fibonacci theorem for Collatz trajectories via modular graph structure", arXiv:2606.02621 [2026].

Authors: Manuel-Alejandro Reyes Jiménez

arXiv: [2606.02621](https://arxiv.org/abs/2606.02621)

Year: 2026

Classification: cycle

Abstract:

Let $T(n)=n/2$ if $n$ is even and $T(n)=(3n+1)/2$ if $n$ is odd. We prove that for each $m\ge1$, exactly $F(m+1)$ odd integers in $\{1,\ldots,2^m\}$ have the property that their orbit under $T$ avoids the residue class $4\pmod6$ during steps $2,\ldots,m$, where $F(m+1)$ is the $(m+1)$-th Fibonacci number; the proportion decays at rate $(φ/2)^m$, $φ=(1+\sqrt{5})/2$. The proof uses the directed graph $G$ of Collatz transitions modulo $6$ and its unique absorbing strongly connected component $G'=G[\{1,2,4,5\}]$. Removing vertex $4$ from $G'$ yields a subgraph of spectral radius $φ$, against $ρ(G')=2$; the Fibonacci count follows from this spectral gap. We construct an explicit bijection $Ψ_m:\{1,\ldots,6\cdot2^m\}\to\mathcal{P}_m(G)$ onto the directed paths of length $m$ in $G$. We further show that no vertex of $G'$ is dispensable: removing any single vertex reduces the spectral radius strictly below $2$, with hierarchy $1<\sqrt{2}<φ<2$. In particular, every positive cycle of $T$ must vi

Lean file: `Collatz/Papers/Arxiv2606_02621.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
