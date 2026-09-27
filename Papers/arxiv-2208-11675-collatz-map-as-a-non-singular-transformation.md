# arxiv-2208-11675-collatz-map-as-a-non-singular-transformation

Citation: Assani, Idris, "Collatz map as a non-singular transformation", arXiv:2208.11675 [2022].

Authors: Assani, Idris

arXiv: [2208.11675](https://arxiv.org/abs/2208.11675)

Year: 2022

Classification: verification

Abstract:

Let $T$ be the map defined on $\N=\{1,2,3, ...\}$ by $T(n) = \frac{n}{2} $ if $n$ is even and by $T(n) = \frac{3n+1}{2}$ if $n$ is odd. Consider the dynamical system $(\N, 2^{\N}, T,μ)$ where $μ$ is the counting measure. This dynamical system $(\N, 2^{\N}, T, μ)$ has the following properties. \begin{enumerate} \item There exists an invariant finite measure $γ$ such that $γ(A) \leq μ(A) $ for all $A \subset \N.$ \item For each function $f\in L^1(μ)$ the averages $\frac{1}{N} \sum_{n=1}^N f(T^nx)$ converge for every $x\in \N$ to $ f^*(x)$ where $ f^* \in L^1(μ).$ \end{enumerate} We also show that the Collatz conjecture is equivalent to the existence of a finite measure $ν$ on $(\N, 2^{\N})$ making the operator $Vf = f\circ T$ power bounded in $L^1(ν)$ with conserrvative part $\{1,2\}.$

Lean file: `Collatz/Papers/Arxiv2208_11675.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
