# arxiv-2607-01718-a-coordinate-system-for-collatz-dynamics

Citation: Jennifer Williams, "A Coordinate System for Collatz Dynamics", arXiv:2607.01718 [2026].

Authors: Jennifer Williams

arXiv: [2607.01718](https://arxiv.org/abs/2607.01718)

Year: 2026

Classification: verification

Abstract:

It is well-established that every odd positive integer $n$ can be written uniquely as $n = λ\cdot 2^a \cdot 3^b - 1$ where $\gcd(λ, 6) = 1$ and $a \geq 1$. Building from this 3-smooth factorization, we introduce a partition of the nonnegative integers into countably many infinite triangles where each row $k$ forms a Collatz chain of alternating parity. The partition admits a coordinate system as a skeleton $\mathcal{L}_λ$ using the pair $(a, b)$ for odd positive integers within a geometric structure where row $k$ corresponds to $k = a + b$. Each position $(a, b)$ maps to $(a-1, b+1)$, a deterministic diagonal flow requiring no number-theoretic input. At the boundary $a = 1$, the trajectory exits to another skeleton depending on the factorization of $λ\cdot 3^{b+1} - 1$. The coordinate system is new. As a concrete application, we prove that rows $k \equiv 2 \pmod 4$ with $k \geq 6$ in the principal skeleton $\mathcal{L}_1$ contain no primes, and show this is the unique residue class adm

Lean file: `Collatz/Papers/Arxiv2607_01718.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
