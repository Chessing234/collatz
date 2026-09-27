# doi-10-5281-zenodo-18601486-the-end-of-every-hailstone-a-formally-ve

Citation: Reed, Jonathan ƒ(n), "The End of Every Hailstone: A Formally Verified Structural Parity Proof of the Collatz Conjecture", DOI:10.5281/zenodo.18601486 [2026].

Authors: Reed, Jonathan ƒ(n)

DOI: [10.5281/zenodo.18601486](https://doi.org/10.5281/zenodo.18601486)

Year: 2026

Venue: (unknown)

Classification: verification

Abstract:

The Collatz Conjecture is widely viewed as a stochastic hailstone sequence, yet formal verification in Lean 4 reveals it to be a disguised algebraic tautology. We demonstrate that the $3n + 1$ map is not a generator of chaos, but a subtraction engine that systematically eliminates $3$-adic complexity. By establishing [The Principle of Structural Parity] we prove that every odd integer $n$ is definitionally bound to the identity $3^m n + R = 2^K$. Utilizing a recursive lift function to track the structural residue ($R$), we provide a machine-verified proof that the function’s $+1$ is a closing constant that maintains an invariant balance. This reveals that convergence to $1$ is the only mathematically legal configuration for the system, effectively reducing the $3n + 1$ problem to the...

Lean file: `Collatz/Papers/Journal_10_5281_zenodo_18601486.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: journal100-j (2026-09-15)
