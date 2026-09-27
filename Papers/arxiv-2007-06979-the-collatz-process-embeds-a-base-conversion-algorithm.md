# arxiv-2007-06979-the-collatz-process-embeds-a-base-conversion-algorithm

Citation: Stérin, Tristan and Woods, Damien, "The Collatz process embeds a base conversion algorithm", arXiv:2007.06979 [2020].

Authors: Stérin, Tristan, Woods, Damien

arXiv: [2007.06979](https://arxiv.org/abs/2007.06979)

Year: 2020

Classification: cycle

Abstract:

The Collatz process is defined on natural numbers by iterating the map $T(x) = T_0(x) = x/2$ when $x\in\mathbb{N}$ is even and $T(x)=T_1(x) =(3x+1)/2$ when $x$ is odd. In an effort to understand its dynamics, and since Generalised Collatz Maps are known to simulate Turing Machines [Conway, 1972], it seems natural to ask what kinds of algorithmic behaviours it embeds. We define a quasi-cellular automaton that exactly simulates the Collatz process on the square grid: on input $x\in\mathbb{N}$, written horizontally in base 2, successive rows give the Collatz sequence of $x$ in base 2. We show that vertical columns simultaneously iterate the map in base 3. This leads to our main result: the Collatz process embeds an algorithm that converts any natural number from base 3 to base 2. We also find that the evolution of our automaton computes the parity of the number of 1s in any ternary input. I

Lean file: `Collatz/Papers/Arxiv2007_06979.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
