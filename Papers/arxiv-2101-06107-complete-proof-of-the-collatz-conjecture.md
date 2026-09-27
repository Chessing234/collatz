# arxiv-2101-06107-complete-proof-of-the-collatz-conjecture

Citation: Farzali Izadi, "Complete Proof of the Collatz Conjecture", arXiv:2101.06107 [2021].

Authors: Farzali Izadi

arXiv: [2101.06107](https://arxiv.org/abs/2101.06107)

Year: 2021

Classification: logic

Abstract:

The \textit{Collatz's conjecture} is an unsolved problem in mathematics. It is named after Lothar Collatz in 1973. The conjecture also known as Syrucuse conjecture or problem. Take any positive integer $ n $. If $ n $ is even then divide it by $ 2 $, else do "triple plus one" and get $ 3n+1 $. The conjecture is that for all numbers, this process converges to one. In the modular arithmetic notation, define a function $ f $ as follows: \[f(x)= \left\{ \begin{array}{lll} \frac{n}{2} &if & n\equiv 0 \pmod 2\\ 3n+1& if& n\equiv 1 \pmod 2. \end{array}\right. \] In this paper, we present the proof of the Collatz conjecture for many types of sets defined by the remainder theorem of arithmetic. These sets are defined in mods $6, 12, 24, 36, 48, 60, 72, 84, 96, 108$ and we took only odd positive remainders to work with. It is not difficult to prove that the same results are true for any mod $12m, $ for positive integers $m$.

Lean file: `Collatz/Papers/Arxiv2101_06107.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
