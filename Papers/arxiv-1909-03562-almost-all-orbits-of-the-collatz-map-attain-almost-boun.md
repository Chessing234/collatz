# arxiv-1909-03562-almost-all-orbits-of-the-collatz-map-attain-almost-boun

Citation: Tao, Terence, "Almost all orbits of the Collatz map attain almost bounded values", arXiv:1909.03562 [2019].

Authors: Tao, Terence

arXiv: [1909.03562](https://arxiv.org/abs/1909.03562)

Year: 2019

Classification: density

Abstract:

Define the \emph{Collatz map} $\mathrm{Col} : \mathbb{N}+1 \to \mathbb{N}+1$ on the positive integers $\mathbb{N}+1 = \{1,2,3,\dots\}$ by setting $\mathrm{Col}(N)$ equal to $3N+1$ when $N$ is odd and $N/2$ when $N$ is even, and let $\mathrm{Col}_{\min}(N) := \inf_{n \in \mathbb{N}} \mathrm{Col}^n(N)$ denote the minimal element of the Collatz orbit $N, \mathrm{Col}(N), \mathrm{Col}^2(N), \dots$. The infamous \emph{Collatz conjecture} asserts that $\mathrm{Col}_{\min}(N)=1$ for all $N \in \mathbb{N}+1$. Previously, it was shown by Korec that for any $θ> \frac{\log 3}{\log 4} \approx 0.7924$, one has $\mathrm{Col}_{\min}(N) \leq N^θ$ for almost all $N \in \mathbb{N}+1$ (in the sense of natural density). In this paper we show that for \emph{any} function $f : \mathbb{N}+1 \to \mathbb{R}$ with $\lim_{N \to \infty} f(N)=+\infty$, one has $\mathrm{Col}_{\min}(N) \leq f(N)$ for almost all $N \in

Lean file: `Collatz/Papers/Arxiv1909_03562.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.

Batch: arxiv100-c (2026-09-15)
