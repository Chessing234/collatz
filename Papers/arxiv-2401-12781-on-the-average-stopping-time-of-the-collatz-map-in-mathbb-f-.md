# arxiv-2401-12781-on-the-average-stopping-time-of-the-collatz-map-in-mathbb-f-

Citation: Manuel Inselmann, "On the average stopping time of the Collatz map in $\mathbb{F}_2[x]$", arXiv:2401.12781 [2024].

Authors: Manuel Inselmann

arXiv: [2401.12781](https://arxiv.org/abs/2401.12781)

Year: 2024

Classification: verification

Abstract:

Define the map $T_1$ on $\mathbb{F}_2[x]$ by $T_1(f)=\frac{f}{x}$ if $f(0)=0$ and $T_1(f)=\frac{(x+1)f+1}{x}$ if $f(0)=1$. For a non-zero polynomial $f$ let $τ_1(f)$ denote the least natural $k$ number for which $T_1^{k}(f)=1$. Define the average stopping time to be $ρ_1(n)=\frac{\sum_{f\in \mathbb{F}_2[x], \text{deg}(f)=n }τ_1(f)}{2^n}$. We show that $\lim_{n\rightarrow\infty}\frac{ρ_1(n)}{n}=2$, confirming a conjecture of Alon, Behajaina, and Paran. Furthermore, we give a new proof that $τ_1(f)\in O(\text{deg}(f)^{1.5})$ for all $f\in\mathbb{F}_2[x]\setminus\{0\}$.

Lean file: `Collatz/Papers/Arxiv2401_12781.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
