# arxiv-2601-04289-an-explicit-near-conjugacy-between-the-collatz-map-and-a-cir

Citation: Barmak Honarvar Shakibaei Asli, "An Explicit Near-Conjugacy Between the Collatz Map and a Circle Rotation", arXiv:2601.04289 [2026].

Authors: Barmak Honarvar Shakibaei Asli

arXiv: [2601.04289](https://arxiv.org/abs/2601.04289)

Year: 2026

Classification: verification

Abstract:

We introduce an explicit logarithmic transformation $T(x) = \{\log_6(x + 1/5)\}$ under which the Collatz map becomes a rigid circle rotation by the irrational angle \(α= \log_6 3\), perturbed by a uniformly bounded error term. We prove that for all positive integers \(x\), $T(C(x)) = T(x) + α+ \varepsilon(x) \pmod{1}$, where \(|\varepsilon(x)| \le 0.2749\) and \(\varepsilon(x) = O(1/x)\) as \(x \to \infty\). We derive the transformation from an exact functional equation linking the even and odd branches of the Collatz map, explain the arithmetic origin of the parameters \(6\) and \(1/5\), and analyse the structure of the resulting error term. Extensive numerical computations up to \(10^{12}\) confirm the sharpness of the bounds and show that cumulative errors remain uniformly bounded along all tested trajectories. While this near-conjugacy does not by itself resolve the Collatz conjecture, it provides a concrete and quantitative dynamical framework that clarifies the geometric structur

Lean file: `Collatz/Papers/Arxiv2601_04289.lean`.

Formalization status: statement recorded as `mainStatement`; only weak bridge lemmas are checked. The paper's main theorem is not proved in Lean.
