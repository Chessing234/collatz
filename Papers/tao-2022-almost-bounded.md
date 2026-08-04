# tao-2022-almost-bounded

Citation: Terence Tao, "Almost all orbits of the Collatz map attain almost bounded values", Forum of Mathematics, Pi 10 (2022), e12.

Source checked: arXiv:1909.03562 and the published Forum Math. Pi article.

Tao proves that for every function `f : ℕ⁺ → ℝ` tending to `+∞`, the infimum `Col_min(n)` of the standard Collatz orbit satisfies `Col_min(n) ≤ f(n)` for almost all `n` in the sense of logarithmic density.  The proof uses ergodic-theoretic and Fourier-analytic methods on a `3`-adic skew random walk.

Lean file: `Collatz/Papers/Tao2022.lean`.

Formalization status: the definitions of `Col`, iterates, and the infimum predicate `Col_min(n) ≤ m` are formalized.  The easy lemma that an orbit reaching `1` has infimum at most `1` is proved.  Tao's main logarithmic-density theorem is recorded as a proposition; no proof is claimed.
