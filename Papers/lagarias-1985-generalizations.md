# lagarias-1985-generalizations

Citation: Jeffrey C. Lagarias, "The 3x+1 problem and its generalizations", The American Mathematical Monthly 92 (1985), 3--23.

Source checked: Lagarias's annotated bibliography (arXiv:math/0309224) and the original Monthly article.

The paper surveys the standard Collatz map `C(n) = n/2` for even `n` and `3n+1` for odd `n`, the accelerated map `T(n) = n/2` for even `n` and `(3n+1)/2` for odd `n`, and records the equivalence of the standard Collatz conjecture with the accelerated conjecture and with the statement that every `n > 1` has a finite stopping time under `T`.

Lean file: `Collatz/Papers/Lagarias1985.lean`.

Formalization status: the one-step expansion facts (`T(n) = C(n)` for even `n`, `T(n) = C^2(n)` for odd `n`) are proved. The main equivalence and the stopping-time converse are recorded as propositions; the delicate indexing argument needed for the converse direction is not claimed.
