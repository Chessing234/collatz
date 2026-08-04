# everett-1977-iteration

Citation: C. J. Everett, "Iteration of the number-theoretic function f(2n)=n, f(2n+1)=3n+2", Advances in Mathematics 25 (1977), 42--45.

Source checked: Lagarias's annotated bibliography (arXiv:math/0309224).

Everett's function `f` is the accelerated Collatz map `T(n) = n/2` for even `n` and `(3n+1)/2` for odd `n`.  He gave a probabilistic/density analysis showing that almost all starting values have a finite stopping time.

Lean file: `Collatz/Papers/Everett1977.lean`.

Formalization status: the identification of Everett's map with the accelerated step, parity observations, and computability of parity vectors are recorded.  The density-`1` stopping-time theorem is recorded as a proposition using the bounded approximation `hasStoppingTimeBy n N`; no proof of the density result is claimed.
