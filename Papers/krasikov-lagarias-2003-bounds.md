# krasikov-lagarias-2003-bounds

Citation: Ilia Krasikov and Jeffrey C. Lagarias, "Bounds for the 3x+1 problem using difference inequalities", Acta Arithmetica 109 (2003), 237--258.

Source checked: Lagarias's annotated bibliography (arXiv:math/0309224).

Krasikov and Lagarias use difference inequalities to obtain a non-trivial lower bound on the number of integers up to `N` that eventually reach `1` under the `3x+1` iteration.  They produce explicit positive rational constants `p/q` such that at least `N^(p/q)` integers `≤ N` have finite total stopping time for all large `N`.

Lean file: `Collatz/Papers/KrasikovLagarias2003.lean`.

Formalization status: a computable bounded reachability predicate `reachesOneBy n B`, a finite counting function `reachesOneUpToCount N`, and the lower-bound proposition are defined.  The closure property "if `n` reaches `1` then `T(n)` reaches `1`" is proved.  The main lower-bound theorem is recorded as a proposition; no proof is claimed.
