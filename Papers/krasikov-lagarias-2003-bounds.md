# krasikov-lagarias-2003-bounds

Citation: Ilia Krasikov and Jeffrey C. Lagarias, "Bounds for the 3x+1 problem using difference inequalities", Acta Arithmetica 109 (2003), 237--258.

Source checked: Lagarias's annotated bibliography (arXiv:math/0309224).

Krasikov and Lagarias use difference inequalities to obtain a non-trivial lower bound on the number of integers up to `N` that eventually reach `1` under the `3x+1` iteration.  They produce explicit positive rational constants `p/q` such that at least `N^(p/q)` integers `≤ N` have finite total stopping time for all large `N`.

Lean file: `Collatz/Papers/KrasikovLagarias2003.lean`.

Formalization status: a computable bounded reachability predicate `reachesOneBy n B`, a finite counting function `reachesOneUpToCount N`, and the lower-bound proposition are defined.  The closure property "if `n` reaches `1` then `T(n)` reaches `1`" is proved.

Round LXXVI: the recorded proposition was mis-stated (`N^p ≤ count · N^q`, vacuous at `p = q`) and has been corrected to `N^p ≤ count^q`.  `Collatz/Strategy/TreeCount.lean` proves it with exponent `p/q = 1/5` (`krasikovLagariasLowerBound_holds`), together with the unconditional `N < 22 · count(N)^5` for every `N ≥ 1` (`count_pow_five`).  The proof is the elementary Crandall-style branching bound — two of every three consecutive odd preimages are prime to three, each below `22` times the parent — not the paper's difference-inequality method, and the exponent `0.224` is far below the paper's `0.84`.  `Collatz/Strategy/TreeBranching.lean` (same round) charges every fertile child its own size and certifies exponent `3/8` (`count_pow_eight : N^3 < 8·10^16 · count(N)^8`).  `Collatz/Strategy/TreeHalf.lean` (Round LXXVI.6) formalises the paper's residue-class system at classes modulo `81` with the minimum-over-lifts device and a generated integer certificate, and certifies exponent `1/2` (`count_sqrt : N < 2·10^21 · count(N)^2`); the paper's `0.84` needs its elimination of advanced terms at classes modulo `3^11`.  `Collatz/Strategy/TreeTwoThirds.lean` replaces the elimination by an induction on the absolute bound and certifies exponent `2/3` at classes modulo `243` (`count_cube : N^2 < 4·10^29 · count(N)^3`).  `TreeSevenTenths.lean` repeats it at classes modulo `729` for exponent `7/10` (`count_ten`).
