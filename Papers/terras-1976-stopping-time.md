# terras-1976-stopping-time

Citation: Riho Terras, "A stopping time problem on the positive integers", Acta Arithmetica 30 (1976), 241--252.

Source checked: MathWorld, "Collatz Problem" (Wolfram Research), which lists Terras (1976) and Terras (1979); and Lagarias's annotated bibliography, arXiv:math/0309224 [math.NT].

The paper introduces the accelerated 3x+1 map `T(n) = (3n+1)/2` for odd `n` and `T(n) = n/2` for even `n`, and defines the stopping time `σ(n)` as the least `k ≥ 1` such that `T^k(n) < n`. The main result is that the set of positive integers with a finite stopping time has natural density `1`.

A finer density-existence result is given in Terras, "On the existence of a density", Acta Arith. 35 (1979), 101--102.

Lean file: `Collatz/Papers/Terras1976.lean`.

Formalization status: the accelerated map, the stopping-time predicate, a bounded stopping-time value function, and several finite computations (including the general fact that every even `n ≥ 2` has stopping time `1`, and the values `σ(2)=1`, `σ(3)=4`, `σ(4)=1`, `σ(5)=2`, `σ(7)=7`) are checked in Lean. The natural-density-`1` theorem is recorded as a proposition; no proof of it is claimed.
