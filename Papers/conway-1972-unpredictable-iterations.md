# conway-1972-unpredictable-iterations

Citation: John H. Conway, "Unpredictable iterations", Proceedings of the 1972 Number Theory Conference (University of Colorado, Boulder, CO, August 14--18, 1972), pp. 49--52. MR 52 #13717.

Source checked: Lagarias's annotated bibliography, arXiv:math/0309224 [math.NT], item 43, which summarizes: "This paper states the 3x+1 problem, and shows that a more general function iteration problem similar in form to the 3x+1 problem is computationally undecidable." Also MathWorld, "Collatz Problem" (Wolfram Research): "Conway (1972) also proved that Collatz-type problems can be formally undecidable." Kurtz and Simon, "The Undecidability of the Generalized Collatz Problem" (TAMC 2007) restate Conway's theorem as: given a Collatz function g, it is undecidable whether, for all integers x of the form 2^k, some iterate g^(i)(x) equals 1.

The paper studies the class of *generalized Collatz maps*: functions given on each residue class `n ≡ i (mod m)` by an affine law `g(n) = (a_i n + b_i)/m`. The classical `3x+1` step map (even `n/2`, odd `3n+1`) and the accelerated map `T(n) = (3n+1)/2` for odd `n` are members of this family. Conway proved that the iteration problem for this family is algorithmically undecidable: his construction encodes register-machine computations, with integers of the form `2^k` standing for configurations, so that reachability of `1` simulates halting.

Lean file: `Collatz/Papers/Conway1972.lean`.

Formalization status: generalized Collatz maps are defined; the classical step map and the accelerated map are proved to be instances of the family, and their iterates are shown to agree with `Collatz.orbit` and `acceleratedOrbit`; every power of two is proved to reach `1` under the step, accelerated, and halving-only maps (induction, via the halving branch `n/2`); several finite computations are checked, including the arm of `27` (111 steps in the classical map, 70 in the accelerated map). Conway's undecidability theorem is recorded as propositions; no proof of it is claimed.
