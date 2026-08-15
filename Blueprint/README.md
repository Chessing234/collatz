# Blueprint

The route, from the seed statement to what is actually left.

Nothing here is a proof of Collatz.

Every arrow below is checked in Lean.

## The shape of the argument

A counterexample fails in one of two ways.

Its orbit runs away, or it falls into a cycle.

Pigeonhole forces that dichotomy, and `Structure/Divergence.lean` proves it.

So Collatz splits into two independent problems.

`collatz_iff_no_divergence_and_no_nontrivial_cycle`

## The cycle half

A cycle that touches the basin of `1` is the trivial cycle.

That is `Cycle.mem_trivial_of_periodic_of_reachesOne`.

So any other cycle is a counterexample outright.

Return times are closed under `gcd`, so a cycle has a minimal period.

Periods `1`, `2` and `3` are excluded by hand.

Any nontrivial cycle therefore has period at least four.

For the accelerated map, a cycle of length `L` with `a` odd steps needs `3^a < 2^L`.

Its least element is odd, and it contains both step types.

The cycle half closes if every cycle meets `[1, 1024]`.

## The divergence half

Verification by descent clears `[1, 10000]` inside the kernel.

A counterexample therefore exceeds `10000`.

The congruence identity does the rest of the work.

`T^k(2^k m + r) = 3^{a(r,k)} m + T^k(r)`

The `k`-fold map is affine on each class mod `2^k`.

The multiplier depends only on the residue.

So a whole class descends whenever its multiplier is small enough.

Iterating over moduli gives a sieve.

## The sieve

| modulus | surviving classes | density |
|---------|-------------------|---------|
| `4`     | `3`               | `1/4`   |
| `8`     | `3, 7`            | `1/4`   |
| `16`    | `7, 11, 15`       | `3/16`  |
| `32`    | `7, 15, 27, 31`   | `1/8`   |
| `256`   | 19 classes        | `≈ 7%`  |
| `1024`  | 64 classes        | `1/16`  |

Each row is a theorem, closed by kernel computation.

## What is left

Route A: no divergence, plus every cycle meets `[1, 1024]`.

Route B: every `n > 1` has an accelerated iterate below itself.

Route C: the drop property for the surviving classes.

Three suffice at modulus `16`, eight at modulus `64`.

All of these are equivalent to the conjecture.

None of them is easier by virtue of being shorter.

## Where the method dies

The class `-1 mod 2^K` takes `K` consecutive odd steps.

Its multiplier is `3^K`, which exceeds `2^K`.

So it survives the sieve at every level, for every `K`.

`Obstruction.sieve_never_clears`

The survivor list is never empty.

Refining the modulus will not reduce the pillar count to zero.

Any complete proof needs an argument that is not residue descent.

Knowing where the method dies is the point of the blueprint.
