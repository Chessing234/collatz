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

## The density theorem

Weight each residue by `2^{a(r,k)}`, the multiplier's exponent.

Residues pair up: `r` and `r + 2^k` take opposite parity steps at time `k`.

So the pair's weights sum to `3` times the common weight one level down.

Summing over pairs gives `W(k) = 3^k` in one induction.

No binomial coefficients, no entropy bound, no logarithms.

A heavy residue has `3k <= 5a`, which follows from `32^k > 27^k`.

Comparing weight against count gives `heavyCount(k)^5 * 8^k <= 243^k`.

The obstruction has density zero, at a geometric rate.

## Cycles are short or nonexistent

On a cycle, `2^L n = 3^a n + b` with `b + 2^L <= 3^L`.

That bound is sharp, and an odd step reproduces it exactly.

Since `3^a < 2^L`, every cycle point is at most `(3^L - 2^L)/(2^L - 3^a)`.

For `L <= 20` that bound falls inside the verified range.

So no nontrivial accelerated cycle has length `20` or less.

The cycle half now needs only a cap on cycle length.

That is a smaller target than excluding cycles.

## Thirty chains

Each chain is hypotheses plus a proved implication to Collatz.

Six hypotheses are refuted, not left open.

Four die to the class `-1 mod 2^k`, which takes `k` odd steps in a row.

Any hypothesis whose parameter does not depend on `n` is dead on arrival.

Five chains are proved equivalent to Collatz, so they are restatements.

The classification lives in `Collatz/Chains/Index.lean`.

## Where the method dies

The class `-1 mod 2^K` takes `K` consecutive odd steps.

Its multiplier is `3^K`, which exceeds `2^K`.

So it survives the sieve at every level, for every `K`.

`Obstruction.sieve_never_clears`

The survivor list is never empty.

Refining the modulus will not reduce the pillar count to zero.

Any complete proof needs an argument that is not residue descent.

The obstruction set is worse than nonempty: it is unbounded.

For every level `k` there are arbitrarily large integers heavy at level `k`.

Density zero is not emptiness, and here the gap is infinite.

Knowing where the method dies is the point of the blueprint.
