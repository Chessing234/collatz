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

Then two lemmas combine and beat either one alone.

The least point of a nontrivial cycle exceeds the verified range.

The greatest point is at least twice the least.

Applying the range at the small end and the bound at the large end doubles the constant.

With verification to `60000` that pushes the exclusion to `L <= 26`.

The cycle half now needs only a cap on cycle length.

That is a smaller target than excluding cycles.

## What a cycle must look like

After an odd step the value is `2` mod `3`, since `T(2j+1) = 3j+2`.

So a multiple of three is only ever reached by halving.

Run backwards around a cycle and every predecessor is again an even multiple of three.

The cycle would be all halvings, which strictly decrease.

So no point of a cycle is divisible by three.

An odd greatest point would step up to `(3M+1)/2` and escape its own maximum.

So the greatest point is even, and its successor `M/2` is still on the cycle.

Hence `M >= 2m`: a cycle spans at least a factor of two.

## Runs of odd steps

A number takes `j` consecutive odd steps exactly when it is `-1` modulo `2^j`.

The proof is `2(T(x) + 1) = 3(x + 1)` for odd `x`, plus coprimality of three to powers of two.

Iterating that identity gives the closed form `2^j (T^j(x) + 1) = 3^j (x + 1)`.

A run is not merely bounded, it is computed: the whole climb is one multiplication by `3^j`.

Climbing is therefore rationed: `j` steps up in a row need `x >= 2^j - 1`.

On a cycle every point is at most `M`, so no run anywhere exceeds `log2(M + 1)`.

The least point is `3` mod `4`, so it always begins a run of length two.

Hence `4(M + 1) >= 9(m + 1)`, sharpening `M >= 2m` to `M >= 2.25m + 1.25`.

On the class `7` mod `8` the run has length three and the constant rises to `27/8`.

This also re-derives `m = 3` mod `4` by counting odd steps rather than by exhibiting a descent.

The two derivations agree, which is a check on the development.

It also names the obstruction exactly: every method here fails on `-1 mod 2^k`, and that class is precisely the one that climbs.

## What must follow a run

A chain of `W` halvings is an exact division: `y = 2^W T^W(y)`.

The orbit minimum is never undercut, so `T^{v+W}(m) >= m`.

Combining with the run identity eliminates `T^v(m)` and gives `2^(v+W) m + 2^v <= 3^v (m + 1)`.

This is heaviness with no slack: the averaging bound `a >= 3(k-1)/5` stated exactly, step by step.

With `v = 2` and `W = 2` it reads `16m + 4 <= 9m + 9`, so `7m <= 5`, which is absurd.

So two halvings never follow the minimum's opening run, and the step at time three is forced odd.

On the class `3` mod `8` that forces `m = 11` mod `16`, so `m` is never `3` mod `16`.

The surviving classes modulo `16` are `7`, `11`, `15`.

Those are exactly the classes the computational sieve leaves at level four.

So the sieve is not an accident: at each level it is this bookkeeping, done by search rather than by algebra.

That also says why enlarging it cannot terminate.

Each level asks the same question about one more halving, and `-1 mod 2^k` always answers it.

## The chains

Each chain is hypotheses plus a proved implication to Collatz.

Twenty-nine hypotheses are refuted, not left open.

Four die to the class `-1 mod 2^k`, which takes `k` odd steps in a row.

Any hypothesis whose parameter does not depend on `n` is dead on arrival.

The counterexample set is closed under doubling.

So it is empty or unbounded, and three chains need no dynamics at all.

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

## The next lever

The cycle bound scales with the verified range, and verification is the
bottleneck.

Brute force costs one check per integer, so `60000` already takes minutes of
kernel time.

But the sieve already settles `960` of every `1024` residue classes.

Checking only the `64` surviving classes would cover sixteen times the range at
the same cost.

That would push the cycle-length exclusion from `26` to about `31`.

Past that, `L = 27` admits a cycle-point bound near `1.5` million, so the next
plateau needs verification past `750000`.
