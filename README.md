# collatz

A small lab for a wild conjecture.

This repo tests the limits of AI.

AI can suggest odd new lemmas.

AI still fails at the whole proof.

The bet is simple.

Collect enough useful lemmas.

Check each one in Lean.

Chain them with care.

Maybe a path appears.

The Collatz conjecture is the beast.

No one has tamed it yet.

This repo does not claim a proof.

It records statements.

It proves what it can.

It rejects loose words.

Every paper gets a file.

Every lemma gets a name.

Every proof must pass CI.

## Status

3 064 theorem and lemma declarations (3 041 public) across 207 modules, 56 690 lines.

Verified range: every positive `n < 1 086 464` reaches 1.  Cycle bound: no accelerated
cycle through a non-reaching point has length below 6809.  **Both are finite results.**
Neither half of the conjecture is proved — see the gap statement at the end of
`RESEARCH.md`.

No `sorry`. No added axioms. No Mathlib.

Everything is proved from the Lean core `Nat` API.

The conjecture itself is open, and this repo does not change that.

## What is proved

Collatz is equivalent to: no orbit diverges, and every cycle is trivial.

Any cycle meeting the basin of `1` is the trivial cycle.

Any nontrivial cycle has minimal period at least four.

An accelerated cycle of length `L` with `a` odd steps needs `3^a < 2^L`.

Its least element is odd.

A number takes `j` consecutive odd steps exactly when it is `-1` modulo `2^j`.

Along such a run, `x + 1` is multiplied by exactly `(3/2)^j`.

So the least point of a cycle climbs to at least `9/4` of itself, improving `M >= 2m`.

Two halvings can never follow the minimum's opening run.

Hence the orbit minimum of a counterexample is never `3` modulo `16`.

That is exactly what the residue sieve computes at level four, here derived algebraically.

The 2-adic valuation of a number is `v` exactly when it is `2^v` modulo `2^(v+1)`.

Three has order two modulo eight, so `v(3^a - 1)` is `v(a) + 2` for even `a`, and `1` for odd.

Hence three has order `2^(L-2)` modulo `2^L`, and `3^a mod 2^L` repeats with that period.

A cycle has `a <= L`, and `L < 2^(L-2)`, so that constraint is empty on every cycle shape.

The gap `2^L - 3^a` is odd, so `v(C) = v(n)` in the affine law of a cycle.


Say a number never drops when its own orbit never goes below it.

Collatz is exactly the statement that `1` is the only number that never drops.

Every structural theorem here specialises to that one predicate.

An excursion is a run of odd steps followed by the halvings after it.

It satisfies the exact identity `2^(v+W) x' + 2^v = 3^v (x+1)`.

Substituting `x' >= x` gives obstructions; substituting the other way proves descent.

For `x >= 2^(v+W)`, the first excursion descends if and only if `3^v < 2^(v+W)`.

One excursion is not enough: `102411` has no contracting first excursion.

The sieve's survivor count rises while its density falls: 3, 8, 19, 64 at levels 4, 6, 8, 10.

So the surviving classes are proliferating, not dwindling to a few stubborn ones.

The sieve is nested, and its survivors form one coherent tower under reduction.

That tower specifies a single 2-adic integer, `-1`, which survives every level at once.

The density rate is sharpened from `3/5 = 0.600` to `17/27 = 0.62963`, against a true threshold of `0.63093`.

The heavy fraction then decays like `0.9695^k` instead of `0.98965^k`.

The rate argument is stated once for any `p/q` with `3^p < 2^q`, and the old rates become instances.

No rate beats `0.96863^k`, so the method is within 0.1 percent of its own ceiling.

The verified range is `307200`, three times what the development is stated against.

So a nontrivial cycle has least point above `307200` and greatest point above `691199`.

Running the map backwards gives infinite descent on the minimal counterexample.

The least number that never drops is not `2` mod `3`, and not `4` mod `9`.

A multiple of three has exactly one preimage, its double, so backward descent provably cannot reach `3 | m`.

Descent works from any point of the orbit, not just from `m`, so no orbit point `= 2` mod `3` lies below `(3m+1)/2`.

That window ends exactly at `T(m)`, so the bound is sharp.

The inverse odd step is a generator: if `3n+1 = 2^j m` and `m` reaches 1, so does `n`.

It yields the family `1, 5, 21, 85, 341, ...`, unbounded, each reaching 1 by an argument not a search.

`T^k` is affine on each residue class mod `2^k`, with multiplier fixed by the residue.

A minimal counterexample survives a residue sieve: only 64 of 1024 classes mod 1024.

The sieve can never clear, because `-1 mod 2^K` always escapes it.

Terras' density theorem, from scratch: the residues obstructing `k`-step descent
number at most `(243/256)^{k/5}` of all `2^k` classes.

And the matching negative: that obstruction set is unbounded, so no fixed level
of the analysis reaches every integer.

Collatz follows from the drop property for just three classes mod `16`.

No nontrivial accelerated cycle has length `26` or less.

No point of an accelerated cycle is divisible by three.

The greatest point of a cycle is even, and at least twice the least.

Every `n` below `102400` reaches `1`, verified inside the kernel by checking
only the sixty-four residue classes the sieve leaves open.

No point of an accelerated cycle is divisible by a large power of two unless it
is correspondingly large; in particular no cycle contains a power of two.

The least point of a cycle is odd, `3` mod `4`, not a multiple of three, hence
`7` or `11` mod `12`, and is followed by a second odd step.

A cycle takes at least two odd steps, and either at least eleven or has length
at most `33`.

The orbit minimum of any counterexample is odd, `3` mod `4`, above `102400`,
never drops, and is heavy at every scale below itself.

That last fact covers the divergence half too, which the cycle lemmas cannot
reach.

Nearly two hundred chains of hypotheses, each with a proved implication to
Collatz.

Thirty-six of those hypotheses are refuted outright.

## Structure

`Collatz/Core/` arithmetic, reachability, pigeonhole, least element.

`Collatz/Search/` kernel-checked verification and stopping times.

`Collatz/Structure/` cycles, divergence, congruences, the sieve, the obstruction.

`Collatz/Strategy/` reductions, and the list of what is left.

`Collatz/Chains/` thirty decompositions, classified in `Index.lean`.

`Papers/` tracks sources.

`Blueprint/` explains the route.

`scripts/` checks integrity.

`.github/workflows/` runs CI.

## Loop

Find a paper.

Extract a lemma.

Write the Lean statement.

Prove it or mark it open.

Link it to its source.

Run the checks.

Push the smallest useful step.

## Build

    lake build Collatz
    bash scripts/check_integrity.sh

The hunt continues.
