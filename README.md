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

639 theorems.

No `sorry`. No added axioms. No Mathlib.

Everything is proved from the Lean core `Nat` API.

The conjecture itself is open, and this repo does not change that.

## What is proved

Collatz is equivalent to: no orbit diverges, and every cycle is trivial.

Any cycle meeting the basin of `1` is the trivial cycle.

Any nontrivial cycle has minimal period at least four.

An accelerated cycle of length `L` with `a` odd steps needs `3^a < 2^L`.

Its least element is odd.

Every `n` up to `10000` reaches `1`, verified inside the kernel.

`T^k` is affine on each residue class mod `2^k`, with multiplier fixed by the residue.

A minimal counterexample survives a residue sieve: only 64 of 1024 classes mod 1024.

The sieve can never clear, because `-1 mod 2^K` always escapes it.

Terras' density theorem, from scratch: the residues obstructing `k`-step descent
number at most `(243/256)^{k/5}` of all `2^k` classes.

And the matching negative: that obstruction set is unbounded, so no fixed level
of the analysis reaches every integer.

Collatz follows from the drop property for just three classes mod `16`.

No nontrivial accelerated cycle has length `20` or less.

Thirty chains of hypotheses, each with a proved implication to Collatz.

Six of those hypotheses are refuted outright, four by the same obstruction.

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
