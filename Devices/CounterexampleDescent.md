# Devices 16–17 — descent in the space of counterexamples

Assume a non-dropping orbit exists.  Its minimum `m` satisfies
`NeverDrops m`, and `m > 1`.  A descent *in the space of counterexamples*
would be an explicit map sending that orbit (or `m`) to another never-dropping
orbit whose minimum is strictly smaller.  Well-founded descent on `Nat` would
then empty the space.

`T(m)` is not a candidate.  A never-dropper is odd, so
`T(m) = (3m+1)/2 > m`.

Two maps are smaller.  Neither is a self-similarity of the dynamics: the
intertwining `Φ ∘ T = T ∘ Φ` is false at every odd start, and the
one-step growth property that `NeverDrops` requires of an odd start does not
pass to the image.  On a least non-Mersenne never-dropper the cofactor map
produces a dropper by minimality in `Nat`.

No statement about Collatz is made.  In particular this file does not assert
that a never-dropper `> 1` exists, nor that none exists.

Lean: `Collatz/Strategy/CounterexampleDescent.lean`.

---

## Device 16 — the odd cofactor `Φ`

Write `n + 1 = 2^v · u` with `u` odd.  Set

    Φ(n)  ≔  u  =  odd part of `n+1`.

This is the `u` of `IsExcursion`.  For odd `n > 1` one has `v ≥ 1`, hence
`2u ≤ n+1`, hence `Φ(n) < n` (`phi_lt`).  The map is not `T`.

### What self-similarity would have been

Along the opening odd run of length `v` the shift identity is exact:

    T^j(n) + 1  =  2^{v−j} · 3^j · u     (j ≤ v)

(`run_shift`, which is `RunValue.oddRun_value_quot`).  The orbit of `n` during
those `v` steps is an affine function of `u`, not of the orbit of `u`.  After
the run the state is `3^v u − 1`, whose later iterates are the orbit of that
number, not the orbit of `u`.

The intertwining that would make `Φ` a conjugacy is therefore

    Φ(T(n))  =  T(Φ(n)).

It fails at the first step.  An odd step multiplies the shift by `3/2`, so
`T(n)+1 = 2^{v−1} · 3u` and `Φ(T(n)) = 3u`, while `T(u) = (3u+1)/2`.  These
are equal only if `3u = 1`, which does not occur (`not_intertwine`).  Concrete
witness: `Φ(T(27)) = 21 ≠ 11 = T(Φ(27))`.

That is the obstruction, proved, not assumed.  There is no commuting square
that would transport `NeverDrops` from `n` to `u` along the dynamics.

### The implication `NeverDrops m ⇒ NeverDrops Φ(m)`

Two things are true, and they are not Collatz.

**1. On a least non-Mersenne never-dropper the implication is false.**
If `m > 1` never drops, is least with that property among integers `> 1`, and
is not Mersenne (`Φ(m) > 1`), then `Φ(m) < m` with `Φ(m) > 1`, so minimality
gives `¬ NeverDrops Φ(m)` (`phi_kills_least_non_mersenne`).  The space of
counterexamples, ordered by the minimum, is well-founded.  A strictly smaller
image of the least element cannot be a counterexample.

If the least never-dropper *is* Mersenne, then `Φ(m) = 1` (`phi_mersenne`).
The number `1` never drops and is not a counterexample.  Descent in
counterexample space still fails: the image has left the space.

So `Φ` does not send a least counterexample to a smaller counterexample, in
either case.

**2. Transfer along `Φ` would reduce to Mersenne never-droppers, not to `1`.**
If `NeverDrops` passed to the cofactor at every `x > 1`, iterating `Φ` would
reach a never-dropping Mersenne number (`transfer_reaches_mersenne`).  That is
a reduction to the profile obstruction already recorded in `NeverDrops`:
`2^k − 1` satisfies every local clause of `neverDrops_profile` for large `k`.
The implication is not claimed.

### Why a proof of transfer cannot be local: `FirstGrows`

`NeverDrops` on an odd start forces the first excursion landing to sit at or
above the start (`firstGrows_of_neverDrops`).  Call that property
`FirstGrows`.  It is a necessary condition, checkable on actual Collatz
numbers, and it is the weakest local shadow of never-dropping.

The famous pair does **not** refute transfer of `FirstGrows` along `Φ`:

    27 + 1 = 2^2 · 7,     Φ(27) = 7,
    27 ↦ 41 ↦ 31 ≥ 27,    7 ↦ 11 ↦ 17 ↦ 13 ≥ 7.

Both first-grow (`phi_preserves_firstGrows_at_twenty_seven`).  They both
eventually drop, so they are not never-droppers; they only show that the
cofactor of a first-grower *can* first-grow.

Transfer fails on a different pair, of the same shape:

    39 + 1 = 2^3 · 5,     Φ(39) = 5,
    39 ↦ 59 ↦ 89 ↦ 67 ≥ 39,     5 ↦ 8 ↦ 4 ↦ 2 ↦ 1 < 5.

So `FirstGrows 39` and `¬ FirstGrows 5` (`not_phi_preserves_firstGrows`).
The whole family is the same obstruction: for `u ≡ 1 (mod 4)` and `u > 1`,

    n = 8u − 1

has a light first excursion (`2^{3+1} = 16 ≤ 27 = 3^3`), hence first-grows,
while `u` itself has `v = 1` and drops in one excursion
(`phi_firstGrows_obstruction`).  The case `u = 5` is `n = 39`.

Any argument that `NeverDrops m` implies `NeverDrops Φ(m)` by inspecting only
the first excursion is therefore false, because the necessary condition
`FirstGrows` does not transfer.

---

## Device 17 — the adjacent sibling `Ψ`

The cofactor `Φ` strips *every* factor of two from `n+1`.  The adjacent
sibling strips one:

    Ψ(n)  ≔  (n − 1)/2.

On odd `n` this is `Ψ(n)+1 = (n+1)/2` (`psi_shift`).  For `n > 1` one has
`Ψ(n) < n` (`psi_lt`).  A never-dropper is `3 (mod 4)`, so `Ψ(m)` is odd
(`psi_odd_of_neverDrops`).

The odd numbers with the same cofactor `u` are the tower

    n_j  =  2^j · u − 1,     1 ≤ j ≤ v,     n_v = n.

For `j ≥ 2`, `Ψ(n_j) = n_{j−1}`, and the cofactor is invariant
(`psi_preserves_cofactor`).  The last odd sibling is `2u − 1`, not `u`.
Device 16's last collapse, from `2u − 1` to `u`, is the different map
`x ↦ (x+1)/2`.  The two devices are the two granularities of the same
tower, not the same map.

### `FirstGrows` fails on the sibling of 27

Here the pair `27` and `7` *is* the witness, by looking one step off the
cofactor:

    Ψ(27) = 13,     13 ≡ 1 (mod 4),     13 ↦ 20 ↦ 10 ↦ 5 < 13.

So `FirstGrows 27` and `¬ FirstGrows 13` (`not_psi_preserves_firstGrows`).
The cofactor `7` first-grows; the adjacent sibling `13` drops.  Self-similarity
of the tower would have required every `n_j` to first-grow if the top did.

A never-dropper may be `11 (mod 16)` (the profile permits it).  Every such
number has `Ψ ≡ 1 (mod 4)`, hence a first excursion that drops whenever
`Ψ > 1`.  Transfer of `NeverDrops` along `Ψ` would therefore forbid the class
`11 (mod 16)`, against the profile rather than by a new mechanism.  The
implication is not claimed; the local obstruction is the `27 ↦ 13` drop.

---

## What a working descent would have needed, and does not have

A map `Φ` on never-droppers with `Φ(m) < m` and `NeverDrops Φ(m)` would empty
the counterexample space.  The cofactor of `m+1` is the natural candidate
that is smaller and is not `T(m)`.  Three independent obstructions stop it:

1. **No intertwining.**  `Φ ∘ T ≠ T ∘ Φ` at every odd start.  There is no
   conjugacy that could carry an orbit property from `m` to `Φ(m)`.
2. **Minimality.**  On a least non-Mersenne never-dropper, `Φ(m)` is a smaller
   integer `> 1`, hence not a never-dropper.  On a least Mersenne never-dropper,
   `Φ(m) = 1` leaves the space.
3. **The local shadow already fails.**  `FirstGrows` is necessary for
   `NeverDrops` on odd starts and does not pass to `Φ` (witness `39 ↦ 5`) or
   to `Ψ` (witness `27 ↦ 13`).  The pair `27 ↦ 7` shows that the cofactor
   *can* first-grow; it is not a refutation, and it is why the sibling map is
   the complementary test.

None of this decides whether a never-dropper `> 1` exists.
