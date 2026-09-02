# Device: the +1-carry cocycle

Agent 4 — cocycle.  Broader than a potential.  Not a ranking, not a
renamed valuation budget.

## Exact definition

A **cocycle** for the accelerated map `T` is an integer-valued `A(n,k)`
satisfying

    A(n, k+ℓ)  =  A(n,k)  +  A(T^k n, ℓ)

for every start `n` and every split of the window.  Every coboundary
(potential)

    A(n,k)  =  Φ(T^k n) − Φ(n)

is a cocycle.  The converse is false: a cocycle is a path integral of a
1-cochain `α(n) = A(n,1)`, and it is a coboundary if and only if `α = Φ∘T − Φ`.
Rankings are coboundaries that decrease.  The logarithmic increment
`log T^k(n) − log n` is the coboundary of `log`.  The sum of extra halvings
`Σ W_i` is the path integral of the even-run lengths — the valuation budget,
already closed.

The device is the 1-cochain that the `+1` in `3n+1` actually feeds, on even
steps, into the 3-adic valuation of `u = n+1`.

    Injects(x)  ≔  x even  and  x ≡ 1 (mod 3)
    injBit(x)   ≔  1 if Injects(x), else 0
    injCount(n,k) ≔  Σ_{i < k} injBit(T^i n)

This is the **+1-carry**, or **injection count**: an even step with
`x ≡ 1 (mod 3)` is exactly the case `3 ∣ (T x + 1)`
(`ThreeAdic.three_dvd_even_step_iff`).  In base 3, adding `1` to `x+1` to
produce `x+2` carries through the trailing `2`-digits; the carry happens
precisely on this class, and the even step then injects those threes into
`u = Tx+1`.

It is not `v₂` of a polynomial of the endpoints: at `x = 4`,
`injBit(4) = 1` while `4+1` and `T(4)+1 = 3` are both odd, so the coboundary
`v₂(T x + 1) − v₂(x + 1)` is zero.  It is not `Σ W_i`: two even runs of
length one contribute `W = 2` and `injCount = 0`; one even run of length two
contributes `W = 2` and `injCount = 1`.

## Why it is not a potential

`injCount` is a cocycle by additivity of a path sum
(`DeviceCocycle.injCount_add`).  It is not a residue-class potential
modulo 6: any `Φ` with `Φ(T n) = Φ(n) + injBit(n)` that identifies the
class `n ≡ 2 (mod 6)` at `{2, 8}` (so `Φ 8 = Φ 2`) yields

    Φ(2) = Φ(4) + 1,     Φ(4) = Φ(8),     Φ(8) = Φ(2),

which is `Φ(4) = Φ(4) + 1` (`inj_not_class_potential`).  The 1-cochain
*is* a class function modulo 6 (`injBit x = 1` iff `x ≡ 4 (mod 6)`), but
`T` does not descend to `ℤ/6`, so the coboundary equation cannot hold for
a class function.

## Winding around powers of 3

The two nontrivial classes modulo 3 are the two sides of the first power of
three in the shift `u = n+1`:

| class of `n` | meaning | even-step effect on `u` |
|---|---|---|
| `n ≡ 2 (mod 3)` | `3 ∣ (n+1)` — sitting on a power of 3 | **kill**: `v₃(u)` drops to 0 |
| `n ≡ 1 (mod 3)` | `3 ∣ (n+2)` — the +1-carry | **inject**: `v₃(Tx+1)` rises from 0 |

An odd step always lands on `2 (mod 3)` (`odd_step_mod_three`).  So the first
even step after an odd run is a kill, never an injection
(`injBit_step_of_odd`).  Consecutive even steps then *alternate*:

    ≡ 2  →  ≡ 1  →  ≡ 2  →  ≡ 1  →  ⋯
    kill    inj     kill    inj

(`even_kill_to_inj`, `even_inj_to_kill`).  That alternation is the winding of
`n` around `{3^j}` in the only coordinate the even branch can see: the two
nonzero residues modulo 3.  After an odd start, an even run of length `e`
therefore contributes exactly `⌊e/2⌋` injections — a function of the run
lengths, but not their sum.

The unsigned winding around `3^1` itself (the bit `3 ∣ (n+1)` flipping) is
vacuous for odd starts: after the first odd step the orbit never meets a
multiple of 3, so every subsequent even point is `≡ 1` or `≡ 2 (mod 3)` and
every step flips the bit.  The device is the *carry*, not that bit.

## One nontrivial theorem on never-droppers

For the least never-dropper `m`, every even orbit point `≡ 1 (mod 3)` is at
least `3m+1` (`ThreeAdic.even_orbit_one_mod_three_ge`).  In cocycle language:

> **Support law.**  If every orbit point `T^i(m)` with `i < k` lies below
> `3m+1`, then `injCount(m,k) = 0`.
> (`injCount_eq_zero_of_low_window`)

All injections of a least never-dropper live at height `≥ 3m+1`.  The cocycle
law then says the whole-orbit count is the count of the *high* tail: if the
prefix of length `τ` stays below `3m+1`,

    injCount(m, τ+ℓ)  =  injCount(T^τ m, ℓ).

This is a constraint on never-dropping orbits.  It is not a proof that none
exist except `1`, and it is not claimed to be.

## `3x+d` test

On even inputs the map is still `x ↦ x/2`, independent of `d`.  The
1-cochain `Injects` is therefore `d`-blind.  Genuine cycles see it:

| map | cycle | injection? |
|---|---|---|
| `3x+1` | `1 → 2 → 1` | no (`injCount 1 k = 0`) |
| `3x−1` | `5 → 7 → 10 → 5` | yes, at `10` |
| `3x+5` | `1 → 4 → 2 → 1` | yes, at `4` |
| `3x+7` | `5 → 11 → 20 → 10` | yes, at `10` |

The `3x−1` injection at `10` sits *below* `3·5+1 = 16`.  So the support law
`height ≥ 3m+1` is `d = 1`-specific: it consumes the master bound, not the
cocycle law.  The cocycle law itself holds for every `3x+d` (same even
branch, same residue test).  Diagnostic 3 of `CLOSURE.md` does not fire on
the law, and does fire on the window.

## `expStep` test

`expStep` replaces the even branch by `x ↦ 3x/2`.  The analogue of
injection is `3 ∣ (expStep x + 1)` on even `x`.  This **never happens**:

    2 · (expStep x + 1)  =  3x + 2  ≡  2 (mod 3),

so `3` cannot divide the successor shift (`expStep_even_not_three_dvd_succ`).
The injection cocycle of `expStep` is identically zero.

Consequently:

* a theorem "`NeverDrops` forces a positive injection" is false of `1` and
  of every `expStep` orbit;
* a theorem "`NeverDrops` forces vanishing injection" is true of `1` and of
  every `expStep` orbit.

The natural cocycle does not separate the unique known never-dropper from the
divergence-half witness.  It does not obstruct.

## What the three candidates became

| candidate | verdict |
|---|---|
| `v₂` of a polynomial of the orbit | endpoint form `v₂(T^k n + c) − v₂(n+c)` is a coboundary (a ranking); path-sum `Σ v₂(T^i n + 1)` is the valuation budget.  Both excluded.  Witness that Inj is neither: `n = 4`. |
| winding of `n` around powers of 3 | the `3^1`-bit flip is vacuous on odd starts; the residual winding is the even-run alternation kill/inj on `ℤ/3`, which *is* Inj after an odd step. |
| `+1` injection count | the device.  Exact cocycle.  Supported high on the least never-dropper.  Silent on `1` and on `expStep`. |

## No Collatz claim

Nothing here asserts that `1` is the only never-dropper, that every orbit
reaches `1`, or that a divergent orbit is impossible.  The formal content is
an exact additive law, a window of support, a class-potential obstruction,
and two filters.
