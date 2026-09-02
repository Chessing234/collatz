# Device: the unconstrained increment

This is not a proof of the Collatz conjecture.  It isolates a single integer
parameter that the map is allowed to vary, proves that *some* choice of that
parameter always reaches `1`, and records why the constant choice `1` is the
only member of the usual family `3n+d` for which “reaches `1`” can even be
the right question.

## The object

Fix a natural number `d`.  The **incremented step** is

```
step_d(0)  =  0,
step_d(n)  =  n/2          if n is even and n > 0,
step_d(n)  =  3n + d       if n is odd.
```

The ordinary Collatz step is `step_1`.  The folded odd branch that the
conjecture is often stated with, `n ↦ (3n+1)/2`, is `step_1` followed by the
forced halving (an odd input produces an even value, proved below).

An **unconstrained increment** for a positive integer `n` is a positive odd
natural number `d` such that some iterate of `step_d` equals `1`.  The pair
`(d, t)` with `step_d^t(n) = 1` is an **unconstrained certificate**.

The word *unconstrained* means: `d` is allowed to depend on `n`.  It is not
required to be `1`, and it is not required to be the same integer for every
start.  The Collatz conjecture is exactly the claim that the *constrained*
choice `d = 1`, independent of `n`, is a certificate for every positive
integer.

## What is proved

**Every positive integer has an unconstrained certificate.**

The argument is elementary and does not use the Collatz conjecture.

- If `n` is a positive even integer, one halving produces a strictly smaller
  positive integer, and one repeats.
- If `n` is odd and positive, there exists a power of two strictly larger
  than `3n`, say `3n < 2^K`.  The difference `d = 2^K − 3n` is then a
  positive odd integer (even minus odd), and

      step_d(n)  =  3n + d  =  2^K.

  From a power of two, repeated halving reaches `1`, and the even branch of
  `step_d` ignores `d`.

In particular, the one-step increment for `n = 1` is `d = 4 − 3 = 1`, and
the one-step increment for `n = 5` is `d = 16 − 15 = 1`.  For `n = 7` the
smallest such increment is `d = 32 − 21 = 11`, not `1`.  So a certificate
can exist with `d ≠ 1`; Collatz asks for the uniform value `1` even when a
single odd step with increment `1` does not land on a power of two.

## The theorem that would prove Collatz

**Straightening.**  Suppose that whenever `n` admits some unconstrained
certificate `(d, t)`, it also admits a certificate of the form `(1, t')`.
Then every positive integer reaches `1` under `step_1`, which is the
Collatz conjecture.

The hypothesis is not proved here.  Existence of some `d` is the theorem
above; replacing that `d` by `1` is the whole problem.  The rest of the
note records why `1` is the distinguished constant to straighten *to*, by
comparing the three neighbouring maps named in the query.

## Why `3n` fails (even branch still `n/2`)

Take increment `d = 0`.  This `d` is even, so it is not an unconstrained
increment in the sense above.  On an odd input,

    3n  is odd,

because an odd number times an odd number is odd.  The map never becomes
even, the halving branch is never taken, and for `n > 1` one has
`n < 3n < 9n < ⋯`.  No odd start larger than `1` can reach `1`.

The `+1` is what forces a factor of two: `3n` odd implies `3n+1` even.
That is the only arithmetic role of the inhomogeneous term that is needed
to even *state* a covering of the odd integers by a path that uses
halving.  Without it there is nothing to straighten.

## Why `3n+5` fails

`d = 5` is odd, so parity is flipped and the map is not the `3n` obstruction.
A different obstruction appears: **every odd positive `d` has a tautological
3-cycle**

    d  ↦  4d  ↦  2d  ↦  d.

Indeed `d` is odd, so `3d + d = 4d`, then two halvings return to `d`.  The
unique odd point of this cycle is `d` itself.  The cycle contains `1` if and
only if `d = 1`.

For `d = 5` the tautological cycle is `5 ↦ 20 ↦ 10 ↦ 5`.  It does not
contain `1`.  So `5` has no `step_5`-certificate, even though (as above) it
does have a `step_1`-certificate, because `3·5+1 = 16`.

Separately, `1` is still periodic for `3n+5`:

    1  ↦  8  ↦  4  ↦  2  ↦  1,

since `3+5 = 8 = 2^3`.  Thus `3n+5` has *at least two* attractors that
contain an odd positive integer, `{1,2,4,8}` and `{5,10,20}`.  The
statement “every positive integer reaches `1`” is false, not because
halving is unavailable, but because the tautological cycle of `d` is a
second sink.

## Why `3n+7` fails

Again `d = 7` is odd, so parity flips.  The tautological cycle is
`7 ↦ 28 ↦ 14 ↦ 7`, which does not contain `1`.

The start `1` does not join that cycle either: `3·1+7 = 10`, and then

    1  ↦  10  ↦  5  ↦  22  ↦  11  ↦  40  ↦  20  ↦  10  ↦  ⋯

which is a 6-cycle on `{5,10,11,20,22,40}`, still missing `1`.  So even the
start `1` fails to return to `1` under `step_7` after a positive number of
steps, and `5` and `7` never reach `1`.

The extra fact `1+7 = 8 = 2^3` (the kernel of `1` is a power of two) does
not save the map: unlike `d = 1`, the tautological cycle and the orbit of
`1` are distinct.

## Why `3n+1` is the special constant

Among odd positive increments `d`, the following are equivalent:

1. `1` lies on the tautological cycle `{d, 2d, 4d}`;
2. `d = 1`;
3. `step_d(1) = 4d` (the first odd step from `1` lands on the tautological
   cycle).

So `d = 1` is the unique odd positive increment whose tautological 3-cycle
*is* the cycle of `1`.  Equivalently, it is the unique such increment for
which the covering problem “does every positive integer reach `1`?” is the
same question as “does every positive integer reach the tautological
cycle?”.

Two supporting identities, both `Nat` equalities, explain the same
distinction in affine coordinates.  Write `fold_d(n) = (3n+d)/2` for odd
`n` (legal because `3n+d` is even).  Then

    2 · (fold_1(n) + 1)  =  3 · (n + 1),
    2 · (fold_5(n) + 5)  =  3 · (n + 5),
    2 · (fold_7(n) + 7)  =  3 · (n + 7).

An odd step multiplies the kernel `n+d` by `3/2`.  Reaching `n = 1` is
reaching kernel `2` when `d = 1`, kernel `6` when `d = 5`, and kernel `8`
when `d = 7`.  Only for `d = 1` is that kernel the generator of the
2-powers, which is exactly the landing of the one-shot construction at
`n = 1`.

## What this is not

- It is not a claim that `d = 1` is a certificate for every `n`.
- It is not a claim that unconstrained certificates with `d ≠ 1` can be
  rewritten as Collatz trajectories.  That rewriting is the open
  straightening statement above.
- It is not a statement about residue classes, symbolic words, or a
  comparison of `2^L` against `3^a`.  The only arithmetic used is parity,
  the existence of a power of two above a given integer, and the three-step
  identity `d ↦ 4d ↦ 2d ↦ d`.

## Formalised

`Collatz/Strategy/DeviceUnconstrained.lean` proves: existence of
unconstrained certificates; the tautological cycle and the criterion
`d = 1`; the `3n` parity lock; the cycles of `5` under `3n+5` and of `7`
under `3n+7`; the kernel identities; and that Collatz is equivalent to
every positive integer having a certificate with increment `1`.  Zero
`sorry`.  No Collatz claim.
