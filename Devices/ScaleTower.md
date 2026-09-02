# Devices 14–15 — the scale tower, and the connection that compactness does not see

The 2-adic tower of residues is compact.  The never-dropping condition is not a
2-adic condition.  These two sentences are the whole device.  What follows is
the *connection* that makes them a single object, rather than a list of residue
classes.

No claim about Collatz is made.  In particular this file does not assert that
the inverse limit of the tower is empty, nor that it is `{1}`.

---

## Device 14 — the connection `π_k`

Write `T` for the accelerated map (`n/2` even, `(3n+1)/2` odd).  The
**k-horizon** of a positive integer `n` is the finite never-dropping condition

    Horiz_k(n)  ≔  ∀ j ≤ k,  n ≤ T^j(n).

This is *not* membership in a residue class modulo `2^k`.  The first `k` parities
are a class modulo `2^k`; the inequalities `T^j(n) ≥ n` compare two real numbers.
Those inequalities are the content.

A number in `Horiz_k` either does or does not lie in `Horiz_{k+1}`.  The
criterion uses none of the first `k` letters.  It uses only the current height
`v ≔ T^k(n)` against the start `n`:

> **Lift law.**  If `Horiz_k(n)`, then `Horiz_{k+1}(n)` if and only if
> `v` is odd, or `v` is even and `v ≥ 2n`.

- An odd step cannot decrease: `(3v+1)/2 ≥ v` for odd `v`, and `v ≥ n` already.
  Odd current values **always lift**.
- An even step is `v ↦ v/2`.  This stays above the start if and only if
  `v ≥ 2n`.

So the fibre of `π_k : Horiz_{k+1} → Horiz_k` over `n` is either `{n}` or empty,
and it is empty precisely when the current value sits in the **drop window**

    W(n)  ≔  { v even | n ≤ v < 2n }.

That interval is a bounded subset of the Archimedean line, of length `n`.  It is
not a union of arithmetic progressions modulo `2^k`.  The connection that lifts
a non-dropping condition from scale `k` to scale `k+1` is the statement
"`T^k(n)` is outside `W(n)`".

Two immediate consequences, both identities:

1. Once `T^k(n)` is odd, the next horizon is free.  The only obstruction to an
   infinite lift is an even current value in `[n, 2n)`.
2. Once the orbit has a *floor* at `2^a` with `2^a ≥ n` — every later value is
   at least `2^a` — the drop window `W(n)` lies strictly below the floor, so
   **every later lift is free**.  An infinite non-dropping condition that has
   already climbed past its own start is a finite prefix plus a floor, not an
   infinite family of residue constraints.

That is the connection.  It is a comparison of real sizes, one scale at a time.

---

## Device 15 — the inverse system, and the missing coordinate

Let `X_k` be the set of integers `n ≥ 1` with `Horiz_k(n)`.  Inclusion gives an
inverse system of sets

    X_1  ←π_1—  X_2  ←π_2—  X_3  ←  ⋯

A thread in the inverse limit is a single integer that lies in every `X_k`, i.e.
an infinite non-dropping orbit.  (Equivalently: orbit *segments* of length `k`
with `π_k` forgetting the last value; a thread is then an infinite orbit that
never drops.  The two limits are the same set of starts.)

Each `X_k` is nonempty: `2^{k+2} − 1` opens with `k+2` odd steps, and an odd
step never decreases, so it is a `k`-horizon.  If the system were an inverse
system of nonempty *compact* spaces with continuous projections, the inverse
limit would be nonempty.  That is the compactness argument, and it is the
argument that does not apply.

### Why compactness fails

`X_k` is a discrete subset of `ℝ`.  It is unbounded: `2^{k+m} − 1 ∈ X_k` for
every `m ≥ 2`.  Unbounded discrete subsets of `ℝ` are not compact.  More
quantitatively, the two constructive points

    s(k)   = 2^{k+2} − 1,     s(k)+  = 2^{k+3} − 1

both lie in `X_k`, and their separation is

    s(k)+ − s(k)  =  2^{k+2}.

So already the two-point subset `{s(k), s(k)+ } ⊂ X_k` has Euclidean diameter
`2^{k+2}`, which tends to infinity with `k`.  Finite-scale non-drop cylinders
are nonempty, and their diameters in `ℝ` go to infinity.  That is the exact
reason a compactness (or König) argument on the `X_k` cannot fire: there is no
compact of `ℝ` containing a section of the tower at all scales.

The same obstruction read off the constructive section alone: `s(k) → ∞`, so
any bounded interval of `ℝ` contains `s(k)` for only finitely many `k`.

### The missing noncompact coordinate, named

The residue map `n ↦ n mod 2^k` is a map `X_k → ℤ/2^kℤ`.  The target is finite,
hence compact, the projections are the ring maps `ℤ/2^{k+1} → ℤ/2^k`, and the
inverse limit is `ℤ_2`, which is compact.  `lim¹ = 0` on that tower: every
coherent sequence of residues is a 2-adic integer.  That compactification is
exactly what the repository already recorded (`FiniteInfinite.Tower`,
`ExtensionClass.bounded_tower`).

What the residue map **discards** is the Archimedean size of `n` — the number
`n` itself, as a point of `ℕ ⊂ ℝ`.  Call it `ArchSize(n) ≔ n ∈ ℝ`.  The
never-dropping inequalities are comparisons in this coordinate.  The drop window
`W(n)` is an interval of `ℝ` whose width is `ArchSize(n)`.  The floor test
`2^a ≥ n` is a comparison of `ArchSize(n)` against a scale.  None of these is
continuous (or even well-defined) after reducing modulo `2^k`.

The fibre of the residue map is mixed.  The numbers `1` and `5` are congruent
modulo `4`, so they carry the same length-`2` parity word, but `Horiz_2(1)` holds
and `Horiz_2(5)` fails: `T^2(1) = 1 ≥ 1` while `T^2(5) = 4 < 5`.  Same 2-adic
digit, different real size, different lift.  The connection `π_k` is invisible
to the compact tower.

That is the missing noncompact coordinate: **`ArchSize(n) ∈ ℝ`**, the real
starting height.  Compactness of the residue tower cannot see it, and the
non-dropping condition lives entirely in it.

### What this is not

- It is not a covering of `X_k` by arithmetic progressions modulo `2^k`.  The
  lift law does not mention residues.
- It is not a claim that `⋂_k X_k = {1}`.  That intersection is the set of
  never-droppers, and naming it does not decide its cardinality.
- It is not a compactness proof in `ℤ_2`.  The 2-adic inverse limit is
  nonempty for a different reason (every prefix of `1^ω` is realised) and its
  points need not be positive integers (`FiniteInfinite.padic_eq_int_iff`).
- It is not a ranking, a Lyapunov function, or an AP sieve.

The device is the pair `(π_k, ArchSize)`: a lift of non-dropping from one
horizon to the next that is a real comparison, and the coordinate that every
compact 2-adic argument throws away.  The theorem that makes the failure of
compactness exact is: `X_k ≠ ∅` and `diam_ℝ(X_k) = ∞`, with the constructive
lower bound `diam ≥ 2^{k+2}`.
