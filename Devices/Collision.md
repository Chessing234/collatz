# Device: the successor pair, and the landing collision

Agent 8 — orbit-pair / collision.  Not a ranking on the odd cofactor `u`
(already refuted in `ExcursionCofactor`).  Not a reverse-tree comparison
(`ExcursionReverse`).  The object is the joint evolution of two *related*
trajectories.

No Collatz claim is made.

---

## Canonical partner

The difference `T^k(n) − T^k(m)` is interesting only when `m` is pinned to `n`
by the map, not when `m = n + 2^k` is an arbitrary Terras class (those two
starts share the first `k` parities, so the `+1` cancels and the difference is
homogeneous).  The candidates were:

| partner | relation | verdict |
|---|---|---|
| `m = n+1` | unique successor | **the device** |
| `m = u` | odd cofactor of `n+1 = 2^v u` | the successor orbit at time `v`, not a second start |
| `m = 2^v u` | equals `n+1` | same pair |
| nearest Mersenne `2^v − 1` | same first-run length | Terras AP of difference `2^v(u−1)`; homogeneous until the extra halvings desynchronise |
| even inverse `2n` | `T(2n) = n` | a time-shift of one orbit, not a pair |
| odd inverse `(n−1)/3` | unaccelerated parent | the same time-shift |

So the partner is `n + 1`.  Consecutive integers always have opposite parity.
The first step is mixed, and the inhomogeneous `+1` is forced to appear.

---

## Exact evolution of the difference

Write `T` for the accelerated map.  One-step laws, both `Nat` identities
(`odd_succ_step`, `even_succ_step`):

* `n` odd  ⇒  `T(n)  = T(n+1) + n`
* `n` even ⇒  `T(n+1) = T(n) + n + 2`

The `+1` in `3n+1` is the reason these are not `T(n) − T(n+1) = (3/2)(n − (n+1))`
or `(1/2)(n − (n+1))`.  Mixed parity keeps the inhomogeneous term.

Two-step laws for odd `n`:

* `n ≡ 1 (mod 4)` ⇒  `T^2(n+1) = T^2(n) + 1`  (the pair is consecutive again)
* `n ≡ 3 (mod 4)` ⇒  `T^2(n) = T^2(n+1) + 2n + 1`

For arbitrary starts the affine law gives the exact pair identity
(`affine_pair`)

    2^k T^k(n) + 3^{a(m,k)} m + C(m,k)
      =  2^k T^k(m) + 3^{a(n,k)} n + C(n,k)

The `+1` lives in the two accumulators.  When the first `k` parities agree,
both counts and both accumulators match, and this collapses to the homogeneous
rule `2^k (T^k(n) − T^k(m)) = 3^a (n − m)` (`same_parity_pair`).  The successor
pair never satisfies that hypothesis for `k ≥ 1`.

Along an excursion `n + 1 = 2^v u` the partner is a pure-halving orbit
(`partner_orbit`, `partner_is_cofactor`):

    T^j(n+1)  =  2^{v−j} u     (j ≤ v)
    T^v(n+1)  =  u

while `n` runs odd (`peak_vs_partner`):

    T^v(n) + 1  =  3^v · T^v(n+1)  =  3^v u

The cofactor `u` is not an energy.  It is the partner's state at time `v`.
That is the pair evolution `ExcursionCofactor` did not study.

---

## Collision theorem

After the extra halvings the same-time meeting

    T^{v+W}(n)  =  T^{v+W}(n+1)

is `e = T^W(u)`, hence the divisibility

    2^W · T^W(u) + 1  =  3^v u.

The shift bound `2^k (T^k(x)+1) ≤ 3^k (x+1)` (`orbit_succ_le`) then overruns
as soon as `W < v` (`no_landing_collision_of_v_gt_W`).

Every light excursion has `W < v` (`light_W_lt_v`: otherwise `4^v ≤ 3^v`).
Therefore a light excursion **cannot** meet its successor orbit at landing
time (`no_landing_collision_of_light`).

A never-dropper's first landing stays at or above the start.  On a *light*
first excursion that is the non-dropping condition at time `v+W`, and the
collision theorem says that same-time equality with the partner is impossible
there.  The theorem does not say a never-dropper cannot exist; it says that
if one exists and its first excursion is light, the two trajectories do not
collide at that time.  The trivial cycle `1 ↦ 2 ↦ 1` is not light
(`2^{1+1} = 4 > 3`) and does not collide (`T^2(1) = 1 ≠ 2 = T^2(2)`).

---

## `expStep` test

`expStep` is `3x/2` on evens and `(3x+1)/2` on odds.  It agrees with `T` on
odd inputs.  On the successor pair with `n` odd it fails the one-step law
(`expStep_succ_of_odd`, `expStep_ne_odd_succ_step`):

    expStep(n+1)  =  expStep n + 1     ≠     T(n+1) + n

The even side is treated as if the inhomogeneous term were `0`, so the
difference collapses to `1`.

Along the opening run the contrast is exact (`exp_pair_stays_shift` versus
`peak_vs_partner`):

    E^v(n) + 1  =  E^v(n+1)           (expStep keeps the shift pair)
    T^v(n) + 1  =  3^v · T^v(n+1)     (Collatz maps the partner to the cofactor)

Worked value: `7` has `(v,u,W) = (3,1,1)`.  Collatz sends `8` to `1` in three
steps; `expStep` sends `8` to `27`.  The landing `13` is not `T^4(8) = 2`.

The device uses the even contraction of `T`.  It is false of `expStep`.

---

## What this is not

* Not a Lyapunov on `u`.  The arrows `7 ↦ 13` (`u: 1 → 7`) and `27 ↦ 31`
  (`u: 7 → 1`) already kill every energy of `(v,u)`.  The partner of `7` is
  `8`, whose orbit is the cofactor trajectory, not a ranking.
* Not `ExcursionReverse`.  The reverse tree compares `n` with its *landing*,
  one orbit.  This file compares `n` with `n+1`, two orbits.
* Not a residue covering, not a comparison of `2^L` against `3^a` except as
  the already-named light/heavy split used to get `W < v`.
* Not a proof that `1` is the only never-dropper.
