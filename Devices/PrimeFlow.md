# Device: prime-flow

Agent 7 — prime-flow.  The state is the valuation vector `P(n) = (v_p(n))_p`,
not `v₂` alone and not `v₃(n+1)` (`ThreeAdic`).

No Collatz claim.

---

## What was scanned

Odd primes dividing `3^k ± 1` for `k ≤ 20`, then every odd start `n < 20 000`
(truncated invariant to `30 000`).  Smallest interesting primes:

| `k` | odd primes of `3^k − 1` | odd primes of `3^k + 1` |
|---|---|---|
| 2 | — | 5 |
| 3 | **13** | **7** |
| 4 | **5** | 41 |
| 5 | 11 | 61 |
| 6 | 7, 13 | 5, 73 |

For each excursion `(v, u, W, e)` of such an `n`, compared `v_p(u − 1)`,
`v_p(3^v − 1)`, and `v_p(e)` whenever `p ∣ 3^v − 1`, and the plus-side
analogue `v_p(u + 1)` whenever `p ∣ 3^v + 1`.  Zero failures of the
ultrametric prediction.

Linear combinations of `P(n)` itself, coefficients in `{−1,0,1}` on
`{2,5,7,11,13}`, were tested for same-sign drift on both elementary
arrows `n ↦ n/2` (even) and `n ↦ 3n+1`.  The only non-mixed combinations
are the multiples of `v₂`, and those have **opposite** signs on the two
arrows.  Every nonzero odd-prime weight mixed `3n+1`.

---

## Negative: no ranking from `P(n)`

On `n ↦ n/2` an odd prime is frozen (`odd_dvd_frozen_under_half`).  Only
`v₂` moves, and it falls by exactly one.

On `n ↦ 3n+1` the same odd coordinate is mixed:

* `v₅` falls at `n = 5` (`5 ∤ 16`) and rises at `n = 3` (`5 ∣ 10`);
* `v₁₃` falls at `n = 13` (`13 ∤ 40`) and rises at `n = 17` (`13 ∣ 52`);
* `v₂` on odd `n` *rises* (`v₂(3n+1) ≥ 1`).

So no finite ℤ-linear combination of coordinates of `P(n)` is a joint
Lyapunov for both arrows, except the zero combination.  The `v₂`-only
ranking is the one the brief excluded.

The combination that *does* have forced drift lives on different linear
forms of the excursion datum, not on `P(n)` itself.

---

## Positive: transport along an excursion

Write `n + 1 = 2^v u` with `u` odd, and `3^v u = 2^W e + 1` with `e` odd
(`IsExcursion`).  The peak splits two ways:

    3^v u − 1  =  (3^v − 1) u + (u − 1)
    3^v u − 1  =  3^v (u + 1) − (3^v + 1)

and equals `2^W e`.

**Minus law.**  For every odd `m ∣ 3^v − 1`,

    m ∣ (u − 1)  ↔  m ∣ e.          (`flow_minus`)

**Plus law.**  For every odd `m ∣ 3^v + 1`,

    m ∣ (u + 1)  ↔  m ∣ e.          (`flow_plus`)

Taking `m = p^k` for every `k ≤ v_p(3^v − 1)` is the truncated invariant

    min(v_p(u − 1), α)  =  min(v_p(e), α),    α = v_p(3^v − 1),

scanned with zero exceptions.  That is a finite combination of
divisibility bits — one per prime dividing `3^v ± 1` — with **forced
drift zero** along the excursion.

Named instances, matching the leftover / four-run classes already in
the excursion files:

* `v = 3`, `13 ∣ 3^3 − 1`: `13 ∣ (u − 1) ↔ 13 ∣ e`;
* `v = 4`, `5 ∣ 3^4 − 1`: `5 ∣ (u − 1) ↔ 5 ∣ e`;
* `v = 3`, `7 ∣ 3^3 + 1`: `7 ∣ (u + 1) ↔ 7 ∣ e`.

Residue form of the minus law: `n ≡ 2^v − 1 (mod m)` iff `m ∣ e`, because
`u − 1 = (n − (2^v − 1)) / 2^v` and `m` is odd.

---

## Forced drop of surplus

The truncated invariant is a ceiling, not a conservation of the full
valuation.  If `v_p(u − 1) > α = v_p(3^v − 1)`, ultrametric forces
`v_p(e) = α`: the extra powers drop.

In divisibility language, for a prime `d` with `d ∣ 3^v − 1` and
`d^2 ∤ 3^v − 1`, if `d^2 ∣ (u − 1)` then `d ∣ e` and `d^2 ∤ e`
(`flow_drop`).  Instantiated at the two smallest such primes:

* `v = 4`, `α_5 = 1`: `25 ∣ (u − 1)` ⇒ five-drop (`five_drop_of_v_four`);
  witness numbers `five_drop_numbers`: cofactor `51 = 1 + 2·25`, landing
  `2065 = 5 · 413` (the excursion start is `815`).
* `v = 3`, `α₁₃ = 1`: `169 ∣ (u − 1)` ⇒ thirteen-drop
  (`thirteen_drop_of_v_three`); `thirteen_drop_numbers`: cofactor
  `339 = 1 + 2·169`, landing `143 = 11 · 13` (start `2711`).

This is the one-sided drift the scan was looking for: not a ranking of
`P(n)`, but a forced drop of surplus `p`-content through the peak,
capped by `v_p(3^v − 1)`.

---

## The `expStep` test

`expStep` on evens is `3x/2`.  It multiplies by `3` and does **not** add
`+1`.

    gcd(n, 3n)    = n          every prime of `n` survives
    gcd(n, 3n+1)  = 1          every prime of `n` dies

So `v_p(3n) = v_p(n)` for `p ≠ 3`, while `v_p(3n+1)` is independent of
`v_p(n)` (and `p ∣ n` with `p > 1` forces `p ∤ 3n+1`).  Measured:
`v_p(3n)` and `v_p(3n+1)` disagree on about one fifth of
`(n, p)` pairs for `p ∈ {5,7,11,13,17,41}`.

The transport theorems use the peak `3^v u − 1`, which is the `+1` of
`3n+1` iterated through an odd run.  A `3n`-without-`+1` map produces
`3^v n` and never relates `u − 1` to a landing.  The device therefore
fails of `expStep` in the sense the brief asked for: it is a theorem
about `3n+1`, not about `3n`.

(`expStep` still agrees with Collatz on odd inputs.  The discrimination
is the even branch, which is where `expStep` omits the `+1`.)

---

## What this is not

* Not a proof that every excursion drops.  Transport is an equality of
  divisibility bits, and the drop is only of *surplus* `p`-content, on
  a thin subset (`u ≡ 1 (mod p^2)`).
* Not a clock on a whole light class.  The leftover `(v, W) = (3, 1)`
  family is `n ≡ 7 (mod 32)`; the 13-flow fires only on the further
  progression `n ≡ 7 (mod 13)`, density `1/13` inside that class.
* Not `v₃(n+1)`.  The 3-adic law of an odd step *raises* `v₃(n+1)` by
  one; here an odd prime `p ≠ 3` dividing `3^v − 1` is read on `u − 1`
  and on `e`, and the bit is copied, not incremented.

Lean: `Collatz/Strategy/DevicePrimeFlow.lean`.
