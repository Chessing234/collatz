# Collatz research frontier

Persistent checkpoint. Update at every synthesis round. Status codes:
**PROVED** = Lean kernel-checked. **TESTED** = finite computation only, never a proof.
**CONJ** = conjectural. **REFUTED** = killed, with counterexample. **CLOSED** = provably
unreachable by the stated method.

## The reduction (PROVED)

`NeverDrops x := ∀ j, x ≤ T^j(x)` where `T(n) = n/2` (even), `(3n+1)/2` (odd).

**Collatz ⟺ 1 is the only number that never drops.** (`NeverDrops.collatz_iff_neverDrops`)
Needed the bridge `accReachesOne_of_orbit` (standard reachability ⇒ accelerated).

## The two mirror theorems (PROVED) — the core of the whole development

In the shifted coordinate `u = x + 1`:
- an **odd step** multiplies `u` by `3/2`;
- a **backward odd step** `p(v) = (2v−1)/3` multiplies `u` by `2/3`.

| | forward | backward |
|---|---|---|
| run of length `j` available iff | `2^j ∣ (x+1)` | `3^j ∣ (v+1)` |
| exact identity | `2^j (T^j x + 1) = 3^j (x+1)` | `3^j (p^j v + 1) = 2^j (v+1)` |
| rationed by | `2^j ≤ x+1` | (see master bound) |

`OddRuns.oddRun_iff`, `RunValue.oddRun_value`, `BackwardRun.exists_backChain`.
Each direction is governed by the valuation of `u` at the *opposite* prime.

## Least never-dropper `m` — the profile (PROVED)

- `m ≥ 307200` (verified range, 300 blocks of the mod-1024 sieve)
- `m` odd, `m ≡ 3 (mod 4)`, `m mod 16 ∈ {7,11,15}`
- `m ≢ 2 (mod 3)`, `m ≢ 4 (mod 9)`, so `m ≡ 3 or 7 (mod 12)`
- heavy at every scale; `2^(v+W) ≤ 3^v` and `W < v` on the first excursion
- `T(m) = (3m+1)/2`, `T²(m) = (9m+5)/4` exactly

## MASTER BOUND (PROVED) — strongest single statement

`BackwardRun.orbit_backward_bound`: for every orbit point `v = T^i(m)` and every `j`,

    3^j ∣ (v+1)  ⟹  3^j (m+1) ≤ 2^j (v+1)      i.e.  v+1 ≥ (3/2)^j (m+1)

Contrapositive (`no_low_backward_run`): **no orbit point below `(3/2)^j (m+1)` is
`−1 mod 3^j`.** Subsumes the whole ad-hoc descent ladder (`j=1,i=0` gives `m ≢ 2 mod 3`).
Sharp: bounds attained exactly at `T(m)`, `T²(m)`.

## Exact 3-adic step laws (PROVED) — `ThreeAdic`

- **odd step:** `x` odd ⟹ `3^k ∣ (x+1) ↔ 3^(k+1) ∣ (T x + 1)`. The 3-adic valuation of
  `u` rises by *exactly one*. (`three_pow_odd_step_iff`)
- **even step:** `x` even ⟹ `3 ∣ (T x + 1) ↔ x ≡ 1 (mod 3)`. (`three_dvd_even_step_iff`)
- **REFUTED**: the guess that `v3(u)` just counts the current odd run. Even steps *inject*
  3-divisibility — 32% of even steps do, measured over all orbits from odd starts < 20000.
  This is why the master bound is not vacuous: the even steps are where it has content.

### New forbidden window (PROVED)

`ThreeAdic.even_orbit_one_mod_three_ge`: **every even orbit point `x ≡ 1 (mod 3)` of the
least never-dropper satisfies `x ≥ 3m + 1`.** Width-`2m` forbidden region in a class the
earlier results said nothing about. Now BOTH non-zero classes mod 3 are constrained:

| class | lower bound on orbit points |
|---|---|
| `v ≡ 2 (mod 3)` | `v ≥ (3m+1)/2` — sharp, attained at `T(m)` |
| `v` even, `≡ 1 (mod 3)` | `v ≥ 3m + 1` |
| `v ≡ 0 (mod 3)` | no constraint (and backward descent CLOSED there) |

Early orbit points sit exactly on the boundaries: `T(m)+1 = 3(m+1)/2` and
`T^2(m)+1 = 9(m+1)/4`, so `j = 1, 2` hold with equality. No contradiction yet — the
constraints are all *lower* bounds, and a divergent orbit has no upper bound to clash with.

### Composition: the low window is one residue class (PROVED)

`odd_orbit_not_three_dvd` (general, needs no never-dropping hypothesis): **for odd `x`,
no `T^k(x)` with `k >= 1` is divisible by 3** -- else `x = 2^k * T^k(x)` is even.
Verified: 0 violations over 150000 odd starts; for *even* starts it happens ~1/3 of the
time, so the statement is specific to odd starts and not vacuous.

Composing it with the two windows:
- no orbit point below `(3m+1)/2` is `= 2 mod 3`;
- no even orbit point below `3m+1` is `= 1 mod 3`;
- so an even point in `[m,(3m+1)/2)` would be `= 0 mod 3` -- impossible past time 0.

**`no_even_orbit_below`: the orbit of the least never-dropper has NO even value below
`(3m+1)/2`.** Sharpened (`orbit_one_mod_six_below`): every orbit value there, past time
zero, is **exactly `1 mod 6`**. An entire parity class removed from an interval of width
`m/2` -- neither window does that alone.

Consistency check: `m = 7 mod 12` when `3` does not divide `m`, and `7 = 1 mod 6`.

### 3-adic cap on bounded orbits (PROVED)

`three_pow_le_of_bounded`: orbit bounded by `B` implies `3^j | (T^i(m)+1)` forces
`3^j (m+1) <= 2^j (B+1)`. The mirror of `RunBounds.oddRun_le_cycleMax`, which caps the
2-adic valuation by `2^j <= B+1`. `both_caps` states them together.
**Divergent orbits escape both caps** -- precisely why the divergence half is harder.

## Obstructions (PROVED / CLOSED)

1. **CLOSED — mod-3 descent.** `3 ∣ v` ⟹ `v` has exactly one preimage, `2v`
   (`ThreeObstruction.pred_unique_of_three_dvd`). Backward tree of a multiple of 3 is a
   single doubling chain, so backward descent can *never* reach `3 ∣ m`, at any word
   length, any modulus. Matches computation: all `3^(K−1)` such classes survive at every `3^K`.
   BUT: excluded for cycles (`neverDrops_cycle_not_three_dvd`).
2. **CLOSED — cycle summation.** Multiplying excursion identities round a cycle telescopes
   to `2^L > 3^a`, so the local bound `2^(v+W) ≤ 3^v` provably fails somewhere; no
   summation argument of that shape exists (`Frontier.targetC_no_summation`).
3. **REFUTED — single-excursion criterion.** `102411` has no contracting first excursion
   (`Frontier.targetD_hypothesis_false`). One excursion never suffices.
4. **CLOSED — sieve density.** Survivor counts 3,8,19,64,226,734,2114,7495,27328 at levels
   4..20: density falls but **count rises**. Survivors form a coherent tower = the 2-adic
   integer `−1` (`SieveDensity.coherent_tower`).
5. **CEILING — density rate.** Rate `p/q` needs `3^p < 2^q`; capped by `log2/log3`.
   Best `41/65`; decay ceiling `0.96863^k`; `17/27` already within 0.1% of it.

## Surviving case space

- `m ≡ 2 (mod 3)`: **closed** (descent).
- `m ≡ 0 (mod 3)`: backward descent **provably cannot** reach it; closed only for cycles.
- `m ≡ 1 (mod 3)`: partially closed. Survivor fraction of `≡1 mod 3` classes at `3^k`:
  0.6296 (81), 0.6296 (243), 0.6214 (729), 0.6104 (2187). Slowly decreasing — TESTED only.
- Cycle half reduces to bounding `|2^L − 3^a|` below: linear forms in logarithms (Baker).
  Not elementary; outside Lean-core reach.

## Highest-value open directions

1. Push the master bound: for which `i` is `v3(T^i(m)+1)` large? Combine with forward
   structure to force a contradiction.
2. Joint mod-`2^a·3^b` sieve — is any joint survivor set empty?
3. `≡1 mod 3`: explain the surviving fraction; does it → 0?
4. A potential/Lyapunov function on `u = x+1` using both valuations.
