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

### CEILING — the master bound gains nothing from odd steps (PROVED)

`RunInvariance.bound_invariant_under_run`: for a run of length `A` from `x`,

    3^(A+B) M <= 2^(A+B) (T^A(x)+1)   <->   3^B M <= 2^B (x+1)

The factor `3^A` cancels. So pushing the master bound forward through odd steps
reproduces it exactly, with slack zero. The observed sharpness at `T(m)` and `T^2(m)`
is an identity, not luck. Supporting peak lemma `three_pow_dvd_run_end`:
`2^A | (x+1)` and `3^B | (x+1)` imply `3^(A+B) | (T^A(x)+1)`.
Verified: 0 failures over all odd `x < 400000` (peak lemma) and over 60000 x 400 pairs
(invariance). **All remaining information must come from EVEN steps**, the only place the
3-adic valuation is created rather than transported. Companion: `x+1`, `x+2` never both
divisible by 3, so the first even step after a peak starts from valuation zero.

### CEILING — inverse-tree counting saturates at exponent exactly 1 (Agent C, TESTED + analytic)

Inverse tree of 1: level sizes ratio -> 4/3 (measured to depth 41), residues mod 3
equidistribute to 1/3 each. The counting exponent is
`theta(a) = [H(a) - a ln3] / [ln2 - a ln3]`; numerically `theta_max = 1.000000`, attained
uniquely at `a = 1/2` (identity: numerator = denominator iff `H(a) = ln 2`). `a = 1/2` is
exactly the generic forward profile. **So density-1 is predicted with ZERO slack** — any
loss (path dependence, non-uniform legality factor, second-order terms) lands strictly
below 1. That is why the rigorous record is `N^0.84` and cannot be pushed to `N^1` by
counting. The convergence of the path sum requires the `3^-b` legality factor, which is
equidistribution-mod-3 along backward orbits — itself Collatz-hard.

### CEILING — the master bound captures ~2/3 of NeverDrops and no more (Agent C, TESTED)

Fraction of odd `n` whose excursion is killed by the master bound: 0.39068, 0.39183,
0.39165, 0.39157, 0.39159 for `n < 10^4..5*10^7` — dead constant, no decay. Bucketed by
excursion length over 2*10^8 odd `n`, the kill rate rises then **plateaus at ~0.67** and
does not trend to 1. Reason: only points in `[m, 1.5m)` carry weight 1/3, the next band
1/9, and long excursions sit high up where the test is vacuous; the total is a bounded
constant. **Fatal for cycles**: a cycle is ONE excursion, so there is no independence to
accumulate — 0.67 is all there is.

### REFUTED — the 2-adic "dual" is tautological (Agent C)

`2^t | v => T^(i+t)(m) = v/2^t >= m` looks like a second sieve but is a restatement of
"the orbit does not drop": kill rate 1 on every dropper, zero new leverage. Do not count
it as independent. This also weakens open direction 2 (joint `2^a 3^b` sieve).

### REFUTED — Lyapunov candidate (Agent C)

`S(v) = log_1.5((v+1)/(m+1)) - v3(v+1)` (master-bound slack): equals 0 at every odd-run
peak, invariant under odd runs, drops 1.7095 per even step, jumps back at the next peak.
Not monotone, no well-founded descent.

### NOT STRONGER — Syracuse graph (Agent C)

Syracuse edges are bundles of full-graph edges; the Syracuse tree of 1 and the full tree
have the same node set up to doubling rays. Any counting bound on `|tree ∩ [1,N]|` is
identical; only depth grading changes. Do not spend effort here.

## *** THE DECISIVE OBSTRUCTION (PROVED) — `Mirror` ***

Replace `3n+1` by `3n-1` and the shift `u = x+1` by `u = x-1`. The mirror identity
`2(T(x)-1) = 3(x-1)` holds verbatim, so **every theorem here derived from the shift
identity plus congruences has an exact analogue in the mirror world.**

But the mirror world has nontrivial cycles: `5 -> 7 -> 10 -> 5`. Kernel-checked:
- `Mirror.five_neverDrops`: `5` never drops there, and `5 != 1`;
- `Mirror.five_mod_four`: `4 | (5-1)` -- analogue of `m = 3 mod 4`;
- `Mirror.five_not_two_mod_three`: `3 nmid (5-1)` -- analogue of `m != 2 mod 3`;
- `Mirror.five_master_bound`: the master bound `3^j (m-1) <= 2^j (v-1)` holds at
  EVERY orbit point, for every `j`;
- `Mirror.five_bound_sharp`: with **equality** at `T(m)` and `T^2(m)` -- exactly the
  sharpness `OrbitDescent.windows_sharp` reports for `3n+1`.
- `Mirror.seventeen_cycles`: `17` is an independent second witness (11-cycle).

`Mirror.mirror_model_of_the_profile` packages this as a **model in which every
hypothesis holds and the conclusion fails**.

**CONSEQUENCE: no combination of `OddRuns`, `RunValue`, `BackwardRun`, `ThreeAdic`,
`Descent`, `OrbitDescent` can prove Collatz.** They are blind to the sign of the 1.
This is not about effort; it is a statement about what those hypotheses entail.

**The only non-mirror-invariant asset is the verified range `m >= 307200`** — a
computation about `3n+1` specifically (the mirror least never-dropper is `5`). So any
completion MUST use the verified range *quantitatively*, in the shape
"every never-dropper is `< B`" for explicit `B`. That reshapes the whole programme.

### First result of the required shape (PROVED) — `OneRunCycle`

A cycle of shape "`j` odd steps up, then pure halving down" satisfies exactly
`3^j (m+1) = 2^L m + 2^j`, hence `3^j < 2^L` and — crucially, an **upper** bound on `m` —
`m + 2^j <= 3^j`. With `m >= 307200` this forces `j >= 12`.
Measured (not proved): for `j <= 4000` there is NO integer solution with `m >= 2`, and
`max (3^j-2^j)/(2^L-3^j) = 1243`, a factor 247 below the verified range; the maximum
grows like the continued-fraction denominators of `log2 3`, so `j ~ 10^5` is needed
before it can even reach 307200.

## *** THE PRODUCT INVARIANT (PROVED) — `CycleProduct` — strongest cycle tool ***

Discovered independently by two agents and cross-verified. Let `c` be any floor for the
whole orbit of `x` (`c = 307200` via `VerifiedSharp.ge_verified_sharp`). Then

    (I)   2^k * c^a * T^k(x)  <=  (3c+1)^a * x        a = oddCount x k

One induction: an even step leaves both sides fixed; an odd step multiplies the left by
`c(3v+1)` and the right by `v(3c+1)`, and `c <= v` gives `c(3v+1) <= v(3c+1)`.
**The odd step is charged `(3c+1)/c`, not 3** — that is the whole gain, and it is available
only because `c` is LARGE. Exactly the non-mirror-invariant input `Mirror` demands.

On a cycle `T^L(x) = x` the `x` cancels:

    (II)  2^L * c^a <= (3c+1)^a                       `cycle_product_bound`

Linearising `(u+1)^a * u <= u^a * (u+2a)` at `u = 3c` (`pow_succ_le`):

    (III) 3c * 2^L <= 3^a * (3c + 2a)                 `cycle_min_bound`

### Verification before formalizing
- invariant (I): 119,940 exact instances along real orbits, 0 failures
- linearisation: 0 failures wherever `2a <= u`
- trivial cycle `1 -> 2 -> 1`: satisfies (II) and (III) with EQUALITY, so the bound
  correctly declines to exclude it
- `3n-1` world: the inequality reverses and the bound goes vacuous, exactly as `Mirror`
  predicts for any conclusion that is not mirror-invariant
- Agent D reached the same bound by a different route (product of the `a` odd-step
  equations, `2^L prod n_t = prod (3n_t+1)`), and its sharpness checks agree

### What it gives
`(L, a)` is impossible iff `3^a (3c+2a) < 3c 2^L`. With `c = 307200`:
**first non-excluded pair is `(L, a) = (1539, 971)`** — independently reproduced by me and
by two agents. Previous repo best was `L >= 27`; this is the same verified range used
better, by a factor of 57. Of `a <= 3000` only seven values survive at all:
`a in {971, 1636, 1942, 2301, 2607, 2913, 2966}`.

Kernel-checked: `excludedLength_of_lt` proves **every cycle length below 520** is excluded
(4 chunked `decide`s, ~26s). The reduction `no_cycle_of_excludedLength` is PROVED. The
sweep stops at 520 for BUILD COST only -- the mathematical frontier is 1539, confirmed by
exact integer computation. A sweep to 1560 was attempted and **correctly failed to compile**
(1539 is not excluded), which is exactly the check working: the false range was caught by
the kernel, not by me.

### Square-root payoff law (TESTED)
`max_{L<=X} B(L) ~ 0.38 X^2`, so excluded cycle length grows like `sqrt(verified range)`:

| verified range | cycle lengths excluded |
|---|---|
| 102400 | L <= 484 |
| **307200 (have)** | **L <= 1538** |
| 768000 | L <= 2592 |
| 6662000 | L <= 9970 |

Doubling 307200 -> 614400 buys LITERALLY NOTHING (`B(1539) = 661176 > 614400`); the
staircase is lumpy and 768000 is the next threshold that pays.

## DIVERGENCE IS PROVABLY IMMUNE (Agent E, PROVED sketch)

For every `k`, the truncated hypothesis "never drops for `k` steps" is satisfied by
arbitrarily large `x`: take `x = -1 mod 2^(k+1)`, then `OddRuns.oddRun_iff` gives a run of
length `k+1` and `RunValue.oddRun_value` gives `T^j(x)+1 = (3/2)^j (x+1) > x+1`.
**So no theorem of the form "never-dropper implies m < B" can be proved from any finite
truncation of the never-dropping hypothesis.** The cycle hypothesis is a CLOSED finite
condition (`T^L(m) = m` forces the integer gap `2^L - 3^a >= 1`); divergence has no finite
closure. Any divergence bound needs a genuinely infinitary input, or an a priori bound on
the orbit maximum — which by pigeonhole converts divergence into the cycle case.

Also TESTED: over 994,216 excursion steps from odd starts < 400000, `2^k > 3^(a_k)` while
still above the start occurred **0 times**, so invariant (I) extracts nothing in the
divergent case. Confirmed by (I) itself: the available gap is `O(3^a a/m)`, exactly the
size the right-hand side already permits. Self-consistent, extracts nothing.

## *** WHAT THE MIRROR WORLD ACTUALLY IS — the sharpest framing (PROVED) ***

The mirror map is **the genuine `3n+1` map on the NEGATIVE integers**, read through `n -> -n`:
`T(-n) = -(mirrorStep n)`. Verified over all `n < 20000`, zero exceptions.
Its cycles are exactly the three classical negative cycles of `3n+1`:
`5 -> 7 -> 10` is `-5 -> -7 -> -10`; the 11-step 17-cycle is `-17 -> -25 -> -37 -> ...`;
the fixed point `1` is `-1`.

So the obstruction is NOT about `3n+1` vs `3n-1`. It is:

> Every theorem here derived from the shift identity + congruences is a theorem about
> `3n+1` **over Z**, and `3n+1` over Z HAS nontrivial cycles. Those tools do not see the sign.

**The answer to "what property of 3n+1 must an argument use?" is POSITIVITY.**
A proof must break the `n <-> -n` symmetry of the algebra. What breaks it:
- the verified range (`m >= 307200`);
- `CycleProduct`'s floor `c` — a large POSITIVE lower bound has no negative analogue.
What does not: congruences, the shift identity, valuations, the master bound.

The duality is exact at the defining identity: `OddRuns` rests on `2(T(x)+1) = 3(x+1)`;
the mirror rests on `2(mirrorStep(x)-1) = 3(x-1)` (`Mirror.two_mul_pred_mirrorStep`, PROVED).
Every downstream congruence theorem transfers along it — which is why all of them hold for 5.

## PRODUCT INVARIANT REACHES DIVERGENCE (PROVED) — `neverDrops_product_bound`

The product invariant needs no cycle. For ANY never-dropper, the floor `c = m` is legitimate
and `T^k(m) >= m` cancels the `m`:

    2^k * m^a <= (3m+1)^a      for every k,  a = oddCount m k

This is the **first product-invariant consequence that constrains a divergent orbit**.
Against the classical `2^k < 2*3^a` it trades a fixed additive loss (`-0.631`) for a
multiplicative one (`~1/(3m)`), so for `m >= 307200` it is STRICTLY STRONGER for every
window shorter than about `10^6` steps, and weaker beyond. Both hold, so take the max.
Honest assessment: a real sharpening, not a qualitative change — the asymptotic density
requirement is still `a/k >~ log2/log3`, which is the known wall.

## *** THE WINDOW BOUND — heaviness for ALL windows (PROVED) — the bridge ***

`AffineBoundSharp.two_pow_lt_of_no_drop` gave `2^k < 2*3^a` only for windows with
`2^k <= m`, i.e. `k <~ log2 m` -- about **18 steps** for a counterexample. The product
invariant removes that restriction almost entirely, with NO cycle hypothesis:

    neverDrops_window_bound:   3m * 2^k <= 3^a * (3m + 2a)      for every k
    neverDrops_heavy_window:   2^k <= 2 * 3^a                   whenever 2a <= 3m
    light_window_forces_large_oddCount:  2*3^a <= 2^k  =>  3m <= 2a

For `m >= 307200` this forces the orbit to stay heavy on **every window until the
odd-step count reaches 460800**, i.e. roughly **730000 steps** -- against 18 before.
This is a statement about DIVERGENT orbits as much as cyclic ones, and it is the first
such statement in the project.

Verification before formalizing: the implication `2^k m^a <= (3m+1)^a  =>
3m 2^k <= 3^a(3m+2a)` checked on 1,058,099 exact cases, 0 failures.

### POSITIVITY AUDIT (mandatory table)

| Result | Mirror survives? | Positivity used? | Useful? |
|---|---|---|---|
| shift identity `2(T(x)+1)=3(x+1)` | YES (mirror: `2(T(x)-1)=3(x-1)`) | no | NO |
| congruence / residue lemmas | YES | no | NO |
| valuation lemmas (`OddRuns`, `ThreeAdic`) | YES | no | NO |
| master bound (`BackwardRun`) | YES (holds for 5 with equality) | no | NO |
| verified range `m >= 307200` | NO (mirror least is 5) | YES | YES |
| `CycleProduct` floor `c` | NO (inequality reverses) | YES | YES |
| `neverDrops_product_bound` | NO | YES | YES |
| **window bound / heavy window** | **NO** | **YES** | **YES** |

**Positivity injection point, exactly one line:** the odd-step comparison
`c(3v+1) <= v(3c+1)`, which is `c <= v` multiplied through by positive quantities.
Over Z the ordering reverses, so the mirror analogue of the invariant is
`2^k c^a T^k(x) >= (3c-1)^a x` -- a LOWER bound, which yields nothing.

**Methodological caution (learned the hard way):** evaluating the `3n+1`-form inequality
on mirror data is NOT the right mirror test. It can hold there by accident -- it does for
`m=5`, whose cycle is heavy (`a/k = 2/3 > log2/log3`). The correct test is whether the
mirror *derivation* produces a useful bound. Test the derivation, not the formula.

## *** NEVER-DROPPING ARITHMETISED (PROVED) — `AffineExact` ***

The additive correction is now computed outright, not merely bounded. Writing `C j x`:

    odd step:   C -> 3C + 2^j          even step:  C unchanged
    2^j * T^j(x) = 3^(oddCount x j) * x + affineC j x        (affine_exact)

Verified on 120,000 exact instances before formalizing. So the ENTIRE additive content
of the `+1` in `3n+1` is one accumulator fed only by odd steps.

**`neverDrops_iff_affine`: m never drops  <->  for all j,
`2^j * m <= 3^(oddCount m j) * m + affineC j m`.**
The dynamical hypothesis is GONE; only `2^j`, `3^a` and one explicit integer remain.
This is the cleanest available statement of the problem.

`three_pow_le_affineC`: `3^a <= affineC j x + 2^a` (minimum attained by taking all odd
steps first). Plus `oddCount_le_self`.

### HONEST NEGATIVE: the sandwich carries no information

`neverDrops_iff_affine` is a LOWER bound on C; `CycleProduct.neverDrops_product_bound` is
an UPPER bound on the same C. Together:

    (2^j - 3^a) m  <=  C  <=  m ((3+1/m)^a - 3^a)

The two are compatible **precisely when** `2^j <= (3+1/m)^a` -- which is the product bound
restated. So the "two inequalities on the same intermediate quantity" idea is exhausted
here. Recorded so it is not re-attempted.

### CORRECTION: `a = 3m/2` is an artifact, there is no second regime

The threshold comes from `pow_succ_le`, which needs `2a <= 3m`. The underlying bound
`2^k m^a <= (3m+1)^a` has **no side condition** and stays active well past it -- checked
at `m = 101`, where at `a = 152 > 3m/2 = 151.5` it still forces `a/k >= 0.6307`.
Simplified forms like `2^k <= 2*3^a` introduce thresholds of their own (`a <~ 2.08m`), but
the threshold belongs to the simplification, not the mathematics. **No two-regime
architecture is needed.**

### Where the real wall is

`neverDrops_product_bound` forces `a/k >= theta_m` with `theta_m = ln2/ln(3+1/m)`, and
`theta_m < log2/log3` for every finite `m`, approaching it from BELOW as `m -> inf`.
So the product bound does NOT force super-critical density -- it forces slightly
sub-critical density. The gap between `theta_m` and `log2/log3` is exactly the room a
divergent orbit needs, and it is `O(1/m)`. Closing divergence needs a bound with
`rho < log2/log3` strictly, which this family provably cannot supply.

## *** THE POSITIONAL FORMULA — the +1 retains ORDERING (PROVED) ***

Unrolling `C -> 3C + 2^j` (odd) / `C -> C` (even) gives the exact positional formula

    affineC j x = SUM_{i=1..a} 3^(a-i) * 2^(p_i)      p_1 < ... < p_a = odd-step positions

Verified on 64,000 exact instances. **So the accumulator retains the ORDERING of the odd
steps, not merely their count** -- exactly the information the product invariant discards.

Extremes over arrangements (both PROVED):
- minimum, all odd steps FIRST:  `3^a <= affineC + 2^a`      (`three_pow_le_affineC`)
- maximum, all odd steps LAST:   `affineC + 2^j <= 2^(j-a) * 3^a`  (`affineC_le`)

### THE WINDOW CONDITION (PROVED) — one inequality subsuming several theorems

Feeding the positional upper bound into `neverDrops_iff_affine`:

**`neverDrops_window_condition`: for a never-dropper, EVERY window satisfies
`2^j (m+1) <= 3^a (m + 2^(j-a))`.**

Verified: 57,613 checks on no-drop prefixes, 0 failures. What it forces:

| a | t=j-a | forces | rediscovers |
|---|---|---|---|
| 0 | >=1 | impossible | first step is odd (`oddCount_pos_of_neverDrops`) |
| 1 | 1 | m <= 2 | `m = 3 mod 4` |
| 2 | 2 | m <= 2 | `RunDescent.not_two_halvings` |
| 3 | 2 | m <= 15 | NEW |
| 3 | 3 | m <= 4 | NEW |
| 4 | 3 | m <= 11 | NEW |
| 4 | 4 | m <= 5 | NEW |

One inequality unifying several independently-proved theorems plus an infinite new family.
Cycle-free: applies to ANY never-dropper, so it constrains divergence.

### Honest limitation

The condition bites hardest when the even-count `t` is small: for `2^t << m` it reads
`2^j <~ 3^a` (supercritical density), but once `2^t >> m` the right side is dominated by
`3^a 2^t` and it degenerates to `2^a <= 3^a`, which is trivial. So it is strong only on
windows with `t <~ log2 m` (about 18 even steps for a counterexample). Extending its reach
past that is the live question.

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

1. ~~Push the master bound forward~~ CLOSED by `RunInvariance.bound_invariant_under_run`.
   The single live question: along a maximal halving run from a peak `P` with
   `P+1 = 3^(A+B) w`, the descent points are `P_t = P/2^t` and the bound at `P_t` reads
   `2^j (P + 2^t) >= 2^t 3^j (m+1)` with `j = v3(P + 2^t)`. **Is `v3(3^(A+B) w - 1 + 2^t)`
   controllable in `t`?** This is the only step in an excursion not already implied by the
   bound at the peak. If a lower bound on `max_t v3(P + 2^t)` can be forced from
   `2^A || (m+1)` on the same `w`, that is a genuine new obstruction; if not, the descent
   phase is provably free and the master-bound programme is closed at 0.67.
2. Joint mod-`2^a·3^b` sieve — is any joint survivor set empty?
3. `≡1 mod 3`: explain the surviving fraction; does it → 0?
4. A potential/Lyapunov function on `u = x+1` using both valuations.
