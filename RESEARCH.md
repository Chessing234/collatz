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

## *** COMPRESSION RESULT: the arrangement architecture IS the sieve ***

The proposed "Realizable-Arrangement Theory" (characterise which odd/even words a genuine
orbit can produce, hope the extremal ones are unrealizable) collapses. Three measurements:

1. **Every parity word of length `j` is realized by EXACTLY ONE residue mod `2^j`** — a
   bijection, verified for `j <= 12`, 0 failures. So NO arrangement is arithmetically
   unrealizable. The premise of the architecture is false.

2. **`(oddCount x j, affineC j x)` depend ONLY on `x mod 2^j`** — 40,950 checks, 0 failures.
   So the whole affine data of a window is a function of the residue.

3. **The never-drop-compatible words are EXACTLY the sieve survivors.** Enumerating all
   `2^j` words and filtering by the prefix conditions at `m = 307200` gives counts

       j  = 1  2  3  4  5  6  7   8   9  10  11  12  13  14
       ok = 1  1  2  3  4  8 13  19  38  64 128 226 367 734

   Compare the independently measured mod-`2^k` sieve survivor counts at
   `k = 4,6,8,10,12,14`: **3, 8, 19, 64, 226, 734** — an exact match.

**Conclusion (mathematical compression).** "Which arrangements are realizable by a
never-dropper" is not a new question; it is the mod-`2^k` drop sieve, already mapped:
density falls, count RISES, survivors form a coherent tower converging to the 2-adic
integer `-1`, and it provably never clears. Attacking arrangements is attacking the sieve.

4. **The worst-case bound cannot be improved this way.** `maxC(never-drop compatible) =
   maxC(all words)` at every level tested, ratio exactly 1.0000. The C-maximising word is
   itself never-drop compatible, so replacing the combinatorial extremum by the
   "realizable" extremum gains **nothing**.

### FAILED APPROACHES DATABASE (do not re-attempt)

| approach | why it fails | evidence |
|---|---|---|
| realizable-arrangement theory | all words realizable (bijection with residues) | j <= 12, 0 failures |
| improve `affineC_le` via realizability | extremal word is compatible | ratio 1.0000, j <= 14 |
| the C-sandwich | compatibility condition IS the product bound | algebraic identity |
| two-regime split at `a = 3m/2` | threshold is a linearisation artifact | m=101, a=152 still active |
| floor-comparison family for divergence | `theta_m < log2/log3` always | asymptotic |
| `alpha log u + beta v2 + gamma v3` Lyapunov | 4 explicit witness families | PROVED |
| inverse-tree counting | exponent saturates at exactly 1, zero slack | analytic + measured |
| master bound forward-pushing | invariant under odd runs | PROVED |

## *** THE SIZE INTERACTION, EXACTLY (PROVED) — and a correction to my own report ***

Never-drop is `(2^j - 3^a) m <= affineC j m`; the positional bound gives
`affineC j m <= 2^t 3^a` with `t = j - a`. So the growth ratio `rho = 2^j/3^a` obeys

    rho - 1  <=  2^t / m           <-- THIS QUOTIENT IS THE ENTIRE SIZE INTERACTION

At `m = 307200`: the quotient is `1.0e-4` at `t=5`, `0.0033` at `t=10`, `0.85` at `t=18`,
`109` at `t=25`, `3.6e6` at `t=40`. It is harmless while `2^t <= m` and explodes after.

PROVED: `heavy_while_few_even` -- if `2^(j-a) <= m` then `2^j <= 2*3^a`.
Verified on 86,515 no-drop-prefix checks, 0 failures. Also `affine_slack_bound`.

### CORRECTION to the previous frontier report

I previously wrote that the window machinery is "strong only for `t <~ log2 m`, about 18
even steps". **That understated the reach by about four orders of magnitude.** It is true
of `neverDrops_window_condition` specifically, but `CycleProduct.neverDrops_heavy_window`
reaches far further by a DIFFERENT mechanism: it requires only `2a <= 3m`, i.e.
`a <= 460800`, which at the critical density is `j ~ 730000` steps and
**`t ~ 269000` even steps**. The two routes are complementary; the product route dominates.

So the current best heaviness statement for a never-dropper with `m >= 307200` is:
`2^j <= 2*3^a` for every window with either `2^(j-a) <= m` (t <= 18) OR `2a <= 3m`
(t <~ 269000). The second subsumes the first in practice.

### THE STRUCTURAL WALL, stated precisely

All routes converge on the same limit, and there is a reason. `never-drops` is EXACTLY
`for all j, (2^j - 3^a) m <= C_j` (`neverDrops_iff_affine`, an iff). Since `C_j >= 0` and
`C_j <= 2^t 3^a`, this pins `rho = 2^j/3^a` into `[?, 1 + 2^t/m]`. Asymptotically that is
`density >= log2/log3`, approached FROM BELOW by every bound in the project:

| route | density lower bound | approaches log2/log3 from |
|---|---|---|
| classical `2^k < 2*3^a` | `(k-1)/log2(3) / k` | below (additive loss) |
| product invariant | `ln2/ln(3+1/m)` | below (multiplicative loss) |
| window condition | `log2/log3 - log(1+2^t/m)/(j ln3)` | below |
| heavy_while_few_even | same, with `2^t <= m` | below |

**Never-dropping IS the density condition `3^a >~ 2^j`.** Any elementary bound recovers it
and nothing more, because it is not an approximation of the hypothesis -- it is the
hypothesis. To beat it one needs a reason an ACTUAL orbit cannot sustain
`density >= log2/log3`, and that is not implied by any local structure, since every
parity word is realized by a residue class (see the compression result above).

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


---

# Cycle: ten-field branch (2026-08-20)

The size/density route bottoms out at `log 2 / log 3`.  Ten fields were run
independently against that wall.  Results, most decisive first.

## Kernel-checked this cycle (count 1248 -> 1263)

| theorem | file | content |
|---|---|---|
| `length_ge_520` | `CycleLength520` | **every nontrivial cycle has L >= 520** (was 27) |
| `no_class_ranking` | `NoFiniteRanking` | no rank constant on classes mod `2^k`,`3^l` can decrease |
| `heavy_return_value/_congr/_grows` | `NoFiniteRanking` | the returning family `n+1 = 2^(k+L) 3^l s` |
| `affineC_not_three_dvd` | `AccumulatorArith` | **v3(C) = 0** permanently, once one odd step has occurred |
| `three_not_dvd_orbit_of_odd_step` | `AccumulatorArith` | sharp form of `odd_orbit_not_three_dvd` |
| `affineC_odd_of_odd` | `AccumulatorArith` | v2(C) is a timestamp, not a size |
| `affineC_add`, `oddCount_add` | `AccumulatorArith` | **the accumulator is a cocycle** |
| `full_density_iff_dvd`, `full_density_size` | `HeavyState` | full density = the single class `-1 mod 2^k`, costing `2^k <= x+1` |

## The unifying discovery: every field hit the same object, `-1`

Independent fields converged on one obstruction, the 2-adic fixed point `-1`:

* **graph/automata** — max mean cycle of the mod-`2^k` quotient is `log(3/2)` at
  every `k = 4..14`, pinned by the self-loop at `-1`.  Adding a 3-adic
  coordinate (all `k<=10`, `l<=3`) leaves it unchanged; `-1` is fixed there too.
  Second-worst cycle is `log(3/2) - (log 3)/k`: **more resolution is monotonically
  less useful**.
* **Lyapunov search** — LP over `log x`, `v2(x)`, `v2(x+1)`, `v2(3x+1)`, classes
  mod `2^8` and `3^3`: optimal margin **exactly 0** at every window `L = 1..8`
  and every modulus to `2^14 3^4`.  Certificate is the family above.
* **2-adic** — integrality is not 2-adically visible; every class mod `2^j`
  contains integers, odd-denominator rationals and irrational 2-adics alike.
* **ergodic** — the only integers on infinite no-drop branches, over all periods
  `L <= 20`, are `-1, -5, -17`: exactly the three known negative cycles.

This is `Mirror` in four new languages.  `full_density_size` is the only thing
in the development that separates `2^k - 1` from `-1`, and it does so by size.

## Killed, with reasons

| approach | verdict |
|---|---|
| v3(C) sparsity | **v3(C) = 0 always** — no 3-adic slack exists to exploit |
| Lyapunov on finite quotient | impossible in principle (proved, `no_class_ranking`) |
| graph SCC / ranking | quotient is a single SCC at every `k`; MMC pinned at `log(3/2)` |
| Sturmian/balanced extremal words | **corrected**: the earlier table 2,4,8,16,31,55,87,118 was measured at one fixed word length, not in the limit. The admissible language's factor set is *all* of `{0,1}^*` (`1^N u` is heavy for every `u`), so `p(k) = 2^k` and its shift closure is the full shift. Pseudorandom was an understatement |
| smallness of admissible words | `N(j) ~ 2^(0.95 j)`, entropy `H(theta) = 0.94996` — exponentially many |
| descent by class-minimisation mod `2^L` | rigid: for a never-dropper `2^L > m` always, so the map is the identity |
| phantom-cycle filtering | there are none: integrality + positivity **imply** self-consistency |
| counting/divisibility heuristic for cycles | predicts `~J/2` cycles to length `J` — does not give finiteness |

## Computational, not proved

* `k <= 5` cycles excluded for all `j <= 50`; `(j,a) = (46,29)` checked
  exhaustively over 39,144,869 shapes, 0 hits.
* No nontrivial cycle with `j <= 24` (exhaustive over all position sets).
* Survivor counts `S_k ~ C * lambda^k * k^(-3/2)`, `lambda = 2^H(theta) = 1.9318131`.
* The `S_{k+1} = 2 S_k - N_k` recursion has its doubling levels on the
  **Sturmian word of slope theta** — S-adic, not a finite substitution.
* Semigroup `<A,B>` is free (all `2^j` words, `j <= 22`, zero collisions).

## What remains

The obstruction is now two-sided and named.  Local/congruence information cannot
work: every finite quotient retains `-1`.  Global inequalities cannot work:
never-dropping *is* the density condition.  The only quantity separating the two
worlds is archimedean — `3^a (x+1) > 2^j`, i.e. `full_density_size` and its
relatives.  A proof must be built on that, and no field surveyed supplies a
second independent constraint to combine with it.


# Round 2 — the thirteen-field branch program

Thirteen fields were run independently against the obstruction, then chained.
What follows is the ledger: what became a theorem, what became a bridge, and
what is now closed by proof rather than by discouragement.

## The reframing that organised everything

The gap `d = 2^L − 3^a` of a hypothetical cycle is **odd**.  So `C/d` is always a
2-adic integer: **ℤ₂ places no condition whatsoever on cycle integrality.**  With
`v₃(C) = 0` already known, the entire cycle obstruction is localised away from
both 2 and 3, onto the odd primes dividing `d`.  Three fields reached this
independently (2-adic, accumulator, semigroup), and it is what makes the order
mechanism below the only live arithmetic channel.

Beside it sits the sharpened criterion: a cycle is *exactly* a word whose gap
divides its accumulator (`CycleCriterion.cycle_of_gap_dvd`, both directions).
There is no residual dynamical side condition, and no positivity content either
— every word with `2^L > 3^a` already has a positive rational fixed point.  The
cycle problem is 100% the divisibility.

## New theorems (PROVED this round)

| statement | file | note |
|---|---|---|
| no nontrivial cycle shorter than **1539** | `CycleLength1539` | was 520; the scan over odd-step counts was replaced by two self-certifying comparisons at the top exponent |
| cycles ⟺ words whose gap divides their accumulator | `CycleCriterion` | converse included; the orbit is eliminated entirely |
| `C` and `3^a` are class functions mod `2^j` | `AccumulatorClass` | the bridge from Terras' word↔class dictionary to the arithmetic of `C` |
| `v₂(C)` = time of the first odd step, exactly | `AccumulatorValuation` | divisibility and sharpness both proved |
| orbit residue mod 3 = clock on the current halving run | `ThreeResidue` | the non-divisibility statement was one third of this |
| a class caps its own never-droppers | `ClassCap` | one accumulator kills a whole progression |
| `2^j = 3^a+1` only at `(1,0),(2,1)`; `3^a = 2^j+1` only at `(1,1),(3,2)` | `GapOne` | gap 1 ⟹ trivial cycle; gaps 2, 3 impossible; nontrivial gap ≥ 5 |
| sharp accumulator bound `2^a(C + 2^j) ≤ 3^a 2^j`, attained | `AccumulatorSharp` | dominates the two bounds the development was storing |
| heavy-density exponent **0.95096** | `DensitySharper` | tilt matched to the rate; floor is 0.94996 |
| **no modulus at all** admits a decreasing rank | `AnyModulusRanking` | any `m`, any codomain with an irreflexive relation |
| no congruence-definable transition invariant | `TransitionInvariant` | kills SCT, lexicographic and multiphase certificates too |
| `3x+5` has cycles, and the run identity is uniform in `d` | `Denominator` | any `d`-uniform argument is unsound |

## The one new mechanism: order, not size

For a **one-run** cycle, `2^L ≡ 3^a (mod d)` collapses the cycle equation to

    d | 2^(L−a) − 1,   hence   d ≤ 2^(L−a) − 1.

This is a *multiplicative order* obstruction — the first constraint found that is
neither a magnitude estimate nor a congruence class.  It uses **no verified
range** and is Baker-free.  *Corrected:* the Lean theorem
`OneRunOrder.no_one_run_of_run_lt` excludes every one-run cycle with **`a <
2048`** — that is the kernel budget of `gapOK_sweep`.  The figures 20 000 and
200 000 were checked *outside* the kernel; the file's own docstring says so, and
this ledger previously dropped the qualifier and quoted the outside number as
the theorem's scope.  Its
weakness is its hypothesis: for `k ≥ 2` runs the accumulator mixes independent
`(tᵢ, Bᵢ)` pairs and the collapse fails.  That is the single highest-value open
problem the round produced.

## CLOSED by proof this round (do not reopen)

* **Scale-increasing / adaptive ranking functions.** The returning witness
  `2^L·m − 1` exists at *every* modulus and forces an equality of ranks, so
  growing precision, orbit-dependent moduli and ordinal-valued ranks all die at
  once.  The escape from the finite-quotient obstruction is precision, and full
  precision *is* the conjecture.
* **Transition invariants / Ramsey certificates / SCT / lexicographic ranks**,
  whenever the components are congruence-definable.
* **Any argument uniform in the constant `d`** of `3x+d`, or blind to the sign of
  `2^L − 3^a`: `3x+5` has cycles (smallest `5 → 10 → 5`), `3x−1` has three, and
  the entire run-identity/congruence/density/parity theory is uniform in `d`.
  Every surviving proof must use the verified initial segment or something else
  specific to `d = 1`.
* **Sparsity of `C`.** `C mod p` equidistributes for every `p ∤ 6` once `a ≥ 9`.
  Prime exclusions do bite, but structurally only up to `a ≈ 8`.
* **Fourier / discrepancy on ℤ/2^k.** The joint law of `(x mod 2^k, T^j x mod 2^k)`
  is *exactly* uniform for `j ≥ k` — every nontrivial coefficient vanishes.  There
  is no discrepancy to bound.
* **Exceptional-set improvement.** The count of `n < N` failing to descend in `k`
  steps is a ballot-path count `≈ N^0.9500`; at the verified `2^68` that is a
  *floor* of `3.6 × 10^17`, missing by 17.6 orders of magnitude, and the method
  saturates exactly at `k = log₂ N`.
* **Lattice / geometry-of-numbers framing.** `t ↦ 2^t` is not linear and the
  coefficient `3^(a−i)` depends on the rank of `t` in the set, so no lattice
  exists to run CVP or LLL against.  Measured: 23.4% of `(j,a)` pairs come within
  2 of a multiple of `d` — the misses are as near as arithmetic allows.
* **Descent by cycle surgery.** Over all `2^22` words there are exactly four
  primitive integral cycle words (`1`, `−1`, `−5`, `−17`); every deletion,
  insertion, merge, split, swap and reversal breaks integrality, and only rotation
  survives — and rotation is already a cycle symmetry, not a descent.
* **Idempotents / Büchi-Ramsey factorisation.** A cycle word's image in any
  finite quotient has an idempotent power automatically, so the argument carries
  zero arithmetic content.
* **Sieve refinement past level ~12.** Kernel cost quadruples per level while the
  survivor density falls only from 6.25% to 3.2%; break-even is level 12–14 and
  the current level 10 is near-optimal.  Worse, the survivor count is
  supermultiplicative: safe words concatenate, so the number of surviving classes
  grows like `2^0.95k` at every depth and the sieve provably never clears.

## What is left

The archimedean input — the verified range — remains the only asset that is not
`d`-uniform, and the cycle bound scales with its square root; that is why 520
became 1539 by evaluation alone.  Against it stands one genuinely arithmetic
mechanism, the order obstruction, currently confined to a single run.  A proof
architecture, if there is one, now looks like:

    cycle → gap divides accumulator → order of 2 modulo the gap
          → collapse of the mixed-base sum → contradiction

with the open link being the collapse for `k ≥ 2` runs.  Everything else the
round touched is either a sharpening of what was already known, or a proof that a
hoped-for mechanism cannot exist.


## Round 2, second half — what the follow-up agents settled

### The order mechanism, generalised and then closed

Grouping the accumulator by runs makes it telescope: with `Sᵢ = 2^tᵢ·3^(a−Bᵢ₋₁)`
each summand is `Sᵢ − Sᵢ₊₁·2^(−eᵢ)`, the endpoints are `3^a` and `2^L`, and those
are the same number modulo the gap.  So

`C ≡ Σᵢ μᵢ·(2^eᵢ − 1)  (mod d)`, one term per **even block**, `μᵢ` a unit —

which at `k = 1` *is* `OneRunOrder`.  Proved at `k = 2` in `TwoRunOrder`.

And then closed, honestly.  The collapsed sum satisfies `A = C + d` **exactly**,
for every word and every `k`, so the passage is a re-coordinatisation and not an
elimination.  What it exposes is `v₂(A) = b₁`, the leading odd run; only at
`k = 1` does that carry the whole odd-step count, and there the residual term is
the *fixed* `2^(L−a) − 1`, which bounds `d`.  Past one run the residue is the
Simons–de Weger cyclic system with `2(k−1)` free exponents.  Measured exclusion:
`A < d` kills 92.4 % of two-run words and plateaus at 7.6 % surviving; three runs
are *worse*, 12.7 %.  Decisively, the genuine two-run `3x−1` cycle through `17`
attains `A = d`, so any strengthening is **unsound**, not merely unproved.

### Where the constant `d` lives (`DenominatorScalar`)

`C(w, d) = d · C(w, 1)` exactly: the parity word supplies the accumulator, the
constant supplies only a scalar.  A cycle needs `gap ∣ d · U`, so at word level
the entire problem is uniform in `d` **except through `gcd(d, gap)`**.  That
leaves exactly two non-uniform levers: `gcd(d, gap)` — which is trivial precisely
when `d = 1`, so `d = 1` is the hard case, not an easy one — and positivity, i.e.
the verified range.  `3x+5` has its cycle at `(5, 3)` because the gap there is 5.

### The backward side, closed with a number

Forward runs convert `v₂(u)` into `v₃(u)` one for one, and `RunInvariance` says
the master bound is invariant under exactly that conversion — so combining the
two mirror rations is an **algebraic identity**, not a new constraint.  Measured
to prefix length 220 over 4 M starts: the master bound multiplies the no-drop
survivor density by a constant `0.52`, flat from `k = 20` to `k = 150` — the same
exponent, a fixed gap of `0.85–0.94` bits.  Covering systems are closed too: the
backward classes form a nested 3-adic filtration with all moduli distinct powers
of three, and by Davenport–Mirsky–Newman–Rado no finite exact cover exists.

`HeavyWord` is provably inert here: heaviness *is* never-dropping in the log
coordinate, the same quantity the master bound is measured against.  Its only
backward consequence is a count — at most 956 master-bound tests exist inside the
proved-heavy prefix of 2592 steps.

### Corrections to earlier entries in this file

* **The verified range is not the only non-`d`-uniform asset.**
  `orbit_backward_bound` also consumes `accOrbit_small` ("the orbit of 1 stays
  ≤ 2"), which **fails for `d = 7, 11`** — there the master bound is false at the
  minimum itself (`d = 7`, `m = 5`, `u = 12`: `24 < 36`).  The soundness filter
  is unaffected, since `d = −1` and `d = 5` have both bounded orbits of 1 and
  genuine cycles.
* **"32 % of even steps inject 3-divisibility" is not randomness.**  In the
  shifted coordinate `u = x + d`, the residue mod 3 is a three-state machine:
  odd steps land on `0`, even steps swap `0 ↔ 2`, and `3 ∣ x` is an unreachable
  fixed point.  So `3 ∣ u` happens at *exactly every second point* of an even
  run — deterministic, period two.  This is the same fact `ThreeResidue` proves
  from the accumulator, arrived at from the orbit side.
* **Realizability was measured wrong.**  "Ratio 1.0000, gains nothing" was taken
  with `a` free, where the maximiser is the all-odd word and the ratio is 1
  vacuously.  Per `(j, a)` the ratios are `0.722, 0.460, 0.274, 0.166`.  The
  conclusion — that realizability alone does not break the density wall — stands.

### The state of the frontier

`CycleLength2593` and `HeavyWord.heavy_window_2592` reach the same `(2593, 1636)`
from opposite sides, and both stop where the same certificate first fails.  Three
points now fix the price of the archimedean asset: `102400 → 520`,
`307200 → 1539`, `768000 → 2593`; the bound grows like the square root of the
verified range.  Everything else the round produced is either a sharpening of
what was known, or a proof that a hoped-for mechanism cannot exist.


## The frontier, final for this round: 4701

The product bound compares `3^a·(2c + a)` against `2c·2^j`, and its accumulator
input is `C ≤ a·3^(a−1)`.  That input is loose, and not by a little: the odd-step
*times are integers*, so the true ceiling is the recursion

`Bcap(a+1) = 3·Bcap(a) + 2^(⌊a·log₂3⌋)`,

whose steps land on the integer points of `i·log₂3` rather than on a smooth
envelope.  Realizability, not size.  The gain is a constant factor — measured
`0.7213 = 1/(2 ln 2)`, which is `∫₀¹2^(−u)du`, forced because `log₂ρᵢ = tᵢ −
i·log₂3` is pinned modulo one — and constant factors move this frontier a long
way, because it grows like the square root of its input.

| verified range | product bound | realizability bound |
|---|---|---|
| 102 400 | 520 | 1539 |
| 307 200 | 1539 | 2593 |
| 614 400 | — | 3647 |
| 768 000 | 2593 | **4701** |

The realizability bound at a given range matches the product bound at about two
and a half times that range.

Two simplifications made it cheap.  The induction needs no odd-step-time
bookkeeping at all — the time at which the `(a+1)`-st odd step is taken *is* the
`j` at which it is taken — and the cycle exclusion needs no sweep over lengths,
because the same lemma applied at `j = L` gives `L ≤ ⌊a·log₂3⌋` and contradicts
`3^a < 2^L` outright.  One `decide`, 2966 facts on integers up to 1418 digits,
under a second.

The window lemma that comes out is sharper than the one it was built for: it
holds at **every** time, not only at odd-step times, so it bounds `2^j` by
`3^(oddCount m j)` with no factor of two and no cap on `j` — only on the odd-step
count.  That supersedes `HeavyWord.heavy_window_2592` (whose `j ≤ 2592` implies
`a ≤ 2592 < 2966`).  *Corrected:* it does **not** supersede
`CycleProduct.neverDrops_heavy_window`, which is weaker by a factor of two but
reaches far further — its side condition `2a ≤ 3m` admits `a ≤ 1 152 000` at
`m = 768 000`, roughly 390× the new lemma's `a < 2966`.  The new lemma drops the
factor of two and extends the *exact*-heaviness range from `j ≤ 2592` to
`j ≤ 4700`; it does not extend the factor-two heaviness.

Recorded because it was checked and found wrong: the tidy majorant
`4C ≤ (a+1)·3^a` is true but **not** provable by the obvious induction — the step
needs `frac(a·log₂3) ≥ log₂(4/3)`, which fails at about 40 % of indices, and no
constant strengthening repairs it (the two `⌊i·log₂3⌋` jump cases force
incompatible constants).  `Bcap` itself is sharper and no harder for the kernel.


## The round's one unexplained measurement, refuted

`w ↦ C(w)` looked injective on heavy words — exhaustively to length 28, while
colliding freely on arbitrary words.  Had it been true, `C` alone would have
determined a never-dropper's residue class.

**False.  First collision at length 83:**

    r  = 682585550255899720490087    a  = 53
    r' = 5448846481649007412081903   a' = 55
    C  = 212525282698140465463422331

Both heavy at all 83 prefixes.  Five collisions there, twenty more at 86.
Injectivity is *proved* below 58 and exhausted by a complete decision procedure
to 82 — the measurement was honest, the search was short.

Two facts explain the whole shape, and both are now in `HeavyResidue`:

* **`C ≡ 3^a (mod 4)` on every heavy window.**  Heaviness at `i = 2` needs
  `4 ≤ 3^a₂`, so a heavy word starts with *two* odd steps; every later odd step
  adds `2^j` with `j ≥ 2`, invisible mod 4, and multiplies both sides by three.
  So `C` knows `a` modulo two, and the cheapest collision — counts differing by
  one — is impossible.  This is why the joint search over `(r, 3^(−k)r)` returns
  literally zero both-heavy pairs for odd `k`.
* **Size closes the window only temporarily.**  With
  `C/3^(a−1) = Σ 2^tᵢ/3^(i−1)`, heaviness caps every term at one so the sum is
  at most `≈ 0.7213a`, and ordering floors it at three.  A collision at
  `a' = a+2` needs two such sums a factor of nine apart inside `[3, 0.7213a]` —
  impossible until `a ≈ 37`, i.e. `j ≈ 58`.  The margin shrinks **linearly**: the
  ceiling grows with `a`, the target is the constant 27.  The window opens at 58;
  the first collision lands at 83, with the ratio exactly 9.

Two by-products worth keeping.  The factor of two that `HeavyWord` removes from
the older window bound is *precisely* what makes the mod-four law available:
relaxing heaviness to `2^i ≤ c·3^aᵢ` survives to 24 at `c = 3/2` but breaks at
`c = 2` with an **odd** count difference, because `c = 2` is the constant that
admits a word beginning `OE`.  And `heavy_accumulator_bound_sharp` improves the
stored bound by a factor `3/2` from the identical induction.

The negative conclusion constrains future work: `C` is not a complete invariant
of a heavy window, so anything carrying window data must keep carrying the pair
`(oddCount, affineC)`.

Note also that this question could never have been decisive: `C(w,d) = d·C(w,1)`
and heaviness is `d`-free, so it was literally the same statement for `3x−1` and
`3x+5`.  The soundness filter would have caught it before the search did.

---

# Round III — the obstruction moves from size to distribution

Fifteen agents, eleven in parallel, in eleven different mathematical languages.
The round's finding is structural and can be stated in one paragraph.

**The cycle problem is now one-dimensional, the size route has a proved ceiling,
and what remains is a question about how `C(w)` is distributed modulo the gap.**

## The collapse: `L` is a function of `a`

`GapSandwich.cycle_length_determined` — for a nontrivial accelerated cycle with
minimum `m` and odd-step count `a < 1152000`,

`L = ⌊a · log₂ 3⌋ + 1`   exactly.

The repo previously had only the one-sided `fexp a < L`.  Two-sidedness collapses
the search from two parameters to one and fixes `G = 2^(fexp a + 1) − 3^a` as the
*least* gap available at that `a`.  `MinimalCycle.ledge_rigid` reaches the same
statement independently through the product invariant rather than the realizable
ceiling — two routes, one ledge.

It is also **certificate-free**.  `GapSandwich.Bstar`/`Ecap` degrade where
`RealizableBound`'s induction collapses, so `L ≥ 2593` now follows with *zero*
kernel computation, replacing a 2592-index `decide` over 1400-digit numerals with
a three-line induction.

Only **358** values of `a` below 40000 survive the size sandwich under the exact
`Bstar` criterion, one `L` each.  (Survivor counts in this file are criterion-
sensitive: the crude majorant `2a·3^a/3` gives 2216 below 60000, the smooth
constant `K = 0.7213` gives 2393, and the exact `Bstar` gives 811.  Any count
quoted without naming its criterion should be distrusted.)
They are exactly `a = 306k + 665j`, and the gaps between consecutive survivors
are drawn from the small set `5, 12, 17, 29, 41, 53, 94, 147, 200, 253, 306, 359,
665` and nothing else.  *Corrected:* an earlier version of this paragraph called
these "exactly the continued-fraction denominators of `log₂ 3`".  They are not —
the convergent denominators are `1, 2, 5, 12, 41, 53, 306, 665, 15601`, and
`17, 29, 94, 147, 200, 253, 359` appear nowhere in that list.  They are the
**semiconvergents** (intermediate fractions): `17 = 5 + 12`, `29 = 5 + 2·12`,
`94 = 41 + 53`, and then `147, 200, 253, 306, 359` each adding a further `53`.
The distinction matters, because semiconvergents are exactly what the
three-distance theorem produces, and convergents alone would have been a much
stronger and much less generic statement.

## The ceiling: how much the archimedean route can ever buy

`ArchimedeanCeiling.sandwich_vacuous` — the inequality that produces *every*
frontier bound in this development is satisfiable outright once `a ≥ 3N`.  Powers
of two are never more than a factor two apart, so the least `L` overshoots `3^a`
by at most `3^a`, while the permitted gap grows *linearly* in `a`.

So the family is capped at `a < 3N`, and no sharpening of the analysis around
that inequality reaches past it.  The *achieved* bound is far below the ceiling,
and now explained: the argument stops at the first `a` whose distance from an
integer multiple of `log₂ 3` dips below a linear-in-`a` threshold, which by
three-distance is of order `√N`.  **That is the empirical square-root law**, and
the criterion reproduces the repo's own product bounds on the nose:

| `N` | first admissible `a` | `L` | bound recorded in the repo |
|---|---|---|---|
| 102 400 | 306 | 485 | 520 |
| 307 200 | 971 | **1539** | **1539** |
| 768 000 | 1636 | **2593** | **2593** |

Extrapolating: `N = 10⁷` buys `L = 12079`; `N = 10⁹` buys `75235`; `N = 10¹²`
buys `301994`.  The cost is quadratic in the bound.  This route will not reach a
proof, and the round's remaining work was directed accordingly.

## The measurement that redirected the round

`CycleLanguage`.  The heavy language grows at exactly `H₂(log 2/log 3) = 0.94996`
bits per letter, and that entire drop from one bit is the *density*, which
`3^a < 2^L` already forces.  `heavy_pad` shows the factor set of the heavy
language is all of `{0,1}^*` — prefixing any block with `2k` odd steps keeps every
prefix heavy — so there are **no forbidden blocks**, the language is not sofic,
and every finite-block SFT over-approximation of it is the full shift.  No finite
automaton can ever see the 0.94996.

The cyclic constraint costs a factor `L` and no entropy: by the cycle lemma no
word has two heavy rotations, and at `(4701, 2966)` the heavy count equals
`binom(4701, 2966)/4701` exactly.

Then the key number, and it came out the opposite way from what was feared.  At
the frontier pair the number of heavy words is `2^(−243.63)` times the gap, and
the deficit *grows* linearly at `0.05019` bits per step of `L`.  Independently
recomputed: `log₂ N = 4447.169`, `log₂ G = 4690.795`.

**The counting budget is in surplus by 243 bits and widening.**  A counting
argument is therefore not dead a priori.  What is missing is a nontrivial bound
on the exponential sum

`S(k) = Σ_{w heavy} e(k · C(w) / G)`,  `k ≢ 0 (mod G)`,

and the bridge must be **statistical, not injective** — injectivity of `w ↦ C(w)`
was refuted last round at length 83.

## Closed by proof this round

* **Every odd modulus is independent of the parity word.**
  `ValuationBudget.word_residue_free`: for every `x`, window length `j`, odd `m`
  and target `r` there is a `y ≥ x` with the *identical* window — same `oddCount`
  and same `affineC` at every index — and `y ≡ r (mod m)`.  The witness is
  explicit: `2` is a unit mod odd `m` with inverse `((m+1)/2)`, so `x + 2^j t`
  sweeps every residue while fixing the whole word.  Hence no proper invariant
  residue set at any odd modulus, and heavy windows of every length carry every
  residue mod every odd `m`.  Any future `p`-adic, covering-system or
  automaton-mod-`p` proposal should be checked against this before any effort.
* **`v₃(C) = 0` has no analogue at any `p ≥ 5`.**  The heavy word `oo` already has
  `C = 5`.  Two and three are the only primes in the recursion, so they are the
  only primes with a structural law.
* **`(oddCount, length, runA)` is a complete invariant of the word.**
  `RunAlgebra.runA_word_eq`.  This is the honest replacement for the refuted
  accumulator injectivity, and it is consistent with that refutation: every
  `affineC` collision at fixed length has distinct odd-count, the length-83 one
  included.  Verified exhaustively over all `2^20` words.
* **Word surgery is closed.**  `(a, L, A)` determining the word means no block can
  be merged or shortened, so no compression descent exists.
* **There are no forbidden runs.**  The joint law of `(oᵢ, eᵢ)` is exactly the
  Terras product measure `2^(−o−e)`; every pattern with `o, e ≤ 3` is realised;
  `oᵢ` and `eᵢ` are independent.  The target theorem *"every cycle contains a
  structurally impossible run"* is **false as stated**.
* **No single-step edit of a cycle word produces another cycle.**  Even-step edits
  are dead twice over — the gap `2^(L−e) − 3^a` is not even positive, and the
  target is off the ledge.  Odd-step edits are on-ledge for `2 − log₂ 3 = 41.5 %`
  of `a` and then need divisibility by a number `≥ 2^(L−1)/3`.  The reason, cleanly:
  a cycle exists because `|2^L − 3^a|` is exceptionally small, a continued-fraction
  property of `log₂ 3`; no edit of size one can preserve it, and the smallest that
  could is twelve.
* **The min-cut/max-cut idea has no second inequality.**  `MinimalCycle.cut_exact`:
  chaining the two block equations returns `3^a ≤ 2^L` and nothing else, because
  the reassembly *is* the cocycle law and the slack is exactly zero.
* **The pigeonhole across rotations does not exist.**  `G ∣ C` at one rotation
  implies it at all `L` rotations (`AccumulatorCap.dvd_affineC_shift`), so the
  simultaneous condition is exactly equivalent to the single one.  Confirmed
  exhaustively over all words to length 22.
* **The verified-range bootstrap closes but loses.**  Gain exactly
  `3(1 − (2/3)^a)/a` — `0.833` at `a = 2`, `0.00101` at the frontier.  The whole
  loss is the spread of the accumulator at fixed odd-count, and both ends are
  attained: the ceiling by the Beatty word, the floor `3^a − 2^a` by the one-run
  word.  What the verified range buys is a *staircase*, not a loop: each rung
  costs a new sweep and multiplies the range by about `1.096`.
* **Generalising the mod-four law is literally the sieve.**
  `Bootstrap.affineC_mod_pow` — `C` is always a 3-adic unit times a seed depending
  only on the first `m` letters — and the bootstrap holds exactly when the heavy
  words admit a *single* seed.  The seed count is on the nose
  `SieveGrowth.safeCount m = 1, 1, 1, 2, 3, 4, 8, 13, 19, 38, 64, …`.  So `m = 2`
  is the last modulus with one seed, a boundary effect of `2² > 3¹`, and the
  generalisation is the sieve, already proved never to clear.  Counterexample:
  `x = 11`, word `1101`, heavy at every prefix, `C = 23` against `3³ = 27` —
  equal mod 4, different mod 8.

## New positive structure

* `Rotation.light_of_max` — the word read from an orbit **maximum** is light at
  *every* prefix.  Hence the largest point of any cycle is even and the smallest
  is odd.  `exists_cycle_max` supplies the argmax the repo lacked.
* `Rotation.no_cycle_of_no_three_power` — no cycle heavy at its last prefix exists
  at any length with no power of three in `[2^(L−1), 2^L)`, about 35 % of lengths.
* `RunAlgebra.runA` — the accumulator of the shifted coordinate `u = x + 1`, fed
  only by *even* steps where `affineC` is fed only by odd ones, with
  `A + 3^a = C + 2^L` and no subtraction.  `phi_const_odd`/`phi_incr_even`:
  `2^j(T^j x + 1)/3^a` is exactly constant across every odd step and increases
  only on even ones.  All new information comes from even steps — now an identity,
  not a slogan.
* `RunAlgebra.heavy_run_count` — a heavy word with `a` odd steps has fewer than
  `10a/17` complete runs, from `3^17 < 2^27`.  Sharp to one:
  `1101101101011011010` has `10B − 17r = 1`.
* `Bootstrap.affineC_ge_pow` — `3^a ≤ C + 2^a`, no hypotheses.  The exact dual of
  `AccumulatorCap.affineC_cap`; the repo had only the upper side.
* `MinimalCycle.append_even_descends` — unconditional: if `(L,a,C,n)` and
  `(L+1,a,C,n')` are both certificates then `2n' < n`.

## Corrections, including to this file

The adversarial agent audited every headline claim against the Lean source.  The
mathematics survived; the prose did not.

* **A real axiom leak, now closed.**  Seven `native_decide` calls were live in
  `Papers/Conway1972.lean`, imported by `Collatz.lean`, each compiling to a
  trusted axiom — and `check_integrity.sh` printed `integrity passed` with them in
  place, because its grep was `\b(sorry|admit|axiom)\b` and nothing else.  That
  misses `sorryAx` (`\bsorry\b` does not match it), `native_decide`,
  `ofReduceBool`, `unsafe`, `partial`, `opaque`, `@[implemented_by]` and
  `@[extern]`.  All eight now fail the check, verified against probe files.  The
  script also gates on `#print axioms` directly, which no keyword list can fool.
  No frontier theorem depended on the leaked facts — they were "27 reaches 1 in
  111 steps" — but the repo's central safety claim was false as written.
* **The soundness-filter asset list was incomplete, and would have caused false
  kills.**  There are four `d = 1` assets, not two: the verified range;
  `accOrbit_small`; **sign(d) = +1** — for `d < 0` the gap is negative and the Nat
  argument does not typecheck, and this is what `OneRunOrder` actually uses; and
  **`|d| < 2`** — exclusion inequalities of the shape `2^m + |d|·6^a ≤ 2^(m+a)`
  can only hold for `|d| ≤ 2`, and with `|d| = 5` or `7` the analogue holds for
  *zero* `a` in `1..59`.  A mechanism using neither of the first two is not
  automatically unsound.  Note `(c)` and `(d)` together still do not separate
  `d = 1` from `d = 5`.
* **The order obstruction's range was overstated here by 100×.**  Corrected in
  place: the Lean theorem clears `a < 2048`, the kernel budget of `gapOK_sweep`.
* **"Strictly supersedes `neverDrops_heavy_window`" was false.**  Corrected in
  place: the new lemma drops the factor of two and extends *exact* heaviness from
  `j ≤ 2592` to `j ≤ 4700`, but `neverDrops_heavy_window` reaches `a ≤ 1 152 000`,
  roughly 390× further.
* **Two numbers inside `RealizableBound`'s own docstrings were wrong** and are
  fixed: the margin at the top of the certified range is `620 858` at `i = 2301`,
  not `767 707` (which occurs nowhere), so the slack is 19 % rather than 0.04 %;
  and the mirror audit's `m = 5` first fails at `i = 5`, not `i = 3`.
* **`Σᵢ v₂(nᵢ) = L − a` is false**, found independently by two agents.  Each even
  run of length `r` contributes `r(r+1)/2`.  The `3x−1` cycle through 17 has
  `L − a = 4` but `Σ v₂ = 7`.
* **The frontier bounds are about the accelerated map.**  A raw `3n+1` cycle of
  the same orbit has length `L + a ≈ 1.63 L`, so the numbers are conservative,
  but "length" has been used unqualified.
* **`ExchangeRate.no_valuation_size_ranking` is a *global* statement**, quantified
  over all `x > N`, not over an orbit.  A rank of that shape decreasing only
  *along* a counterexample orbit is not excluded.  The failed-approaches table
  overstated it.
* **The theorem count of 1558 was stale**, not inflated.  Kernel constants filtered
  to `.thmInfo` with the `Collatz` prefix: **1694** before this round, **1945**
  after it — the two independent measurements reconcile exactly (1937 taken before
  `JointRank` landed, plus its 8 theorems).

## The question Round II left open is now answered — and closed

Round II ended naming one frontier: *"the open link being the collapse for
`k ≥ 2` runs"*, sharpened to whether a two-term S-unit relation can bound its own
modulus.  It can, exactly, and the bound is attained.

`SUnitRelation.run_telescope` (LEAN_PROVED, all `r`, over `List (Nat × Nat)`)
generalises `TwoRunOrder`'s `r = 2` identity to every number of runs:

`A + 3^a = C + 2^L`,   i.e.   `A = C + G`,   unconditionally, for every word.

Verified on all **2 097 151** words of length 2…22 that start odd and end even,
against `affineC` computed from its recursion: zero failures.  For a cycle this
gives `A = G·(m+1)`, and since only the first term of `A` carries `2^(o₁)` while
every other carries `2^(o₁+e₁)`, and `G` is odd:

> **`SUnitRelation.cycle_gap_lead_le` : `G · 2^(o₁) ≤ A`.**

At `r = 1` this *is* `OneRunOrder`'s bound, so it is the correct `k`-run
generalisation of the order obstruction.

The universal identity behind it, verified on every genuine cycle in every
`d`-world tested, is

`d · A = G · (m + d)`.

The Lean theorem is a `Nat` statement carrying `3^a < 2^L`, so it is about
`d = 1`.  Its `d`-dependence is **asset (d), `|d| < 2`**, and that is not a
formality: for `d = 5` the inequality is simply **false** — the cycle through 19
has `|G|·2^(o₁) = 40` against `A = 24` — because `5 ∤ 19`, so `A/G` is not an
integer and the 2-adic argument never starts.

What the table below establishes is therefore narrower than "the bound is
`d`-free", and is the thing that actually matters: the *magnitude* inequality
`|G|·2^(o₁) ≤ |A|` holds for `|d| = 1` in **both** signs, and is **attained** in
the `d = −1` world.  So any strengthening resting only on `|d| = 1` is dead.  Only
a strengthening that additionally consumes **asset (c), sign(d) = +1**, remains
formally possible — and no such thing is in sight, because the identity above
leaves nothing to strengthen.

| map | cycle | runs | `G` | `A` | `|G|·2^(o₁)` |
|---|---|---|---|---|---|
| `3x+1` | 1 | (1,1) | 1 | 2 | **2 — equal** |
| `3x−1` | 5 | (2,1) | −1 | 4 | **4 — equal** |
| `3x−1` | 17 | (4,1),(3,3) | −139 | 2224 | **2224 — equal** |
| `3x+5` | 5 | (1,1) | 1 | 2 | **2 — equal** |
| `3x+5` | 19 | (3,2) | 5 | 24 | 40 — **inequality fails** |

Equality holds exactly when `|m + d| / |d| = 2^(o₁)`; for `d = 1` that reads
`m + 1 = 2^(o₁)`.  (An earlier draft of this paragraph wrote the condition as
`m + d = 2^(o₁)`, which is wrong in both sign and scale — it fails at `d = −1`,
`m = 17`, where `|m+d|/|d| = 16 = 2⁴` but `m + d = 16` only coincidentally, and at
`d = 5`, `m = 5`, where `m + d = 10` is not a power of two at all while
`|m+d|/|d| = 2` is.  Corrected after checking all eight known cycles.)

The order route at `r ≥ 2` is therefore *complete and closed*, not merely open,
and the reason is structural rather than technical: `d·A = G·(m+d)` is an
**identity**, so `G ∣ A` is the cycle equation restated.  No order information can
be extracted that is not already the cycle equation.  This is a
re-coordinatisation, and now provably the last one available.

This is strictly sharper than the ledger's earlier "`A = d` attained": the real
attained bound carries the factor `2^(o₁)`.

Three by-products worth keeping, all from the same file:

* **`one_run_gap_ineq`** — a one-run cycle forces `2^a·(G+1) ≤ 3^a + G`.  That is
  `OneRunOrder.gapOK` with `L` eliminated, so with
  `GapSandwich.cycle_length_determined` supplying `L`, it becomes a
  one-parameter test.
* **`one_run_min_ge`** — a one-run cycle has minimum `≥ 2^a − 1`, using **no
  verified range**.  Tight at the trivial cycle.
* The one-run branch is far stronger than this ledger recorded.  Elementary
  continued-fraction input — Legendre's criterion, Baker-free but real-analytic,
  hence not formalisable without Mathlib — clears **`4 ≤ a ≤ 397 573 379`**, a
  190 000× extension of the kernel sweep's `a < 2048`.  It annihilates the
  archimedean survivor `a = 15601`, `L = 24727` by a factor of `2^15586`.
  (`minLen(15601) = 24727`; an earlier note here said 24728.)

Zsigmondy was adapted honestly and is vacuous exactly where it would matter.
With `g = gcd(L, a)`, `G = X^g − Y^g` for `X = 2^(L/g)`, `Y = 3^(a/g)`, so
Zsigmondy applies and gives `p ∣ G` with `p ≡ 1 (mod g)` — but for a one-run cycle
with `L ≥ 8` one has `g = 1` and the statement is empty.  Over `a ≤ 400`,
`L ≤ 800` the only pair passing the one-run test at all is the trivial `(1, 2)`.

One further computational fact closes off a hoped-for source of extra constraints:
over all words of length ≤ 22, `G ∣ C` with `C/G > 0` holds for exactly **11**
words, and **all 11 are genuinely realised** — the Terras consistency condition
adds nothing beyond `G ∣ C`.  The S-unit condition is *equivalent* to a cycle,
not merely necessary.

## The soundness filter is now a theorem, and it names the target

`NewModels.word_is_cycle_word` / `denominator_one` (LEAN_PROVED).  Let `w` be any
parity word of length `L` with `a` odd letters, `C = affineC L r`,
`G = 2^L − 3^a > 0`.  Put `δ(w) = G / gcd(C, G)` and `n = C / gcd(C, G)`.  Then

> **`n` is a genuine cycle point of period `L` of `x ↦ (3x + δ(w))/2`, carrying
> exactly the parity word `w`.**

and `δ(w) = 1` is precisely the `3x+1` cycle criterion.  Checked exhaustively over
all **112 892** words of length 2…16 with positive gap: zero failures; the only
words with `δ = 1` are the rotations of the trivial cycle, `n = 1` and `n = 2`.

This converts the soundness filter from an argument-from-two-examples into a
proof.  Heaviness, density, congruence class, multiplicative order of 2 mod the
gap, and every bound on `C` are functions of `w` alone.  Since **every** word with
a positive gap is a cycle word — of `3x + δ(w)` — **no property of the parity word
can obstruct a cycle.**  The whole problem is localised onto one quantity:

`gcd(affineC L r, 2^L − 3^a)`.

The decomposition this forces is sharp and exhausts the options.  For every word
`x_w = C/G ∈ ℚ₊` is determined and `n = δ·x_w`, so:

* the **archimedean** input (the verified range) bounds `max_w x_w` from above at
  each `L` — that is exactly `RealizableBound`, and is why the frontier is 4701;
* the **arithmetic** input must bound the **denominator** `δ(w)` away from 1.

Nothing else is left.  This is why the order obstruction was the only live
arithmetic channel — and `SUnitRelation` has now closed it.

One boundary, stated explicitly so the theorem is not overread: it refutes
*word-level* arguments, not arguments that use the verified range.  The attempt to
exhibit a heavy word with small `δ` and large `n` — which would have refuted those
too — fails, and instructively: `δ = n/x_w`, so a large `n` at small `δ` demands a
large `x_w`, which is the realizability ceiling again.  Measured minimum `δ` over
cycle-shaped words with `n ≥ 768000`: none at all below `L = 19`, then `347141`,
`517135`, `502829`, `2599981` at `L = 19…22`.  **The two levers are the same
lever.**

Three further models were taken up and returned negative results with reasons:

* **The word semigroup is free** — `NewModels.word_of_count_and_accum`, three
  lines and no induction, giving `class mod 2^L ↔ (a, C)` as an iff.  Parallel
  discovery with `RunAlgebra.runA_word_eq`, recorded as such.  Its consequence is
  that the accumulator **sumset has unique representation**, so Freiman-type
  structure is absent *by theorem*: there is no additive structure to exploit, and
  the "is a fixed class mod `G` hit rarely" question has no handle.
* **Generating functions are dead because of freeness.**  The monoid law
  `(L,a,C)·(L',a',C') = (L+L', a+a', 3^(a')C + 2^L C')` rescales the `C`-coordinate
  by a base change depending on the *other* factor, so it is not a convolution in
  any variable and no functional equation in `(x, y, z)` exists.
* **Thermodynamic formalism fails the soundness filter before any work.**  A
  potential on the shift is a function of the word, hence `d`-uniform.  A "second,
  arithmetic potential" would have to see `C mod G`, and `G` depends on the whole
  word — it is not locally constant, so it is not a potential at all.
* **Two more hatches in the ranking obstruction are now shut.**
  `no_variable_window_ranking`: no class function mod `m` can drop over a
  *variable* window, for any step family at all.  `no_ranking_on_heavy_prefix`: no
  finite heaviness side condition helps, because `2^L·m − 1` sits on an odd run of
  length `L` and survives every finite filter.  The one hypothesis that could not
  be closed is a rank on "class mod `m` **plus** the archimedean datum `⌊log₂ x⌋`",
  which is not a finite quotient and so is untouched by the existing theorems.
  Recorded as the live remnant.

## The counting theorem was vacuous, and the measurement was not

A second adversarial pass audited this round's *own* new claims.  The mathematics
held again; four things did not, and this is the one that matters.

`CycleLanguage.count_lt_gap_4701` and `count_lt_gap_5755`, as first written,
**counted the empty set.**  `heavyCount L a` demands heaviness at *every* prefix,
the last one included — and a cycle word cannot be heavy at `i = L`, because
heaviness there is `2^L ≤ 3^a`, exactly the negation of the gap being positive.
Since `fexp 2966 = 4700` puts `3^2966` strictly below `2^4701`,

`heavyCount 4701 2966 = 0`,

so the theorem asserted `0 < G`.  The file's own §"The three languages" defines
the cycle language as heavy at every *proper* prefix; `heavyCount` does not, and
the two disagree at precisely the pairs of interest.  A definitional mismatch the
file named and then walked into.

**The measurement was never in doubt** — `log₂(binom(4701,2966)/4701) = 4447.1688`
and `log₂ G = 4690.7951` were recomputed independently three times, and the
`2^(−243.6)` surplus stands.  What was missing was a theorem about it.

The repair is exact and costs nothing.  The cycle-language count splits on the
last letter:

`#cycle-language(L, a) = heavyCount (L−1) a + heavyCount (L−1) (a−1)`,

both terms nonzero.  Raising the smaller class to the common power costs a factor
two, so the combined majorant is `3·3^(L−1)` and the witness carries that three
(`deficit_of_witness_sum`).  The split identity was checked exhaustively: over
every `(L, a)` with `L ≤ 16` and `3^a < 2^L`, the number of words heavy at every
proper prefix equals `heavyCount (L−1) a + heavyCount (L−1) (a−1)` — **zero
mismatches** — and `heavyCount L a` is zero at *every one* of those pairs, not
only at the two the theorems used.  **Both advertised exponents survive unchanged**:
`205` and `254` are still exactly tight, and `206` and `255` are both false.  So
the headline numbers were right and only the object being counted was wrong.

One Lean-technique note, because it cost an hour and will recur: the repaired
lemma must take the common power as a *variable* `M`, not as `2 ^ (a+1)`.  Stating
it as a successor makes the elaborator unify `?a + 1` against a four-digit numeral
at each use site, and that unification does not terminate in any practical time —
the file simply never elaborated.  With `M` a variable and the successor
arithmetic done at the call site, both theorems compile in seconds.

Recorded as a standing gap: `heavyCount` is still not *proved* equal to the
cardinality of the heavy language.  The recursion is transparently the right
transfer count and reproduces the exhaustive figures (`heavyCount 20 13 = 8045`),
but the identification is an unproved bridge, and the deficit theorems should be
read as bounds on the recursion, not on a set.

### The other three kills

* **A staircase row was off by a whole riser.**  `RealizableFrontier6809`'s table
  claimed `c ≥ 420 842 ⟹ A = 2966 ⟹ L ≥ 4701`.  The `G`-records are
  `238 670, 420 841, 620 858, 841 477, 1 086 054, 1 358 717`, so `A(420 842) =
  2301` and the frontier is `L ≥ 3647`; the threshold for `A = 2966` is
  `c ≥ 620 859`.  The table silently deleted the `A = 2301` riser.  Every other
  row was exact.  Also corrected there: the margin by which `768 000` missed was
  `73 477`, not `3 477` — a dropped digit.
* **The S-unit sharpness argument cited cycles that cannot instantiate its own
  theorem.**  `cycle_gap_lead_le`'s `hgap` is a `Nat` statement needing a
  non-negative gap, so the `3x−1` witnesses fall outside it — the equality they
  satisfy is the sign-flipped `A = |G|·(m−1)`.  Worse, exhaustive search over
  every run list with `runLen ≤ 24` *inside* the hypotheses finds equality only at
  `rs = (10)^r`, and **every in-scope equality case has `m = 1`** — the trivial
  cycle traversed `r` times.  So "sharp at `r ≥ 2`" survives, but a strengthening
  consuming `m ≥ 2` is not refuted by any in-scope witness.  The closure argument
  rests on the out-of-scope `d = −1` witnesses, which kill any `|d| = 1`-only
  strengthening; that is what it establishes, and no more.
* **A docstring cited a theorem that does not exist** — `word_denominator_least`
  appears nowhere in the repository, and minimality of `δ` is never proved.

### And the claim about continued fractions was wrong in three files

This ledger, `GapSandwich` and `MinimalCycle` all said the gaps between
consecutive surviving `a` "are exactly the continued-fraction denominators of
`log₂ 3`".  They are not.  The convergent denominators are `1, 2, 5, 12, 41, 53,
306, 665, 15 601`; the observed gaps include `17, 29, 94, 147, 200, 253, 359`,
none of which is in that list.  They are **semiconvergents** — `17 = 5 + 12`,
`29 = 5 + 2·12`, `94 = 41 + 53`, then `147, 200, 253, 306, 359` each adding a
further `53`.  That is what the three-distance theorem produces, and it is a
weaker, more generic statement than the one it replaces.  `MinimalCycle` also
listed `29` as a convergent denominator, which it is not.

Two smaller repairs: `Rotation`'s "both sets are empty" holds for `a ≥ 1` but not
for the all-even word, which has `C = 0` and is divisible by every gap; and
`ArchimedeanCeiling`'s "the cost is quadratic in the bound" is contradicted by its
own table (`L/√N` spreads over a factor of twelve across the rows), so the `√N`
law is an average, not an exponent — what is exact is the ceiling, not the rate of
approach to it.

Verified clean under this second audit, with independent recomputation: the whole
`6809` frontier including a direct simulation of all 19 904 surviving residues in
blocks 750–1060 (**max steps-to-drop 183**, against fuel 200, first failure at
block 1099 exactly as claimed); `GapSandwich`'s entire induction chain, with
`affineC_le_Bstar` stress-tested on 200 000 real orbit prefixes for zero
violations; `word_is_cycle_word` exhaustively to `L = 14`; `ExpSum`'s Parseval
normalisation and all nine rows of its measurement table; both completeness
theorems; and `sandwich_vacuous`'s constant.

## The exponential-sum route is closed too — by an unconditional barrier

The 243-bit surplus is real and was confirmed from a second direction.  It is
also **unreachable by any absolute-value or character method**, and the reason is
a two-line barrier rather than a hard estimate.

For **any** map `f : W → Z/G` with `|W| = N ≥ 1`, let
`R = #{(w,w') : f(w) = f(w')} ≥ N`.  Parseval gives `Σ_k |S(k)|² = G·R`, and
`|S(k)| ≤ |S(0)| = N`, so

`Σ_{k=0}^{G−1} |S(k)| ≥ (Σ_k |S(k)|²)/max_k |S(k)| = G·R/N ≥ G.`

Hence `Σ_{k≠0} |S(k)| ≥ G − N`, and the triangle bound
`Z ≤ N/G + (1/G)Σ_{k≠0}|S(k)|` has right-hand side **≥ 1, always** — for every
`W`, every `f`, every `G`.  The circle-method route to `Z < 1` is not hard; it is
**vacuous**.  It applies verbatim to every divisor `q ∣ G`, so no smaller modulus
escapes.  Verified numerically, and the barrier is *tight* exactly at perfect
equidistribution.

The measurements, taken before the theory as instructed (exact FFT over all `k`,
full enumeration of the cycle language):

| `L` | `a` | `G` | `N` | `max|S|/N` | `mean|S|/√N` | `Σ_{k≠0}|S|/G` |
|---|---|---|---|---|---|---|
| 8 | 5 | 13 | 7 | 0.394 | 0.641 | 1.57 |
| 13 | 8 | 1631 | 85 | 0.530 | 0.749 | 6.90 |
| 16 | 10 | 6487 | 476 | 0.373 | 0.690 | 15.05 |
| 18 | 11 | 84997 | 961 | 0.687 | 0.687 | 21.31 |
| 20 | 12 | 517135 | 2652 | 0.836 | 0.653 | 33.64 |

So square-root cancellation **is** present on average (`mean|S|/√N ≈ 0.65–0.89`,
stable) — the naive question answers *yes*.  But there are always major arcs at
`k ≈ G/q` for small `q`, because `C` is genuinely non-equidistributed at small
moduli (`t₁ = 0` always, so `C` is odd; and `C ≢ 0 mod 3` always).  And the column
that matters is the last: the bridge needs `Σ_{k≠0}|S(k)| < G − N`, and it is
measured at 1.5 to 33.6 times `G`, growing like `0.65√N`.

At the frontier pair even a *perfect* `|S(k)| ≤ √N` gives `G·√N = 2^6914.4`
against a budget of `2^4690.8` — **short by 2224 bits**.

Two supporting closures, both exact:

* **The transfer matrix is provably blind to `k`.**  Writing
  `S(k) = e₀ᵀ M_{L−1}(k)⋯M_0(k) e_a`, each `M_j(k) = I + D·S` with `D` diagonal
  *unitary*; conjugating by a diagonal unitary gives `V*M_jV = I + S`, phase-free.
  So `‖M_j(k)‖` is independent of `k` and of `j`, and the product bound is `≈2^L`,
  *worse* than the trivial `N = 2^(0.94996 L)`.
* **The bilinear form gives exactly square-root cancellation and no more.**  The
  cocycle split must condition on `b = a_u`, and Cauchy–Schwarz across the `a+1`
  blocks yields `|S(k)| ≲ √((a+1)N)` — precisely the bound that is 2224 bits short.
* **No small prime divisor of `G` is structurally avoided.**  For every `p ∣ G` at
  every enumerable pair, `#{w : p ∣ C(w)}` matches `N/p` within ordinary
  fluctuation.  There is no cheap small-modulus obstruction.

One correction to my own framing of this task, recorded because it was wrong: I
described the situation as collision-forced, with `2^4447` words mapping into
73478 admissible targets.  That is not the shape.  `C` maps into its own *range*
`[0, a·3^a/2]` and is **sparse** there — density `2^(−264.4)` — and the ~`10⁶`
admissible multiples of `G` then give expected hits `2^(−243.7)`, independently
reproducing the counting figure.  Both facts coexist: expected colliding pairs are
`N²/range = 2^4183`, which is why `HeavyResidue`'s length-83 collision is
unsurprising, but `2^4183 ≪ N`, so almost every value of `C` is attained exactly
once.

## The many-primes thesis, refuted three ways

The most natural remaining idea was: `G ∣ C` is a system of `ω(G)` simultaneous
conditions, so a gap with many prime factors is overdetermined.  It is wrong, and
the refutations are independent.

**Structurally**, by CRT the `ω(G)` conditions `C ≡ 0 (mod p_i^(e_i))` *are* the
single condition `C ≡ 0 (mod G)`.  Splitting `G` into primes adds nothing and
removes nothing; the strength is `1/G` whatever `ω(G)` is.  More primes means
*weaker* individual conditions, not more of them.

**Computationally**, `ω(G)` is small and does not grow — mean 1.85 below `L = 40`
rising only to 5.00 for `L ∈ [160, 200]`, the Erdős–Kac `log log G` rate.  And `G`
is **outright prime** at `(L, a) = (89,56), (97,61), (110,69), (116,73),
(121,76)`.  So a cycle-plausible gap need not have many prime factors at all, and
no elementary lower bound on `ω(2^L − 3^a)` can exist — any such bound would deny
those five.

**And a genuine cycle settles it.**  The `3x+5` cycles of length 27 have
`(L, a) = (27, 17)` and `G = 2^27 − 3^17 = 5 077 565 = 5 · 71 · 14303`, `ω = 3`.
For *both* of them, the `d`-free accumulator satisfies **two of the three prime
conditions exactly**:

| minimum | `C(w,1)` | mod 5 | mod 71 | mod 14303 |
|---|---|---|---|---|
| 187 | 189 900 931 | 1 | **0** | **0** |
| 347 | 352 383 011 | 1 | **0** | **0** |

Independently verified.  `71 · 14303 = 1 015 513` divides `C(w,1)` in both cases;
the only failing condition is `p = 5`, which is exactly `gcd(d, G) = 5` — the
`d = 5` rescue.  If "several prime conditions cannot all hold" had content, it
would fail right here.  It does not.

The scan behind this was large and negative: the 358 survivors below 40000 plus
`a = 79335, 190537`, against every prime `5 ≤ p < 2·10⁶`.  Mean 2.653 small prime
factors per gap against 2.8787 predicted by the exact lattice model — statistically
ordinary.  **34 survivors have no prime factor below `2·10⁶` at all.**  And for
`a = 2966`, 400 admissible heavy words hit every residue mod every `p ≤ 23`,
including 0, at exactly rate `1/p`.  The shape "some small `p ∣ G` has `C ≡ 0
(mod p)` incompatible with heaviness" **does not exist** at any `p < 2·10⁶` for any
of the 360 surviving `a`.

What survives is a clean classifier rather than an obstruction.  The set
`{(L,a) : p ∣ 2^L − 3^a}` is a sublattice of `Z²` of index exactly
`M_p = lcm(ord_p 2, ord_p 3)`, giving density `1/M_p` — and for the first three
primes this is decidable from `(L, a)` alone:

* `GapPrimes.five_dvd_gap_iff` : `5 ∣ 2^L − 3^a ↔ (L + a) % 4 = 0`
* `GapPrimes.seven_dvd_gap_iff` : `7 ∣ 2^L − 3^a ↔ (a + 4L) % 6 = 0`
* `GapPrimes.thirteen_dvd_gap_iff` : `13 ∣ 2^L − 3^a ↔ (L + 8a) % 12 = 0`

checked against brute force over all `L < 400` with zero violations, and against
the wild scan with exact agreement (5 divides `G` for 88 of 360 survivors against
a predicted `1/4`; 7 for 58 against `1/6`; 13 for 28 against `1/12`).  Composed
with `cycle_length_determined` these become conditions on `a` alone.

Also proved: every nontrivial divisor of a gap is `≥ 5` (`gap_divisor_ge_five`),
and the divisor set is closed under exponent addition (`gap_add_dvd`,
`gap_dvd_scale`).  The latter is worth its own note — since `L = fexp(a)+1` is not
additive, the scaled pairs `(kL, ka)` are never themselves survivors for `k ≥ 2`,
so non-primitive cycles carry no new information.  Together with the rotation
result this says the divisibility is invariant under both symmetries of the
problem, and neither yields an extra constraint.

**>>> CORRECTED in Round V — the sentence above is FALSE. <<<**  Writing
`δ_a = L − a log₂ 3 ∈ (0,1)`, one has `δ_(ka) = k·δ_a`, so the scaled pair
`(kL, ka)` stays on the ledge for **every** `k` with `k·δ_a < 1`, and ledge
survivors have `δ_a ≈ 10⁻³`.  Measured: over every ledge point with `a < 200 000`,
dividing `(L, a)` by any common divisor lands back on the ledge — zero exceptions
— and 137 of the 357 sandwich survivors below 40 000 have `gcd(L, a) > 1`.  At the
frontier, `(9402, 5932) = 2·(4701, 2966)`, `(14103, 8898) = 3·(4701, 2966)` and
`(23505, 14830) = 5·(4701, 2966)` are all ledge points and all survivors.  See
`PrimeLedge.ledge_descend`.

The honest quantitative summary of the whole direction: at `(L, a)` the words
number `2^(0.95 L)` and the constraint has strength `1/G`, so with
`δ = L − log₂ G` the expected solution count is `2^(δ − 0.05L)`, and `δ` was
measured in `[1.00, 6.74]` over all 136 near-critical pairs with `L ≤ 200`.  The
constraint beats the freedom by 0.05 bits per step — but closing the sum over `L`
needs an effective bound `δ ≤ o(L)`, i.e. an effective irrationality measure for
`log₂ 3`.  That is exactly the Baker-type input this development forbids, and
"expected count → 0" is not "count = 0".

## The frontier moved twice: 4701 -> 6809

The one lever that still pays was priced exactly by the gap sandwich and then
paid.  The verified range went from **768 000 to 1 086 464** (1061 blocks of
1024), and the cycle frontier crossed *two* risers at once:

`RealizableFrontier6809.length_ge_6809` — no nontrivial accelerated cycle has
length below **6809**.

Two rungs came for one sweep because 768 000 was sitting only 3 477 short of the
first riser.  The `G`-records, independently recomputed, are spaced by exactly 665 — which *is*
a convergent denominator of `log₂ 3`, unlike the survivor gaps above:

| record index `i` | `G(i)` | `fexp i` | frontier `L` |
|---|---|---|---|
| 971 | 238 670 | 1538 | 1539 |
| 1636 | 420 842 | 2592 | 2593 |
| 2301 | 620 858 | 3646 | 3647 |
| 2966 | 841 477 | 4700 | 4701 |
| 3631 | 1 086 055 | 5754 | 5755 |
| **4296** | **1 358 718** | **6808** | **6809** |

Verified independently: `max_{i<4296} G(i) = 1 086 054 < 1 086 464 = c` (margin
exactly **410**), and `G(4296) = 1 358 717 > c`, so the certificate genuinely stops at
4296 and

*Convention note, added after an audit.*  This column mixes floor and ceiling: rows
`971, 2301, 2966` print `⌊G⌋` while rows `1636, 3631, 4296` print `⌊G⌋ + 1`.  Under the
floor convention used at `RESEARCH.md:1354` the maximum is `1 086 054`, and `1 086 055`
is the least admissible `c`, not the maximum; likewise `VerifiedExtended.lean:24` has
`G(4296) = 1 358 717` correctly.  No theorem statement is affected — the numerals in
`cert_4296` and `cert_1086464` are unaffected — but the table should be read as
floors.
`fexp(4296) = 6808`.  Axiom footprint `[propext, Classical.choice, Quot.sound]`.

The machinery is reused verbatim — sieve modulus `2^10`, 64 survivor residues,
`Sieved.reachesOne_of_blocks`, fuel 200 — and the added build cost is 140 s wall,
against 274 s for the existing sweep.

**The stopping point was forced, and the reason is worth recording.**  Fuel 200
covers every survivor through block 1060.  The first block needing more is
`m = 1099` (`n = 1 126 015`, requiring 224 accelerated steps), so 1100 blocks
would have broken the uniform-fuel aggregation and required a `dropsWithin`
fuel-monotonicity lemma.  Stopping at 1061 keeps the structure intact.  The next
rung — range 1 358 718, frontier `L ≥ 7863` — needs 267 more blocks (~190 s), that
monotonicity lemma, and a `cert 4961` at ~2370-digit numerals.  Affordable, no
longer free.

This is the staircase `Bootstrap` priced: each rung costs a fresh sweep and
multiplies the range by about 1.1.  It is not a bootstrap, and by
`ArchimedeanCeiling.sandwich_vacuous` it cannot pass `a = 3N` however far it is
pushed.

## The last surviving hypothesis class is now closed too

The paragraph below this one, as first written, named the joint rank
`Φ(x) = f(x mod m, ⌊log₂ x⌋)` as "the unique survivor of eleven independent
attacks and untouched by every impossibility theorem in the development."  It is
now touched.

> **`JointRank.no_joint_class_ranking`** — for every modulus `m ≥ 1`, every window
> `L ≥ 2`, every threshold `B`, and every `Φ` constant on pairs
> `(x mod m, ⌊log₂ x⌋)`, there is no `x > B` with `Φ(T^L x) < Φ(x)` for all such
> `x`.  `no_joint_ranking_wf` gives the same for **any well-founded codomain**,
> ordinals included.

Two things about how it was proved are worth keeping, because both correct
guesses recorded here.

**The collapse I conjectured does not happen.**  The guess was that since the
residue mod `2^L` determines the drift (Terras), taking `m = 2^L` would make the
archimedean coordinate a function of the residue and reduce the joint rank to a
pure congruence rank, already closed.  It does not.  The residue pins the *ratio*
`T^L(x)/x`, but `⌊log₂⌋` of a pinned ratio still depends on the **mantissa** of
`x`, which the residue does not see.  Measured over 200 000 consecutive `x` near
`2^20`: at `L = 8`, `m = 2^8`, 112 of the 256 residue classes carry **two**
distinct drift values, spread exactly 1.  So the joint class is strictly larger
than the closed congruence class, and these theorems are not corollaries of
`AnyModulusRanking`.

**Cycle detection is the wrong test, and the old witness does not work.**  The
`AnyModulusRanking` witness `n = 2^L·m − 1` fails here: `T^L(n) = 3^L·m − 1` and
`3^L ≥ 2^(L+1)` for `L ≥ 2`, so `⌊log₂⌋` *strictly increases* and no descent is
contradicted.  (At `L = 1` it does work — `m = 5`, `n = 9`, `T(9) = 14`, same
residue and same bucket — which is why the theorems carry `L ≥ 2`.)  Nor is the
realized `(residue, bucket)` graph the right object: it is **infinite**, so
acyclicity would not give a ranking, and it does contain cycles anyway.

The killing object is an **infinite strictly-ascending path at constant residue
with prescribed bucket**.  For target bucket `H`, put `P = 2^(H−L)`,
`M = m·(⌊P/m⌋ + 1)`, `wit = 2^L·M − 1`.  Then `P < M ≤ 2P` gives
`⌊log₂ wit⌋ = H` exactly, `wit ≡ T^L(wit) ≡ −1 (mod m)`, and
`T^L(wit) + 1 = 3^L·M ≥ 2^(H+1)` so the bucket strictly rises.  Descent then gives
`g(H') < g(H)` with `H' > H` for every `H ≥ L + m + B` — an infinite descent in a
well-founded codomain.  Independently verified on 11 264 witnesses
(`m ≤ 64`, `2 ≤ L ≤ 12`, 16 buckets each), zero failures, with `T^L` recomputed
from the map each time.

A sharp structural distinction falls out.  `AnyModulusRanking.no_ranking_general`
needed only *irreflexivity*, because its witness forced an **equality** of ranks.
Here the witness forces a strict decrease along an ascending chain, so
**well-foundedness is exactly what is consumed** — which is what "ranking
function" means, so nothing is lost.  A non-well-founded codomain genuinely
escapes, and is not a ranking function.

What is left free, stated precisely: a rank reading a *finer* archimedean datum
than the bucket (at the limit, `x` itself, where a rank trivially exists — so this
is the real boundary); a rank decreasing only *along* a counterexample orbit
rather than globally, the same caveat that applies to
`ExchangeRate.no_valuation_size_ranking`; and variable windows together with the
bucket simultaneously, which `joint_step` should transport to but which was not
proved.

## What is actually left

Every mechanism this round examined closed.  Setting them side by side, the
closures have a shape:

| route | status after this round |
|---|---|
| archimedean (verified range + size ceiling) | capped at `a < 3N`, achieves `≈√N` |
| order / S-unit, any number of runs | **closed** — the sharp bound is attained by a genuine `3x−1` cycle |
| counting / exponential sums | **closed** — unconditional L¹ barrier |
| congruence at any odd modulus | **closed** — word and modulus provably independent |
| ranking, any finite quotient or well-order | **closed** (earlier rounds), plus variable windows and finite heaviness filters |
| word surgery, compression, minimality descent | **closed** — no single-step edit survives |
| rotation / cyclic symmetry | **closed** — the simultaneous condition equals the single one |
| forbidden blocks or runs | **closed** — none exist; the factor set is everything |

And `NewModels.word_is_cycle_word` explains *why* they all close together: **every
word with a positive gap is a cycle word of `3x + δ(w)`**, so no property of the
parity word can obstruct a cycle.  Everything in the table above is a word-level
property.  They were never going to work, and now that is a theorem rather than a
pattern.

Add to that table one more row, closed after it was first written:

| ranking on residue **together with** `⌊log₂ x⌋` | **closed** — `JointRank`, by an ascending path, not a collapse |

So the remaining target is not a lemma about words, and it is not a ranking
function of any shape the development has been able to pose.  It is:

> **Bound `δ(w) = (2^L − 3^a) / gcd(affineC(w), 2^L − 3^a)` away from 1, using
> data that is not a function of the word alone.**

That is the honest end state, and it should be read with its context rather than
as an invitation.  The two levers available are the archimedean one, which bounds
`x_w = C/G` from above and is capped by `sandwich_vacuous`, and the arithmetic
one, the order of 2 modulo the gap, which `SUnitRelation` closed.  And they are
**not independent**: the attempt to refute range-plus-word arguments failed
precisely because `δ = n/x_w`, so a large `n` at small `δ` demands a large `x_w`,
which is the realizability ceiling again.  *The two levers are the same lever.*

This round therefore ends differently from the last two.  Round II ended naming a
frontier — the two-run S-unit collapse — and this round closed it.  Round III ends
naming **no viable mechanism at all**.  Every route it examined is either closed
by proof or capped by a proved ceiling, and the one hypothesis class that survived
eleven attacks was closed by the twelfth.  What remains is a sharply stated target
with an empty list of known-viable approaches to it.

That is not a claim that the problem is hopeless, and it is not a claim that the
list of approaches is exhaustive — it is the list this development has tried.  It
is a claim about where the next generation must look: **not at the parity word,
because that is now provably impotent; not at a ranking function, because every
form is closed; and not at size, because the ceiling is proved.**  The one object
that no theorem here constrains is `gcd(affineC(w), 2^L − 3^a)` itself, and
nothing in fifteen agents' work says anything about it beyond that it is what the
problem reduces to.


---

# Round IV — the filter was wrong, and one real non-archimedean descent

Five agents, and a correction to this file that reopens territory it had closed.

## The correction: word-level mechanisms are NOT dead

Round III concluded from `NewModels.word_is_cycle_word` that *"no property of the
parity word can obstruct a cycle"*, and Round IV's whole strategy was built on it.
**It is false.**

`δ(w) = G/gcd(C, G)` is itself a function of the word.  So `δ(w) = 1` is a
word-only property, and it is *exactly* the obstruction — indeed the no-cycle half
of Collatz **is** a statement about parity words (`for every heavy word of length
L with a odd letters, G(w) ∤ C(w)`), so any proof of it is necessarily a word-only
mechanism.  This file contradicted itself about it five lines apart, at the
"localised onto `gcd(affineC L r, 2^L − 3^a)`" sentence.

Verified directly: for the `3x+5` cycles of length 27 (minima 187 and 347), `δ(w)`
computed **from the word alone** equals 5.  The word separates `d = 1` from
`d = 5` perfectly.

**The corrected filter.**  Dead is word-only *and invariant under `C ↦ d·C`* —
heaviness, density, factor complexity, block structure, `ω(G)`, `ord₂` mod `G`,
magnitude bounds on `C`.  Live is anything comparing `C(w)` to `G(w)`
**multiplicatively**: `gcd`, `v_p(C)` against `v_p(G)`, `C mod G`.  And the filter
is quantitatively far weaker than advertised: 87.5 % of words (`L ≤ 12`) have
`gcd(C,G) = 1`, hence `δ(w) = G ≈ 2^L`, so any argument using a bound `d < 2^k`
for `k ≪ L` is untouched.  Only arguments *uniform in `d` over the full range* are
forbidden.

## A non-archimedean descent that is real, and where it stops

`RepetitionDescent.subst_yields_cycle` (LEAN_PROVED).  Substituting one factor `p`
of a cycle word by another factor `q` of the same length and the same odd count,
with `wC q < wC p`, produces a **strictly smaller cycle point** — while leaving
`L`, `a`, the gap `G`, `v₂`, `v₃` and every orbit magnitude fixed.  The descending
measure is the accumulator itself.  That is the answer to "find a descent whose
measure is not integer magnitude", and it is the first one this development has.

The bridge that made it possible was missing until now:
`RepetitionDescent.wC_parityVector : wC (parityVector r L) = affineC L r`, with the
free-monoid law `wC (u ++ v) = 3^(ones v) · wC u + 2^|u| · wC v`.  Word-level
statements now transfer to the cycle criterion mechanically.

**Where it stops, measured exactly.**  The descent halts at the minimum of
`S(L,a,G) = {w : |w| = L, ones w = a, G ∣ wC w}`, and that set is a union of
rotation classes of genuine cycles.  Independently verified:

* `S(11, 7, 139)` has **exactly 11** elements, and their `C/G` values are
  `{17, 25, 34, 37, 41, 55, 61, 68, 82, 91, 136}` — precisely the eleven elements
  of the `3x−1` cycle through 17.  Nothing outside the rotation class.
* `S(19, 12, 7153)` is **empty** (all 50 388 words checked).
* `S(27, 17, 1 015 513)` has 54 elements — the two rotation classes of the two
  `3x+5` 27-cycles, and nothing else.  Note that **two distinct cycles share one
  `(L, a)` and one gap**, so even uniqueness of the minimal configuration fails.

So the failure is *termination, not soundness*: reaching a contradiction requires
`S = ∅`, which is the original problem verbatim.  The named open input is a bound
on a cycle's **spread** `M/n`: a substitution partner is forced iff
`log₂(M/n) > 0.1025 L − 2.05 δ`, giving `M/n > 2^474` at `(4701, 2966)` and
`2^690` at `(6809, 4296)`.  The crude `M/n ≤ (3/2)^L = 2^(0.585 L)` does not decide
it.

Also killed here, with theorems rather than assertions: Architecture C (a repeated
*state* is not a repeated *value* — `state_repeat_not_value` exhibits `2^k·M`
returning to its class at the different value `M`; and the expanding branch is
realised at every odd orbit point, so the dichotomy is not separately excludable);
the ledge edit as a uniform rule (`fexp(a+j) − fexp(a)` takes **both** values for
every ledge step `j ∈ {5,12,17,29,41,53}`, over `a < 20000`); and any modulus other
than `G` (substituting at `M ≠ G` destroys `G ∣ C`).

## The run-refined accumulator bound

`heavy_accumulator_bound_sharp` proves `3C ≤ a·3^a` one odd step at a time, and its
induction is exactly tight at every step — so no per-step argument improves it.
The missing information is **adjacency**: if the step before an odd step was also
odd then `a_j = a_(j−1) + 1`, and heaviness one step earlier gives
`2^j = 2·2^(j−1) ≤ 2·3^(a_j − 1)`, a factor `3/2` stronger than heaviness at `j`.
Counting those occurrences as `pairCount p`:

`RunRefined.accumulator_pair_bound : 9·C + p·3^a ≤ 3·(a·3^a)`

— the stored bound exactly when `p = 0`, strictly sharper otherwise.  With the
combinatorial lemma `pair_bound` (`2a ≤ p + j + 1`, since odd runs are separated by
even steps) this closes to

`RunRefined.accumulator_closed_bound : 9·C ≤ (a + j + 1)·3^a`,

i.e. `C ≤ 0.2873·a·3^a` against the stored `0.3333` — a 14 % improvement carrying
**no certificate**.  Measured exactly tight (worst ratio 1.0000) over all 59 058
heavy words of length ≤ 20.  The extremal words are not what the per-step bound
suggests: they have odd runs of length **two**, e.g. `[2,2,2,1,2,2,1]` at `L = 20`.

It does **not** beat `RealizableBound.Bcap` (`0.2404`), which was confirmed here to
be *exactly attained* — `max C = Bcap a` on the nose for every `a ≤ 12`.  So it
does not move the frontier; its value is a different mechanism at zero certificate
cost.

## Branches closed

* **3-adic / simultaneous p-adic.**  Dead by a trivial Hasse principle: the cycle
  criterion is *one linear equation in one unknown*, so solvability in every `Z_p`
  is definitionally `G ∣ C`.  There is no room for a joint local obstruction.  At
  `p = 3` it is worse than redundant — `v₃(G) = 0` always, so the 3-adic closure
  has a unique solution for **every** exponent vector
  (`PAdicJoint.cycle_three_adic_vacuous`).  The by-product is the real result:
  `word_free_dyadic` pins the word-preserving witness to a *prescribed dyadic
  block*, so no obstruction may use `⌊log₂ x⌋` either — closing Round III's last
  opening by a second route, in a stronger form than `JointRank`.
* **Reverse tree.**  A relabeling: `ReverseTree.reverse_eq_forward` proves the
  backward and forward relations are literally the same equation.  Its one
  genuinely `d`-dependent feature — the branch condition `2y ≡ d (mod 3)` — depends
  on `d` only through `d mod 3`, and `3x+7` (with `7 ≡ 1`) has the cycle
  `5 → 11 → 20 → 10 → 5`; `branching_cannot_decide` is the kernel-checked obituary.
  Genuinely new and kept: `odd_pred_exists_iff` (the exact branch criterion) and
  `reverse_determined` (the dual of Terras — a word plus an endpoint names one
  integer).  Also corrected: "branch points = odd steps" is **false**; the true
  count is `B = a + Σ⌊r_i/2⌋`, and the two `3x+5` 27-cycles have branch counts 20
  and 19 despite sharing `(L,a)`.
* **Infinite words.**  The argument "an integer is rational, so its parity word is
  eventually periodic" is a **trap**, and now a documented one.  It conflates the
  *binary expansion* coordinate with the *parity-vector* coordinate, which `Φ`
  exchanges.  What it assumes is exactly the Bernstein–Lagarias **Periodicity
  Conjecture** `Φ(Q ∩ Z₂) = Q ∩ Z₂` — only the useless inclusion `⊆` is known, and
  BL prove the conjecture equivalent to no-divergence for *all* `3x+k`,
  `k ≡ ±1 (mod 6)`.  `InfiniteWord.periodicity_equiv_no_divergence` proves the
  circularity in Lean.  New and kept: **every heavy word of length ≥ 4 contains the
  block `11`** (`not_noAdjOdd_of_heavy`) — a *required* block, complementing Round
  III's "no forbidden blocks", and exactly the `p ≥ 1` that `RunRefined` needs.

## Corrections from the adversary

* The `(a−1)` summand of the `CycleLanguage` split **vanishes** at both pairs used
  (`2^4700 > 3^2965`), so the docstring's "both terms nonzero" was false.  The
  theorems are *not* vacuous — the surviving term's logarithm is `4447.16881`
  against `log₂(binom(4701,2966)/4701) = 4447.16881`, agreeing to twelve figures —
  but the content is "every cycle word at these pairs ends in an even step", which
  is not what was claimed.
* `check_integrity.sh` had a **fail-closed** bug (an axiom-free theorem prints
  `does not depend on any axioms`, which failed the gate) and a **fail-open** hole
  (`set_option debug.skipKernelTC` was unblocked, which would disable kernel
  typechecking entirely).  Both fixed, along with modifier prefixes
  (`private unsafe def`), and `word_is_cycle_word` added to the gate.
* `JointRank`'s `L = 1` case is **not** closed in general — the file supports it
  with a single instance (`m = 5`, `9 ↦ 14`).  The adversary supplied a general
  witness, `wit1 m H = 2m(2^H/(2m) + 1) − 1`, verified for all `m ≤ 79`.  Recorded
  as an open repair.
* And a genuine impossibility: the **variable-window** joint rank cannot be closed
  at all.  With `m = 1`, `φ = ⌊log₂⌋`, "for every `x` there is `L` with
  `⌊log₂ T^L x⌋ < ⌊log₂ x⌋`" is *equivalent* to Collatz.  That target should be
  removed from the list rather than attacked.
* `word_is_cycle_word` admits the degenerate `a = 0` instance, where `n = 0`; and
  "of period `L`" should read "with `L` as a period", since primitivity is never
  proved.

## Where Round IV leaves it

The single open input is now sharper than "bound the gcd".  It is:

> **Bound a cycle's spread `M/n`.**  If `log₂(M/n) < 0.1025 L − 2.05 δ`, no
> substitution partner is forced and `subst_yields_cycle` cannot start; if it
> exceeds that, the descent runs — and still bottoms out at `S(L,a,G)`, whose
> emptiness is the theorem itself.

That is an honest statement of a mechanism that is *correct and formalised* but
non-terminating, together with the exact quantity that would decide whether it can
even begin.

---

# Round V — the prime direction, closed with measurements

One question: **does anything survive in the prime direction?**  Round III
refuted the many-primes thesis three ways; Round IV killed the `p`-adic route by
a trivial Hasse principle.  Three angles were left explicitly open.  All three
turn out to be **real** — each contains a true, previously unrecorded structural
fact — and all three deliver information about `G` alone, which by CRT is worth
exactly nothing against `G ∣ C`.  New file: `Collatz/Strategy/PrimeLedge.lean`
(11 theorems, axiom footprint `[propext, Quot.sound]`, no `Classical.choice`).

## Admission test

The prime direction *does* see something the density / affine-magnitude
framework cannot: `v_p(C)` against `v_p(G)` is a multiplicative comparison of `C`
to `G`, it is not a function of magnitudes, and it is not invariant under
`C ↦ d·C` (`v_p(d·C) = v_p(d) + v_p(C)`).  So it passes the corrected soundness
filter and the branch was admitted.  What it then turns out to be, once measured,
is the CRT collapse in valuation clothing — which is a *result*, not a filter
failure.

## 1.  The ledge is closed under common divisors — and the ledger was wrong

`PrimeLedge.ledge_descend` (LEAN_PROVED).  Define
`Ledge L a := 2^L ≤ 2·3^a ∧ 3^a < 2^L`, which `ledge_iff` proves equivalent to
`L = fexp a + 1`.  Then for every `g ≥ 1`,

> `Ledge (g·L') (g·a')  →  Ledge L' a'`

by pure `Nat` monotonicity of `x ↦ x^g` in both halves — no real analysis.  With
`GapPrimes.gap_dvd_scale` this gives `ledge_gap_dvd`: at a ledge point whose
exponents share a factor `g`, the gap of the primitive point `(L/g, a/g)` — which
is itself a ledge point — divides the gap; and `ledge_cycle_gap_dvd` carries that
into the cycle criterion.

This **falsifies** the Round III sentence "the scaled pairs `(kL, ka)` are never
themselves survivors for `k ≥ 2`" (corrected in place above).  The smallest
kernel-checked witness is `Ledge 16 10 → Ledge 8 5`, with
`2^8 − 3^5 = 13 ∣ 6487 = 2^16 − 3^10` (`gap_13_dvd_6487`).

Consequence for Zsigmondy, which Round III found vacuous because it looked at the
one-run branch where `g = 1`: on the *ledge* `g > 1` is common (137 of 357
survivors below 40 000), Zsigmondy's hypotheses hold (`gcd(2^(L/g), 3^(a/g)) = 1`;
the `g = 2` exception needs `X + Y` a power of two and `2^(L/2) + 3^(a/2)` is
odd), so `G` has a primitive prime divisor `p ≡ 1 (mod g)`, and running over the
divisors of `g` gives `ω(G) ≥ d(g) − 1`.  **Non-vacuous and useless**: Round III
proved that any lower bound on `ω(G)` is worth nothing, because by CRT the `ω(G)`
conditions *are* `G ∣ C`.

## 2.  `v_p(C)` is not structurally bounded.  REFUTED, with the law

The route needs `v_p(G)` forced large while `v_p(C)` is capped.  Both halves fail
and both distributions are exactly geometric with ratio `1/p`.

*`v_p(G)` on the ledge*, exhaustive over `1 ≤ a ≤ 20 000` with exact integer gaps:

| `p` | `v_p = 1` | `2` | `3` | `4` | `5` | max |
|---|---|---|---|---|---|---|
| 5 | 4001 | 799 | 162 | 32 | 8 | **5** at `a = 351` |
| 7 | 2846 | 407 | 63 | 9 | 1 | **5** at `a = 4606` |
| 11 | 1819 | 163 | 15 | 1 | 0 | **4** at `a = 3428` |
| 13 | 1546 | 116 | 8 | 1 | 0 | **4** at `a = 7548` |

So `max_{a ≤ X} v_p(G)` grows like `log X / log p`.  (The brief's `5^4 ∣ G` at
`a = 31708` and `5^3` at `a = 20203` are ordinary members of this distribution.)

*`v_p(C)` on heavy words*, exhaustive over the cycle language:

| `L` | words | `v₅(C) = 0,1,2,3,4,5,6` | geometric prediction |
|---|---|---|---|
| 20 | 29 980 | 23983, 4798, 957, 189, 43, 8, 2 | 23984, 4797, 959, 192, 38, 8, 2 |
| 22 | 93 222 | 74626, 14878, 2977, 588, 117, 29, 7 | 74578, 14916, 2983, 597, 119, 24, 5 |

and the same agreement at `p = 7, 11, 13`.  **No cap, no cutoff, no tail
structure.**  Quantitatively at `(L, a) = (4701, 2966)`: `2^4447` words, `v₅(G) ≤ 5`
in the measured range, fraction with `v₅(C) ≥ 5` equal to `5^(−5) = 2^(−11.6)`,
leaving `2^4435` survivors of the `p = 5` condition.  Pushing to the absolute cap
`p^(v_p(G)) ≤ G` (`gap_prime_power_le`) recovers the fraction `1/G` — i.e.
exactly `G ∣ C` and not one bit more.  **The valuation route is CRT again.**

## 3.  The ledge and the prime lattices *do* interact non-randomly — exactly

Over all ledge points with `a < 40 000`, the frequency of `p ∣ G` matches
`1 / lcm(ord_p 2, ord_p 3)` to four decimals for every `p < 200`.  The **survivor
set** is different, and the deviation is not noise.

Every one of the **8847** sandwich survivors below `a = 200 000` (criterion
`c·G ≤ 0.2404·a·3^a` at `c = 768 000`, which reproduces Round III's 357 below
40 000 and 807 below 60 000) is **exactly**

`(L, a) = k·(485, 306) + j·(1054, 665)`,  `k ∈ [1, 70]`,  `j ∈ [4, 294]`

with **zero exceptions**.  Divisibility of `G` by `p` is then a condition on
`(k, j)` modulo `(u_p, v_p)`, the multiplicative orders of `2^485/3^306` and
`2^1054/3^665` mod `p`.  Since the survivor profile is skewed (`k` small, `j`
large), primes with `v_p` small and `u_p` large are systematically **rare**.
Screening every `p < 300` against 8847 survivors gives exactly three outliers at
`|z| > 2.5`, and all three are this mechanism:

| `p` | `u_p` | `v_p` | observed | naive `n/M_p` | `z` |
|---|---|---|---|---|---|
| **37** | 36 | **1** | **150** | 245.75 | **−6.11** |
| 173 | large | large | 29 | 51.44 | −3.13 |
| 251 | 250 | **5** | 18 | 35.39 | −2.92 |

`p = 37` is exact to the unit: `37 ∣ 3^665 − 2^1054`, so `v₃₇ = 1` and `j` is
irrelevant; `u₃₇ = 36`, so `37 ∣ G` iff `36 ∣ k`, iff `k = 36` in range — and the
number of survivors with `36 ∣ k` is **150**, matching the observed count of
`37 ∣ G` exactly.

The theorem behind it is new: `PrimeLedge.gap_translate_iff` and its
negative-gap companion `gap_translate_iff_neg`, with iterated forms.  If `m`
divides the gap of a "null" pair `(K, b)` and `2` is invertible mod `m` (explicit
inverse `(m+1)/2` for odd `m`, `two_inv_of_odd`), then

> `m ∣ 2^(L+K) − 3^(a+b)  ↔  m ∣ 2^L − 3^a`.

`GapPrimes.gap_add_dvd` had only `→`; the converse is what makes the divisibility
a function of one lattice coordinate.  Kernel-checked instances:
`929 ∣ 2^485 − 3^306` (`nine_two_nine_k_blind`) and `37 ∣ 3^665 − 2^1054`
(`thirtyseven_j_blind`).  Note the sign — the second generator's own gap is
**negative**, `2^1054 < 3^665`, which is exactly the `δ_a = k·δ₃₀₆ − j·ε`
decomposition `GapSandwich` records, and is why the two companions are needed.

**And it is still not an obstruction.**  It classifies *which* primes divide `G`.
Round III measured `C mod p` over heavy words at `a = 2966` for every `p ≤ 23`
and found every residue, `0` included, at rate `1/p`; the shape "some small
`p ∣ G` forces `p ∣ C` incompatibly with heaviness" does not exist for any
`p < 2·10⁶` at any of 360 surviving `a`.  Non-random *selection of the primes*
composed with equidistributed *`C` mod each prime* is still strength `1/G`.

## Verdict

**Nothing survives in the prime direction.**  Every angle left open by Rounds III
and IV is real and none of them obstructs, for one reason stated three times: all
of them are information about the factorisation of `G`, and by CRT the
factorisation of `G` carries no information about `G ∣ C`.  The soundness filter
admitted the branch correctly — `v_p(C)` vs `v_p(G)` genuinely is a multiplicative
comparison — and the branch then died to measurement rather than to the filter.

The program should stop spending rounds on primes.  What is left is unchanged
from Round IV: bound `δ(w) = G/gcd(C, G)` away from 1, or bound a cycle's spread
`M/n`.  Neither is a statement about which primes divide anything.


---

# Round V — the substitution route is closed, and the sink was never a bad measure

Five agents.  The round set out to bound the cycle spread `M/n`; that target was
wrong in both directions, and the correct statement is stronger.

## The criterion had a spurious term

Round IV's substitution criterion `log₂(M/n) > 0.1025·L − 2.05·δ` is invalid.  A
partner must satisfy `RepetitionDescent.subst_dvd`'s hypothesis `ones q = ones p`,
which is forced, not decorative: changing the odd count changes `a`, hence `G`, so
the divisibility would be by the **wrong gap**.  The pool is therefore words of
fixed length *and* fixed odd count — size `binom L a`, independent of the spread.
The `M/n` factor came from letting `a` range over a band, which the hypothesis
forbids.

> **A partner is forced iff `binom L a > G`.**

On the ledge this holds at exactly six pairs — `a ∈ {1, 3, 5, 10, 17, 29}` — and
never for `a ≥ 30`.  The deficit then grows linearly at `(1 − H(log₃2))·L ≈ 0.05 L`
bits: `+0.73` at `a = 17`, `+0.01` at `a = 29`, `−3.37` at 30, **`−231.4`** at 2966,
**`−337.0`** at 4296.  It cannot be forced asymptotically either, since `δ > 0.05L`
would need `ε < 2^(−0.05L+0.53)` against `ε ≫ a^(−4.2)` from the irrationality
measure of `log₂3`.  This is `CycleLanguage`'s 243-bit surplus, reached from the
substitution side.

## The spread computation, restated correctly

An exact DP over words heavy at every proper prefix gives minimum spread `1.5098`
at `L = 27` rising to `1.5837` at `L = 4701` — converging to `log₂3`, a constant.
The minimiser is the greedy Sturmian word `a_i = ⌈i·log₃2⌉`, so this is a **closed
form**, `minspread(L) = max_(i<L)(⌈i log₃2⌉ log₂3 − i) < log₂3`, uniform in `L`.

That is a *minimum*, and I originally used it to conclude "substitution is never
forced".  **That inference is invalid** — the conclusion needs a bound on the
*maximum*.  There is none: `1^a 0^(L−a)` is heavy at every proper prefix at
`(4701, 2966)` with spread `1735`.  Heaviness confines the spread only to
`[≈1.58, ≈0.585a]` and pins neither end.

What it does prove, with `NewModels.word_is_cycle_word`:

> **No `d`-free mechanism can lower-bound a cycle's spread.**  The Sturmian word at
> `(4701, 2966)` is a genuine cycle of `3x + δ(w)` — `δ` 1413 digits, minimum 1418
> digits — with spread **exactly 2.99930**.

A spread bound must consume an asset; heaviness will not deliver one.

## The sink was never a bad measure — no second measure can exist

`SinkStructure.wC_inj`: on binary words, `(length, ones, wC)` is a **complete
invariant** (independently verified, zero collisions over all 524 286 words to
length 18; consistent with the length-83 refutation, which had different odd
counts).  So the fibres of `w ↦ wC` at fixed `(L,a)` are **singletons**, and:

* `lex_collapses` — for **any** `μ`, a strict lexicographic decrease of `(wC, μ)`
  across a shape-preserving operation is already a strict decrease of `wC`.  Runs,
  max run, run multiset, rotation index, `v₂` profile: all functions of the word,
  hence of `C`, hence redundant.
* `no_descent_on_list` — if `S` is finite, `T₂` maps `S` into `S`, and **any** `ν`
  strictly decreases along `T₂`, then `S = ∅`.  `ν` carries no hypotheses, so this
  covers every second operation and every measure at once.  `sink_rigid_17` is the
  witness: `S(11,7,139)` is the eleven rotations of the `3x−1` cycle, decided in the
  kernel, nonempty.  The same argument runs at `(27,17)` for the `3x+5` cycles.

Also established exhaustively (135 non-empty blocks, every length ≤ 28, three
worlds, zero exceptions): **every** element of `S` is a genuine cycle word, not
merely every sink.  Divisibility alone, not minimality, makes a cycle word.  So
Round IV's hoped-for equivalence is true-but-vacuous forward and false in reverse.

**Verdict: the descent architecture is complete.**  The sink is the statement that
`S(L,a,G)` is a nonempty finite set whenever a cycle exists, and no strictly
decreasing map exists on such a set.  Any contradiction needs `S(L,a,G) = ∅`, which
is the original problem verbatim.

## The extremal coincidence is a theorem

`ExtremalWord`.  Re-coordinatising heaviness by odd-step times gives

> **heaviness ⟺ `t_i ≤ fexp(i)` for every `i < a`** —

so the heavy words with `a` odd steps are exactly the integer points of a **box**,
whose unique top corner is the Beatty word.  `C` is strictly increasing in every
`t_i`, so it is maximised at the corner; the prefix odd-count profile is antitone,
so the spread is minimised at the *same* corner.  Two objectives monotone in
opposite directions along one partial order.

Consequences: `max C = Bcap a` is a **tautology**, not luck — "exactly attained for
`a ≤ 12`" needed no coincidence; the corner minimises *every* monotone functional of
the profile simultaneously; and equality in `C ≤ Bcap` holds **iff** the word is the
Beatty word (`Cw_eq_Bcap_iff`).  Agreement measured 15/15 on the ledge, both
extremisers unique.

The near-extremality mechanism is nevertheless **dead**, and instructively.  On a
cycle `C = G·m` with `m ≥ 1086464`, so the forced ratio `C/Bcap ≥ G·m/Bcap` — and
computing it just reproduces the frontier: the first `a` where it drops below 1 is
`a = 4296`, `L = 6809`, *exactly* `RealizableFrontier6809`.  So "the cycle word is
near-extremal" is a restatement of the frontier bound, available only where the
frontier already closes the case.  Past it the median forced ratio over surviving
`a ≤ 40000` is 0.494, minimum 0.0053.  Explicit witness: the `3x−1` cycle through 17
sits at 63 % of its ceiling.  Cycle words are not near-extremal.

Also computed: `gcd(Bcap a, G) = 1` for 88.2 % of `a ≤ 3000`, maximum 22139 at
`a = 2773` against a gap of `2^4397`.  **The Beatty word is never a cycle word.**

## `δ` collapses onto counting

`DeltaSpectrum`.  Exhaustive over the cycle language to `L = 40` (up to
820 236 724 words; growth rate `1.9318^L`): the Round III observation that heaviness
suppresses `gcd(C,G)` is **a sample-size artifact**.  Past `L = 20` the maximum gcd
explodes — 1 015 513 at `L = 27`, 1 320 539 363 at `L = 40` — and `min δ` does not
grow: 5 at `L = 27`, 13 at 24, 191 at 40.

Against the null model `C` uniform mod `G`: `P(gcd = 1)` matches `∏_{p|G}(1−1/p)` to
four decimals; `χ² = 182` on 27 dof, with the *entire* excess at `p = 5` and of
opposite sign at different lengths.  Measured growth `log₂ δ_min ≈ 0.050768·L +
13.22` against the theoretical `1 − H(log₃2) = 0.0500445`.  So `δ → ∞`
heuristically, but **the mechanism is pure counting and heaviness contributes zero
suppression** — `δ = 1` cannot be excluded this way.

`delta_no_growing_bound` (axiom-free): any length-indexed lower bound on `δ` over
heavy words is pinned at five lengths by non-increasing values, so `δ ≥ 6` is
formally false.

## Nothing survives in the prime direction

`PrimeLedge`.  All three remaining angles are real and none obstructs, for one
reason stated three times: each delivers information about the *factorisation* of
`G`, which by CRT carries none about `G ∣ C`.

* **Primitive divisors are live but useless** — and they correct this ledger.
  `ledge_descend` proves `Ledge (g·L') (g·a') → Ledge L' a'`, so the claim above
  that *"the scaled pairs `(kL, ka)` are never survivors for `k ≥ 2`"* is **false**:
  `δ_(ka) = k·δ_a`, and **137 of the 357** survivors below 40000 have `gcd(L,a) > 1`.
  Round III found Zsigmondy vacuous because it looked at the one-run branch where
  `g = 1`; on the ledge `g > 1` is common.  It yields `ω(G) ≥ d(g) − 1` — a lower
  bound on `ω(G)`, which Round III already proved buys nothing.
* **`v_p(C)` versus `v_p(G)`: refuted with the law.**  Both follow the same geometric
  distribution with ratio `1/p` and no cutoff.  `max v_p(G)` on the ledge grows like
  `log X/log p` (max 5 for `p = 5` over `a ≤ 20000`); `v_p(C)` over the cycle
  language matches the prediction to three figures.  At `(4701,2966)` the constraint
  removes 11.6 of 4447 bits.  Pushing to the cap recovers exactly `1/G` and not one
  bit more.
* **The ledge is non-random and it is exactly explained.**  Every one of the 8847
  survivors below `a = 200000` is `k·(485,306) + j·(1054,665)` with zero exceptions.
  Screening `p < 300` gives exactly three outliers beyond `|z| > 2.5`, all one
  mechanism: `37 ∣ 3^665 − 2^1054` makes `j` irrelevant, so `37 ∣ G` iff `36 ∣ k` —
  predicted 245.75, observed **150**, and the survivors with `36 ∣ k` number exactly
  150.  New: `gap_translate_iff`, the `↔` strengthening of `GapPrimes.gap_add_dvd`.
  A sign correction fell out: the second generator's gap is **negative**,
  `2^1054 < 3^665`.

## Corrections, including four to my own work

* **The Round IV substitution criterion is invalid** (spurious `M/n` term) — above.
* **My spread inference used the wrong extremum** — above.
* **`RunRefined` "exactly tight (worst ratio 1.0000)" is false.**  Ratio 1 is
  attained at exactly three words, all of length ≤ 3.  At every heavy length ≥ 4 the
  ratio is ≤ 0.958; at `L = 20` the maximum is 0.86840.  The asymptotic slack is
  13 %, so the true extremal constant is nearer 0.250 — closer to `Bcap`'s 0.2404
  than claimed.  The advertised extremal profile `[2,2,2,1,2,2,1]` at `L = 20` has
  35 of its 36 words non-heavy, and the one heavy word has ratio 0.857.
* **`RunRefined`'s headline measurement was against the wrong class** — the same
  empty-set error Round III found, now in my own file.  "12 448 heavy words with
  positive gap" used *proper*-prefix heaviness while the theorem hypothesised
  heaviness at every `i ≤ j`; under that hypothesis the positive-gap class is
  **empty**.  The correct count is 12 449.  **Repaired for free**: the induction
  never uses heaviness at `i = j`, so the hypothesis weakens to `i < j` — which is
  what makes the bound applicable to a cycle word at all.  Both theorems now carry
  the weaker hypothesis.
* **`heavy_accumulator_bound_sharp` has equality iff `a ≤ 1`**, and is off by a
  factor 1.386 forever (`sup 3C/(a·3^a) → 1/(2 ln 2)`).
* Docstring kills, Lean correct in each case: `PAdicJoint.cycle_three_adic_vacuous`
  quantifies `C` and `n` freely, so it is "a unit is surjective mod `3^j`" rather
  than a statement about the fixed point `n = C/G`; `ReverseTree` contains an
  `Iff.rfl` between character-identical sides, a theorem proving `2 = 2`, and a
  `d mod 3` claim that ignores preimage *values* (`(2y−d)/3` is 3 for `d=1` and 1 for
  `d=7` at `y=5`); `InfiniteWord`'s docstring says "never-dropping" where the Lean
  says *heavy* — `n = 1` never drops and its word `(10)^∞` contains no `11`.

## Where Round V leaves it

The substitution architecture is closed at **both** ends: it cannot be entered
(pigeonhole fails by `0.05·L` bits past `a = 29`) and it cannot be extended (no
second measure exists, since the fibres are singletons).  The word-only program is
now empirically exhausted as well: heaviness is *statistically invisible* to
`C mod G` — `P(gcd=1)` matches the Euler product to four decimals, and the only
detectable bias is 0.35 % at `p = 5` and changes sign.

Every route examined in Rounds III–V reduces to the same object: `C mod G`
equidistributes on the heavy language, and the counting surplus is `0.05·L` bits.
The honest remaining leverage is asset (a) — the verified range — applied to
something that is **not** a word invariant at all.


---

# Round VI — the surplus is 2-adic, and the gap is odd

Five agents.  The round proposed attacking with *state-dependent* quantities the
parity word does not determine.  The premise was half right, and the half that was
wrong was mine.

## What collapsed, and what I over-claimed

`WindowCollapse.window_sequence_realized`: for any two words `u`, `v` there is an
actual orbit whose first window is `u` and whose next is `v`.  For every **finite**
`N` the words of length `N` biject with residues mod `2^N`, so no finite family of
consecutive windows is stronger than one word of the total length.  **Finite
multi-window arguments are closed** — that operational conclusion stands.

I drew three further conclusions and all three are **false**, by compactness:

* *"The shrinking intersection is never empty; every prefix extends."*  True in `Z₂`;
  **false in `ℕ_{>0}`**.  Every prefix of `0^∞` is realised by `2^N`, every prefix of
  `1^∞` by `2^N − 1`, and no positive integer realises either infinite word.
* *"The growth rate of compatible window sequences equals the word entropy."*  Only
  at fixed finite length.  The infinite words realised by positive integers are
  **countable** — entropy 0 against 1 for the full shift.
* *"The only residual information is magnitude."*  False both ways.  For a cycle
  `n = C(w)/G(w)` is word-determined, so nothing is residual; for a general orbit the
  residual is not magnitude but **the letters after time `L`**.

That last error made my two directives jointly inconsistent — closing multi-window
arguments while requiring the next attack to be about `m`, which later letters
determine.  And the gap between the two models *is* the conjecture
(`InfiniteWord.periodicity_equiv_no_divergence`).

## The high part is identically zero

`HighPart`.  The only place non-word information could hide is `x = r + 2^L·m`.  The
law is `T^L(x) = 3^a·m + T^L(r)` — the offset is the orbit of the *smallest* member
of the class, manufactured from `(2^L, 3^a, C)` — so the coordinate is a
re-coordinatisation, not new information.  `renorm_faithful` and `renorm_compose`
make the renormalisation an isomorphism onto the same problem: the group is `Z`, the
cocycle is `3^(oddCount)`, and **the gap is the renormalisation eigenvalue**.  That
is why every word-level attack recurs verbatim at every scale.

And the coordinate is zero.  From `C ≤ 2^(L−a)(3^a − 2^a)`, every cycle element is
below `2^L` whenever `G·2^a > 3^a` — true for every `a ≤ 20000` except `a = 1`, with
a margin of **4285 bits** at the frontier pair.  The exception is the `3x+5` cycle
`5 → 10 → 5`.

## The surplus lives at the prime 2, and `G` is odd

`ImageDensity` — the round's sharpest result.

**The map is essentially injective mod `G`.**  Exhaustive to `L = 34`:
`image/N ≥ 0.98` everywhere and `= 1` in 15 of 20 shapes; collisions never exceed
the birthday prediction.  So there is **no structural compression** — the image is a
sparse `N`-element subset of `Z/G`, and the question is a covering question about a
sparse set, exactly what the L¹ barrier says size alone cannot settle.

**Where the surplus lives.**  The number of distinct values of `C mod 2^j` over the
cycle language is *exactly* the number of heavy prefixes of length `j`
(1, 1, 2, 3, 4, 8, 13, 19, 38, 64, 128, 226, …), so the image has density
`2^(−0.05j)` in `Z/2^j` — the same `0.05`, realised at the prime **2**.  And
`G = 2^L − 3^a` is **odd**.  So `2^j` is invertible mod `G`, every class mod `2^j`
already contains a multiple of `G`, and by CRT the entire surplus is worth
**exactly zero** against the target.  Proved: `two_power_vacuous`,
`mod_four_excludes_nothing`.  The mod-4 law is not an extra constraint — it *is*
heaviness at prefix 2.

**What `0.05` counts.**  `1 − H₂(log₃2) = 0.0500445` is the large-deviation cost
`D(log₃2 ‖ ½)` of fixing `a = ⌊L·log₃2⌋`.  It is **not** the cost of heaviness: by
the cycle lemma heaviness costs a factor `L` and *no entropy*.

**Rigorous asymptotic** (paper, not Lean): with Rhin's `μ(log₂3) ≤ 5.117`,
`surplus ≥ 0.0500445·L − 4.117·log₂L − O(1) → ∞` unconditionally, and
`Σ 2^(−surplus)` converges.  This upgrades `CycleLanguage.count_lt_gap` from one
pair with the crude constant `0.95405` to an asymptotic with an effective constant.
Measured slope over 7570 shapes with `L ≤ 12000`: **0.05039**.

**The accounting.**  To make counting work outright needs `N < 1`, i.e. a further
**0.94996 bits/letter** — 19× the surplus.  Every known constraint: heaviness 0
(cycle lemma); mod-4 and the whole 2-adic image 0 against odd `G`; Beatty box 0 (it
*is* the heavy language); run structure 0 (`heavy_pad`: no forbidden block exists);
necklace 0; `δ` 0 asymptotically.  **The combination cannot reach 0.06.**

## The reverse tree, and one identification worth keeping

`BackwardRange`.  The verified range buys a constant factor, never an exponent:
pruned branching factor `4/3` to four decimals, identical to unpruned, stabilising
by depth 16, with the range's entire reverse-tree content confined to the single
window `[1086464, 1629696]`.  `backward_range_is_forward_range` proves the two
conditions are one predicate.

The find: the counting exponent for bounded reverse paths is exactly
`1 − H(log₃2) = 0.05004` — the same deficit, and **not by analogy**: the weight
`binom(k,a)·3^(−a)` *is* the forward heaviness generating function.  Two quantities
treated as separate for three rounds are one.

## Corrections

* Three of my `WindowCollapse` conclusions (above), and the inconsistency between my
  own two directives.
* `ExtremalWord`'s `heavy ⟺ box` is **false**; only `⟹` is proved.  Counterexample
  `a = 1`, `t₀ = 0`, `J = 2` (word `100`): the box holds, `2² = 4 > 3 = 3¹`.  The
  exact statement needs `2^J ≤ 3^a`, so the box picture is valid **on the ledge
  only** — verified: off-ledge the box counts `1,1,2,3,7,12,30,85,173` while the
  truth is **zero** in every case.
* `RunRefined` still carried, one screen below the header that repairs it, the stale
  *"worst ratio 1.0000 over 59 058 heavy words"* — a population with no positive-gap
  member.  Now `0.85185` over the 12 449 proper-prefix-heavy positive-gap words.
* **`delta_no_growing_bound` does not close what I said it closes.**  It refutes only
  `L`-indexed *growing* lower bounds on `δ`.  The constant bound `δ ≥ 2` is untouched
  and every measurement supports it — `δ = 1` occurs only at `L = 2`, with
  `min δ ≥ 5` at every `4 ≤ L ≤ 40`.  My brief said the `δ` direction "contributes no
  asymptotic suppression", conflating the two.  Caveat the adversary did not add:
  **`δ ≥ 2` is the conjecture restated**, so it states the target correctly rather
  than advancing on it.
* `SinkStructure`'s "every element of `S` is a genuine cycle word" is **vacuous on
  the `d = 1` side**: `S(L,a,G) = ∅` at every ledge pair with `L ≤ 24`.  Its content
  is in the `d = −1` and `d = 5` worlds.
* Terras surjectivity and the high-part identity were both flagged as *missing
  bridges* by earlier agents.  Both are already proved in the repo
  (`parityVector_surjective_mod_pow_two`, `Congruence.accOrbit_pow_two_mul_add`).
  Third such rediscovery this round — the development needs an index.

## Where Round VI leaves it

Every route now reduces to one statement, and its shape is finally exact:

> The image of `w ↦ C(w) mod G` on the cycle language is a sparse, essentially
> injective, structureless `N`-element subset of `Z/G`, with `N/G = 2^(−0.05L)`.
> Whether it contains `0` is the conjecture.  The surplus is real and provably
> growing; it is also **2-adic, while `G` is odd**, so it is orthogonal to the
> target — and no known constraint contributes at any modulus sharing a factor
> with `G`.


---

# Round VII — cartography, and one theorem that localises the problem

The protocol changed: build an index before attacking.  Four specialists, one
adversary, and the adversary was right about almost everything.

## The deliverable, and its repair

`scripts/index.py` + `INDEX.md` — a regenerable concept map: 2165 declarations,
17 clusters, concept pairs no theorem mentions together, and a what-is-known matrix.
`python3 scripts/index.py find <regex>` answers the question that caused this round
(three times in Round VI an agent flagged a "missing bridge" already proved here).

**The first version was broken three ways** and the adversary found all three.  It
never stripped comments, so it indexed English words from docstrings as theorem
names — `at`, `this`, `plus`, `says`, `that` — which carried tags from surrounding
prose and inflated 41 pair counts.  It covered 64.7 % of declarations while
asserting that *no theorem anywhere* mentions two concepts together.  And its
vocabulary caught only one of the four idioms this repo uses for `G ∣ C`, hiding 18
theorems that state exactly that; `RepetitionDescent.subst_yields_cycle` alone closes
seven of the reported gaps.

**My headline was an artifact.**  I reported "`C mod G` is the most isolated
cluster, zero bridges to seven others".  My own JSON said *twelve*, not seven — I
misread my own output — and after the repair `C mod G` has **four** unbridged pairs
and is not the most isolated cluster at all.  The genuinely isolated clusters are
**Beatty/Sturmian** and **finite-state** (nine unbridged pairs each), then 2-adic
valuation and reverse paths (eight each).  That is where the next round should look.

## The theorem: consecutive gaps are coprime

`AccumulatorAutomaton.gap_coprime_snoc` — independent of the index, and it stands.

`gcd(2^L − 3^a, 2^(L+1) − 3^(a+d)) = 1` for both legal letters `d ∈ {0,1}`, whenever
both gaps are positive.  Two subtraction-free identities do it: even letter
`G' = 2G + 3^a`, odd letter `2G = G' + 3^a`, so a common divisor divides `3^a`, hence
is odd, hence divides `2^L = G + 3^a`, hence is 1.  Zero exceptions over `L ≤ 300`.

By CRT the residue before a letter constrains the residue after by **exactly zero
bits**.  There is no transition law between `C mod G` at consecutive lengths and
there cannot be one, so any bridge to that cluster must live at *fixed* `(L,a)`.
Coprimality is special to the two legal successors; illegal shifts give non-coprime
pairs readily.

And inside fixed `(L,a)` both obstruction shapes die.  State invariants are vacuous
(letter `0` is the identity and the start state is `0`, so no subset of `Z/G` closed
under both letters and avoiding `0` exists).  Time-blind graded invariants are
vacuous too: `C w = Crel(times w)`, the sum over the **strictly increasing** odd-step
times, and dropping *only* the increasing condition hits zero at once —
`Crel[1,1,1,1,0,0,1,1] = 6524 = 4·(2^13 − 3^8)`.  Verified.

> **The entire content of the cycle problem is the ordering `t₁ < ⋯ < t_a < L`.**
> The hoped-for interaction between the multiplier 3 and the modulus `G` does not
> exist — they generate everything mod `G` in two steps.  What remains is
> combinatorial, not arithmetic.

That is a different answer from Rounds III–VI, which kept concluding "this arithmetic
route is closed".  This one says the arithmetic is *free*.

## Every 0.05004 is one number

`ForwardReverse`.  Terras gives every length-`L` word one class mod `2^L`, so the
forward density is `2^(−L)`.  `endpoint_class` gives it one class mod `3^a`, so the
reverse density is `3^(−a)`.  And heaviness, `2^L ≤ 3^a`, **is** the statement
`3^(−a) ≤ 2^(−L)`: *the reverse class is no denser than the forward class*.  The
heavy language is defined by the inequality that equates the two weightings, so the
exponents cannot fail to agree; the only arithmetic input is `log₃2 · log₂3 = 1`.

So the two counts are not in bijection and none exists — they are one coefficient
vector under two weightings.  `1 − H(log₃2) = D(log₃2 ‖ ½)` is a **large-deviation
rate**, not a Perron eigenvalue (the language is non-sofic in both directions) and
not a pressure zero.  Every `0.05004` in this repository — `ImageDensity`'s,
`SieveGrowth`'s, `BackwardRange`'s, the record sequence's — is this one number.
Real, and vacuous: the whole content is a relation between two functionals of
`(L,a)`, and `C(w)` is the coordinate a transfer operator integrates out.

New and worth keeping: `reverse_branching`, `Σ_a binom(L,a)·3^(L−a) = 4^L` — the
first *proof* of the `4/3` reverse branching factor, which Round VI only measured.

## Architecture A is circular

`FiniteInfinite`.  The canonical-representative characterisation is true — realized
by a natural iff the representative tower is eventually constant, positive iff the
eventual value is nonzero — but it is `ℕ ⊆ Z₂` by truncations with a bijection glued
on.  And in `divergent_rep_stabilises` the divergence hypothesis is *bound to an
underscore*: a divergent orbit is by standing hypothesis the orbit of a positive
integer, so its representatives stabilise regardless.  Integrality is the hypothesis
in disguise.

`minNonDrop L → ∞` is **equivalent to full Collatz** — strictly stronger than the
divergence half, against my expectation, since a cycle's minimum never drops and caps
the record exactly as a divergent orbit does.  Its growth law is
`D(L) = Θ(2^L / heavyCount L)`, carrying no arithmetic beyond the survivor count.

## Corrections — seven of them mine

* **The index**, above.
* **My Round VI correction was itself wrong.**  I "corrected" `WindowCollapse` to say
  the residual is "the letters after time `L`, not magnitude", as though those
  differed.  They are the **same datum** — given the prefix, a continuation of length
  `k` and `m mod 2^k` determine each other bijectively, so the later letters *are* the
  binary expansion of `m`.  Verified.  And the inconsistency I derived is false:
  `window_sequence_realized` produces *some* `x` with no bound and says nothing about
  whether a *given* `x` admits a continuation.  Bounded-`x` constraints are untouched
  and sharp.  **The two directives were consistent; I over-corrected.**
* **`HighPart` claimed the high part strictly increases.**  It *decreases*:
  `x = 13`, `L = 2` gives `3 → 2`.  The theorem compared a high part with an orbit
  value, which are incommensurable.  The branch is uninteresting for a different
  reason — a cycle's high part is identically zero.
* **My `0.084 bits/step` was a two-point chord**, not a fit.  OLS gives 0.096–0.099,
  and the true law is `0.05004·L + 1.5·log₂L`, so no single slope over `L ≤ 400` is
  meaningful.  The record sequence itself was verified correct, values and labels.
* **"The finite/infinite gap reduces to the verified range" is wrong.**  It *is* the
  conjecture.  And the sharpest quantification of asset (a) yet: the largest `L` for
  which some `x < 1086464` is non-dropping is **182**, so the verified range
  discharges the boundary at `L = 183` and no further — **183 of 6809 steps, 2.7 %**,
  about 9 of the ~341 bits of surplus at the frontier.
* **`BackwardRange`'s window**: the sharp threshold is `1629696`, not `1629697`
  (`1629696 ≡ 0 mod 3`, so it has no odd preimage at all); the interval is 543232
  wide; and only the **181078** nodes `≡ 2 (mod 3)` actually lose a predecessor — a
  third of the figure quoted.  All verified.
* **`ImageDensity`'s "the surplus is worth zero"** is `YELLOW`, not clean.
  `two_power_vacuous` proves a mod-`2^j` congruence *alone, over unbounded `n`*
  excludes no multiple of `G`.  The surplus is a **cardinality** deficit, and against
  the bounded target `{kG : k ≤ max C/G}` the 2-adic image density is worth exactly
  its `2^(−0.05L)`.  The worry about a modulus sharing a factor with `G` is genuinely
  covered, though — `3 ∤ G` too, so both known structural handles sit at moduli
  coprime to `G`.

Also confirmed, from a long-running background check: Round V's forced-extremality
ratio first drops below 1 at exactly `a = 4296`, `L = 6809` — independently
reproducing `RealizableFrontier6809` — and `max gcd(Bcap a, G) = 22139` at `a = 2773`.

## Where Round VII leaves it

The problem is now localised more sharply than at any previous round, and not where
six rounds of arithmetic looked:

> `C mod G` is arithmetically free — consecutive moduli are coprime, the automaton on
> `Z/G` is unobstructed, and 3 with the powers of 2 generate everything in two steps.
> **All remaining content sits in the ordering `t₁ < ⋯ < t_a < L` of the odd-step
> times.**  Any invariant blind to that ordering is provably vacuous.

The two most isolated clusters in the corrected index — Beatty/Sturmian and
finite-state — are exactly the two that speak about *orderings*.  That is the next
round's target, and it is the first time the map and the mathematics have pointed at
the same place.


---

# Round VIII — the ordering, and the barrier that follows it there

Four specialists and a dedicated adversary against the ordered odd-step times
`0 ≤ t₁ < ⋯ < t_a < L`.  All four proposed chains died; one real bridge was built;
and the barrier that has blocked every previous round transported into the new
language intact.

## The combinatorial layer, stated cleanly

Heaviness `2^j ≤ 3^(A(j))` is exactly `A(j) ≥ j·log₃2` — **the discrepancy path at
the critical density stays non-negative**.  That is the whole of heaviness, and it is
one-sided.  Cleared of logarithms, on the ledge:

> **`CyclicOrder.heavy_walk_pos` / the one-sided bound.**  If `2^j ≤ 3^(A(j))` and
> `3^a < 2^L`, then `a·j < L·A(j)` at every interior `j`.

Four lines: raise heaviness to the `L`, raise the ledge inequality to the `j`, chain,
strip the base.  Verified: 1751 heavy words at ledge pairs, **zero** violations —
and off the ledge **2702 of 4402 violate**, so the hypothesis is load-bearing.

It is sharp, and the upper side is free: `max_j D(j) = a(1 − a/L)` is **attained**,
by `1^a 0^(L−a)`, which is heavy at every proper prefix for every `L ≤ fexp a + 1`.
At the frontier that is `D* = 1585.5` at `(6809, 4296)` against `≈ 1` for the Beatty
word.  **The heavy language spans the entire discrepancy range.**

## The bridge: discrepancy *is* spread

`Discrepancy.bridge_two_sided`.  From the cocycle and the cycle criterion, the
correction term is bounded by the ledge slack itself:

`|log₂(x_j/n) − log₂3 · D(j)| ≤ E = L − a·log₂3 < 1`.

Logarithm-free, that is the pair `3^(A(j))·n ≤ 2^j·x_j` and
`3^a·(2^j·x_j) ≤ 2^L·(3^(A(j))·n)` — a multiplicative window of width `2^L/3^a`,
strictly under one bit.  So **Round V's spread question and Round VII's ordering
question are the same question**, with a translation error bounded by an absolute
constant independent of `n, L, a, d`.

The two Round V endpoints match exactly: min spread `→ log₂3` **is** `Dwidth → 1`
(the Sturmian discrepancy bound); max spread `0.585a` **is** `Dwidth = 0.369a`, since
`log₂3 × 0.369 = 0.5849`.

Because the window is under one bit, the discrepancy **orders the orbit**:

> **`disc_forces_order_any`.**  For a cycle on the ledge, if `D(j) ≥ D(k) + 2` then
> `x_k < x_j`.

Verified over 180 genuine cycles of `3x+d` with `d < 200`: the largest `D`-gap in an
inversion is **0.1034**, so the constant 2 is conservative about twentyfold, and on
the tabulated cycles there are zero inversions — discrepancy order *is* orbit order.
Dropping the ledge hypothesis and sweeping `−99 ≤ d ≤ 99` produces inversions with
gaps to 2.92, which would falsify the theorem; the ledge is genuinely consumed.

**And the barrier transports.**  By the bridge, a `Dwidth` bound is *equivalent* to a
spread bound, and `SpreadFloor` already proves no `d`-free mechanism can supply one —
the Sturmian word at `(4701, 2966)` is a genuine cycle of `3x + δ` with spread
2.99930.  So **no `d`-free mechanism can bound a cycle's discrepancy either.**  The
honest payoff of this round is a barrier transported into a new language, not a route
opened.

## The four chains, all dead

* **Chain A (bounded discrepancy ⇒ balanced ⇒ Sturmian).**  No first step: the
  discrepancy is `Θ(L)` on the heavy language, attained by a heavy word.
* **Chain B (cycle ⇒ balanced).**  Refuted by three explicit words.  Genuine cycles
  are *not* balanced — the `3x−1` cycle through 17 has balance **3**, the `3x+5`
  27-cycles balance **5** and **4** — and `11010`, a genuine `3x+5` cycle, *is*
  balanced.  Balance is neither necessary nor a discriminator.
* **Chain D (accumulator-minimal ⇒ balanced).**  Provably **reversed**.  Within a
  rotation class `C = |G|·n/d`, so accumulator-minimal ⟺ `n`-minimal ⟺ the rotation
  starting at the orbit minimum ⟺ **the heavy rotation** — and heaviness is maximal
  prefix bias.  Confirmed on the only two nonempty test sets: in `S(11,7,139)` the
  minimum is the least balanced of the eleven; in `S(27,17)` it has both the maximum
  balance and the maximum discrepancy of all 54.
* **Chain E (`L` rotations ⇒ `L` constraints).**  `CyclicOrder.walk_shift`: the walk
  is closed, and every rotation gives the same constraint up to an additive constant
  read off the same walk.  Max and min over a period are rotation-**invariant**.

Also closed: the ordering automaton.  `OrderAutomaton.disc_append` — the discrepancy
is **additive** along the word.  So if `ρ` is unknown at read time `D(j)` is not
prefix-computable (not an automaton); if `ρ` is fixed it is additive and the
admissible language is a monoid language with an injection of `{0,1}^m` into it —
verbatim `sieve_never_terminates`.  Diagnostic worth keeping: **test any proposed
finite-state statistic against `disc_append` first; if it is additive along the word,
it is dead on arrival.**

## What the ordering is worth, exactly

The `(j, A(j))` lattice region actually visited by heavy words is **exactly** the
heavy-feasible region at every pair tested — the only region-level constraint is
heaviness restated.  The product automaton `(j, A(j), C mod G)` has reachable set of
maximum conceivable size, deficiency under 0.5 %.  Entropy stays at `2^(0.94996 L)`.
Even a *granted* bound `|D| ≤ M` leaves positive entropy at every `M ≥ 1`.

## Corrections, five of them mine

* **I duplicated an existing theorem.**  I wrote the one-sided bound as a new file
  before consulting the index; it is exactly `CyclicOrder.heavy_walk_pos`, derived
  independently by an agent in the same round.  Deleted.  The index caught it, which
  is what it is for — this time on me.
* **My Chain D refutation attacked the wrong object.**  I refuted "unconstrained
  accumulator-minimal ⇒ balanced"; Chain D's sink is the minimum *subject to*
  `G ∣ C`.  The conclusion survived — the adversary killed the right object, in the
  same direction, with a proof rather than a measurement — but my framing was wrong.
* **`max C = Bcap a` is a ledge statement.**  Below the ledge the Beatty corner does
  not fit and the maximum is strictly smaller: `a = 7, L = 9` gives 3511 against
  3767; `a = 10, L = 13` gives 121165 against 148813.  The minimum half is unaffected.
* **Coordinatewise monotonicity does not by itself put the extremes at the corners**,
  since the feasible set is `box ∩ {strictly increasing}` and raising one `t_i` can
  collide.  The repair: the feasible set is a **sublattice** with top and bottom.
* **`heavy ⟺ box` holds for every `L ≤ fexp a + 1`**, not "on the ledge and only
  there" as `ExtremalWord`'s header and my own note said.  The failure is one-sided —
  above the ledge only, where the heavy set is empty and the box is not.  Verified,
  zero mismatches.

## Where Round VIII leaves it

The ordering is now fully mapped, and it is not where the obstruction lives:

> Heaviness is one-sided non-negativity of the critical-density discrepancy path.
> `C` is monotone on the resulting box, with both corners explicit.  Discrepancy and
> spread are the same quantity to within one bit, and the discrepancy orders the
> orbit.  Every ordering statistic examined — balance, discrepancy width, majorization
> position, rotation profile, lattice region — is a function of the word, invariant
> under `C ↦ d·C`, and therefore dead by the soundness filter.

The barrier is unchanged and now has three equivalent statements: no `d`-free
mechanism can bound a cycle's spread, its discrepancy width, or its accumulator
position in the box.  What would break it must consume asset (a), (b), (c) or (d) —
and asset (a) is worth exactly 183 of 6809 steps.

---

# Round IX — the invention round

The mandate was not another inequality: *invent a mathematical object that
distinguishes a genuine positive-integer Collatz trajectory from an arbitrary
locally realizable parity sequence.*  The **New Object Rule** rejected anything
that turned out to be another function of the discrepancy path.

Every branch that reported closed itself.  That is the correct outcome for an
invention round and it is reported as such — no branch was talked into surviving.

## Part II — what was invented, and how each one died

| field | object | how it died |
|---|---|---|
| heights | canonical height for `T` | the naive one **is** the discrepancy path; and `canonical_height_vanishes` proves the only `H` with `H(Tx) = k·H(x)`, `k ≥ 2`, is `H ≡ 0` |
| transfer operators | `L`-sub-eigenfunction | it **is** a forward ranking function with geometric rate; `cycle_forces_zero` makes it vanish on the trivial cycle |
| rewriting | simplification orders | `no_simplification_order` — `bits x` embeds in `bits (T x)`; fails already at `x = 3` |
| logic | quantifier prefix of each half | `d`-independent, so a ledger entry, not a mechanism — but see Part IV |
| coding theory | transposition syndrome `σ(y)` | the code's `dmin` is **twice the run count**, an invariant already in the development; cycle words are run-rich |
| geometry of numbers | the box, and its dual lattice | Minkowski's hypothesis fails by `1.23^a`; the one theorem with *absence* polarity needs a dual vector a determinant count forbids past `a ≈ 9` |
| homological algebra | `Ext¹` of the transfer module | `= ℤ/G` with class `C mod G`, and the `d`-action is scalar multiplication |
| machine models | weighted automaton on digits | see Part V |

## Part III — the one real theorem the round produced

Not a new object; a closure of a whole class of them.

> **The soundness filter is a corollary of additivity.**  The obstruction group of
> the transfer module is `ℤ/G` with class `C mod G`, and `3x+d` acts on it by
> multiplication by `d` (`class_scales`, `delta_realises`, verified exhaustively at
> `L ≤ 12`, `1 ≤ d ≤ 59`, zero mismatches).  Hence **every** invariant obtained by
> applying an additive functor to the transfer module is `d`-linear, hence refuted.

Any future proposal phrased in homological algebra over the transfer matrix is dead
before it is written.  This upgrades the filter from a rule of thumb about past
attempts to a theorem about abelian categories.

Second, and independent: **the 2-adic tower has no gluing obstruction at all.**
`lim¹` of an inverse system of finite sets always vanishes, so local sections always
glue and the glued object is a 2-adic integer.  Collatz is not a local-to-global
failure.  The only obstruction the tower supports is an **empty level**, which
requires the archimedean cut — and at `B = 1086464` that level is exactly `K = 183`,
witnessed by `x = 1027431` surviving to `L = 182`.  Asset (a) is not an infinite
family of facts; it is one empty level of one inverse system.

## Part IV — two results that change how this program should be run

**The frontier is a cycle-half asset only.**  The cycle half is `Π⁰₁` and the
divergence half is `Π⁰₂` (`collatz_iff_halves`, proved both directions).  A `Π₁`
sentence has finite refutations; a divergent orbit is not a finite object.  So
`L ≥ 6809` says **nothing whatever about divergence**.  The verified range is
different — it bounds a divergent orbit's minimum, so it does bite on both.

**The frontier programme is an instance of the ω-rule.**  Truth of every instance
gives truth of the sentence; provability of every instance gives provability in *no*
formal theory.  Closing it needs a proof uniform in `Lmax`, and
`RealizableFrontier6809.length_ge_6809` takes `Lmax` as a numeral.  Worse, instances
are not cheap: the frontier is driven by the verified range at `L ≈ V/160`, linear,
so the `L`-th instance costs `Θ(L)`.  **Frontier increments should be scored as
compute expenditure, not as progress toward the sentence.**

Two families are also retired outright.  *Independence via a fast-growing witness*:
`σ(n) ≈ 6.83·ln n` measured to `n < 200000`, far below any Paris–Harrington
threshold, so if Collatz is independent of PA it is not for a growth reason.  *Any
compactness or limit argument*: a model of PA with an element `> 1` satisfying
`NeverDrops` exists **iff** PA does not prove Collatz.  So "get a nonstandard
counterexample from compactness" *is* an independence proof.  That is the exact
reason every limit argument in this program has been circular — the object
compactness builds is one quantifier short, and closing that quantifier is the whole
problem.

## Part V — the survivor, named and then narrowed

Round IX's one open mechanism was **matrix interpretations of dimension `≥ 2`**,
unwound as an `N`-weighted automaton reading the **binary digits of `x`** — flagged
as the first mechanism to escape `C ↦ d·C` for a structural reason.

The escape is illusory.  By Terras, `x mod 2^n` and the parity word of length `n`
are the same datum (`low_digits_iff_word`, `word_eq_iff_mod`), so a digit-reading
automaton's entire state trajectory is a parity-word statistic.  Its only extra
information is **where the reading stops** — the digit length, i.e. the magnitude.

Its dimension floor has a better reason than the one first given: a dimension-`1`
automaton yields `ρ^(digits x)`, purely exponential in length, while a ranking
function must track something the size of the stopping time, which is **linear** in
the digit length.  Linear-in-length is exactly a dimension-`2` unipotent block.

And at that dimension it is unreachable.  Hankel rank is the exact dimension of the
smallest weighted automaton computing a sequence; on `σ` restricted to a digit ray it
**saturates** — rank `12, 20, 30` at `24, 40, 60` terms — on `2^m − 1`, `2^m + 1`,
`2^m + 3` and `3·2^m − 1` alike.  The lone exception is `2^m`, where the map is pure
halving (`stopping_two_pow`), which is why that ray is not evidence for the others.
An exhaustive search of all `419904` dimension-`2` interpretations with entries in
`{0,1,2}` returns zero ranking functions.

Honest status: not refuted outright, since a ranking function need not be `σ`.
Downgraded to *open only for a ranking function nobody has exhibited, on the same
archimedean datum every other route needs*.

## Part VI — the object that is missing, named

Not "try another approach".  The object.

Every device in this development is a function of the parity word.  The parity word
of length `L` is exactly `x mod 2^L` — one residue, and by Terras every residue
occurs.  So the parity word is **free**: it carries no obstruction, and every
mechanism built on it inherits `C(w,d) = d·C(w,1)`, which is why `3x+5`, `3x−1`,
`3x+7`, `3x+11`, `3x+13` refute each one in turn.  Round IX closed eight further
fields on exactly this ground, and Part III makes it a theorem for a whole class.

The missing object is therefore not another word statistic.  It is:

> **A quantity that couples the 2-adic datum to the archimedean one — that reads
> `x mod 2^L` and `log₂ x` together, and is not a function of either alone.**

Three independent routes now name the same gap in the same terms.  Heights: the
topological degree of `T` on `ℤ₂` is `2`, the archimedean expansion is `1`, and for
a degree-`d` morphism of `P¹` those are *forced* to agree — Collatz is exactly where
they come apart.  Homological algebra: `lim¹` on the 2-adic tower vanishes
identically, so the only obstruction is an empty level, and a level can only be empty
after an archimedean cut.  Machine models: a digit automaton's state is a parity-word
statistic and its only further datum is the length.

The development already knows the two sides agree to **within one bit** —
`bridge_two_sided`, `|log₂(x_j/n) − log₂3·D(j)| ≤ E < 1`.  That one bit is the entire
remaining content of the problem, and nothing in this program yet computes it.  The
object to invent is whatever *does*.

## Round IX postscript — Part VI, corrected by its own candidate

Part VI named the missing object as *a quantity coupling the 2-adic datum to the
archimedean one*.  Pursuing it immediately produced the canonical candidate, and the
candidate closes half of the question.

Expanding `bridge_two_sided` against the affine law leaves no freedom:
`θ_j = −j·E/L + log₂(1 + r_j)` **exactly**, where

> **`r_j = C_j / (3 ^ (A_j) · n)`** — the accumulator measured against the orbit.

That is the coupling: 2-adic numerator, archimedean denominator, a function of
neither alone.  Its dynamics are clean — unchanged on an even step, `r ↦ r +
d·2^j/(3^(A_j+1)·n)` on an odd one, so `n` enters only through the odd branch's
additive constant, and `r` runs from `0` to `G/3^a`.

**And on a cycle it collapses to a word invariant.**  Verified on genuine cycles of
`3x+1` at `1`, `3x+5` at `187`, `3x−1` at `17` and `5`, `3x+59` at `229`: at every
`j`, `r_j = G·C_j / (3^(A_j)·C_L)`, with both `d` and `n` cancelling.
`Coupling.coupling_collapses` proves it and `collapse_iff_cycle` shows the collapse
is *equivalent* to the cycle criterion, not merely implied by it.  The reason is one
line: `cycle_gap_mul` gives `G·n = C_L`, so **on a cycle the archimedean datum is not
free** — `n` is determined by the word, and there is nothing left to couple.

So Part VI splits, and the split is sharper than the statement it replaces:

* **Cycle half — closed to coupling, permanently.**  Any `Q(x, window)` evaluated on
  a cycle is a function of `(word, d)` because `n` is; `C(w,d) = d·C(w,1)` then scales
  `d` out; so `Q` is a word invariant and the soundness filter refutes it.  *This is
  why every route in this programme dies on the cycle half specifically.*  It names
  the reason rather than a mechanism.
* **Divergence half — open, and this is where the coupling lives.**  A divergent orbit
  never closes, so no relation `G·n = C_L` exists to eliminate `n`.

That matches `collatz_iff_halves` exactly: the `Π⁰₁` half is finitely refutable and
carries no archimedean information, and the `Π⁰₂` half is where it all is.  Read
together with the ω-rule result, the programme's own frontier work has been aimed
squarely at the half where the missing object provably cannot exist.

The independent phantom-mediant branch reached the same conclusion from the other
side and should be recorded with it: its descent fails not from weakness but from
**domain emptiness** — the split band is empty at every convergent shape, including
the entire frontier ladder `(2,1), (8,5), (27,17), (46,29), (65,41), (485,306),
(1539,971), (2593,1636), (4701,2966), (6809,4296)`, each reproduced exactly.  Its
own summary is the same rule in different words: *the only escapes from the complete
invariant are objects on the fibre `(word, magnitude)`, or objects sensitive to `d`*.

---

# Round IX wave two — the required ledger

Five agents, the standing maximum.  Four inventions and a permanent adversary.  The
adversary killed two headline claims, one of them the orchestrator's, and found the
same logical error in three files.  That error is now a permanent diagnostic.

## Part I — existing closure

`CLOSURE.md`, unchanged in its four classes, but its diagnostic list grew from two to
three.  The new one is the round's most reusable output:

> **Diagnostic 3 (homogeneity).**  A quantity dies to Class 4 iff it is **homogeneous
> of degree 0 under `C ↦ d·C`** — *not* because it is a function of the parity word.

Three files argued *"`Q` is word-computable ⟹ `Q` is a word invariant ⟹ refuted"*.
The middle step is invalid: `C_L(w,d)` is word-computable for each fixed `d` and is
not `d`-blind, and `δ(w) = G/gcd(C,G)` is word-computable and is precisely the
`d`-separating residual that belongs to no class.

## Part II — new devices

| device | file | escapes via | assets used | verdict |
|---|---|---|---|---|
| floor schedule (occupation measure on odd steps) | `FloorSchedule` | `(word, magnitude)` fibre | **(a), (c), (d)** | passes the filter, obstructs nothing |
| cut game + strategy memory | `CutGame` | arena quotient | (a) | **unifies the cycle/divergence split** |
| ground state `wTermMax` | `GroundState` | — | none | closure device: no phase transition |
| tropical defect | `TropicalDefect` | — | (a), (c), (d) for one corollary | exact accounting of what tropicalisation destroys |
| linearising coordinate | `Linearizing`, `Coupling` | `d/n` | (c), silently | rank one |

## Part III — the best five, ranked by information the framework cannot see

**1. Strategy memory (`finMem_ultimately_periodic`).**  *Definition:* the state space of
a winning strategy in the cut game, an invariant of the arena quotient, not of a play.
*First theorem:* finite memory ⇒ ultimately periodic run ⇒ eventual genuine cycle ⇒
refuted by asset (a).  *Why it ranks first:* it unifies two facts held separately —
the frontier and verified range are cycle-half assets **because** they are exactly what
refutes finite-memory strategies, and the coupling lives only on the divergence half
**because** that is where play is not eventually periodic.  *Missing bridge:* a
finite-memory play whose tower does not stabilise yields unboundedly many
never-dropping integers rather than one cycle; nothing refutes that.  *Lean:*
LEAN_PROVED.

**2. The floor schedule.**  *Definition:* `f i ≤ T^i(x)` discretising the occupation
measure on odd steps; invariant `∫log(1 + d/(3t))dν` instead of a constant rate.
*Evidence:* the only device this round to consume three assets and to escape the
complete invariant honestly — `x = 3` and `x = 259` share the length-8 word and have
charge ratios `512/3` and `82.04`.  *Counterexample:* none; it is simply not an
obstruction — the vanishing-slack words are still exponentially many.  *Lean:*
LEAN_PROVED.

**3. Diagnostic 3.**  Not an object but a filter, and it corrected three files in one
round.  Ranked here because a wrong filter costs more than a wrong theorem.

**4. The rank-one theorem.**  `r_j = (d/n)·W_j(word)`.  *Why it matters:* it **caps**
what any coupling device can carry — exactly one real number.  Reached independently by
two agents and confirmed in exact rationals on seven cycles.  *Lean:* the `Nat` halves
are proved; the factorisation is COMPUTATIONAL.

**5. The mediant descent, reopened.**  Not new, but wrongly retired: its "domain
emptiness" was a selection artefact, and it has nonempty domain at ~96% of
cycle-admissible shapes.  *Entry point:* `(6816, 4300)`, band size 2839.

## Part IV — three architectures

**A. Cycle half, mediant descent.**  At a non-record ledge take a split with both
halves in the band; mediant betweenness puts one phantom strictly below the cycle
minimum; if that phantom is integral, a smaller cycle exists, contradicting
minimality.  *Missing bridge:* integrality of the sub-phantom — `δ` of the half must
be 1, and `δ = 1` is rigid (only `(10)^k` and the all-even word to `L ≤ 22`).

**B. Divergence half, strategy memory.**  Show a winning play must have finite memory;
`finMem_ultimately_periodic` then forces an eventual cycle, refuted by asset (a).
*Missing bridge:* the memory is at least `ω`, and nothing bounds it.  This is the
architecture the round most wants and least supports.

**C. The fibre.**  The floor schedule pins the archimedean coordinate to the word
within a fixed multiplicative constant, permanently.  Combine with a count of
vanishing-slack words.  *Missing bridge:* that count is `2^{0.94996 L}` — Class 2,
and the unconditional `L¹` barrier already blocks the counting route.

## Part V — the deepest surviving idea

**Strategy memory**, chosen on the stated criterion rather than on evidence.  It is
provably not a word invariant (`escape_word`: `n` and `n + 2^L` share every word to
level `L`), its composition law is a supremum rather than a sum so `disc_append` does
not reach it, and it is the only object this round that *explains* the cycle/divergence
split rather than restating it.  It has almost no supporting computation, which is
exactly why it is chosen here.

## Part VI — the object that is missing, named

Round IX's first pass named *a quantity coupling the 2-adic and archimedean data*.
That object now exists, is understood, and is capped: it is `r_j`, it carries exactly
one real number `d/n`, and it collapses on the cycle half.  So Part VI must be renamed,
and the round's sharpest new fact names it:

> **The missing object is a refuting witness family for the divergence half.**

Every filter this programme owns is a cycle witness.  The soundness filter works
because genuine cycles of `3x−1, 3x+5, 3x+7, 3x+11, 3x+13` exist and refute `d`-free
cycle mechanisms on contact.  **No divergent orbit of any `3x+d` is known.**  So a
divergence-half mechanism faces *no filter at all* — which is not permissive but
disabling: there is currently no way to tell a good divergence-half device from a
vacuous one, and Round IX proved the divergence half is the only place the coupling
can live.

Building that filter — a family of `d` (or of maps in a wider class) with provably
divergent orbits, against which a divergence mechanism can be tested — is now a
first-class task, and it is a concrete, checkable one in a way "find a new invariant"
never was.

---

# Round X, Sections XV–XVII — the pin constant tends to 1, and the product formula is empty

*Arithmetic-dynamics desk.  New file: `Collatz/Strategy/GlobalHeight.lean` (compiles
clean, zero errors, zero warnings, no `sorry`/`axiom`).  `Height.lean` is not
repeated: nothing here obeys a functional equation, and nothing here is a local
decomposition `α·log₂x + β·v₂ + γ·v₃`.*

## XV — A global height, and the one hypothesis no cycle supplies

The device is not a new function on `ℕ`.  It is the **explicit evaluation of the pin
constant** that `FloorSchedule.sched_pin` left as an unevaluated product, using the
one hypothesis the divergence half owns: *the orbit is eventually above every bound.*

**Arithmetic core** (`pow_step_bound`, LEAN_PROVED):
`c · (3c+1)^a ≤ (c + 2a) · 3^a · c^a` whenever `2a ≤ 5c`.
So `(1 + 1/(3c))^a ≤ 1 + 2a/c` — the schedule defect is **linear in the window
length**, not exponential, as soon as the floor exceeds it.

**The pin** (`pin_explicit`, LEAN_PROVED): if `c ≤ T^i(x)` for every `i`, then

> `3^(a k)·x ≤ 2^k·T^k(x)` and `c·(2^k·T^k(x)) ≤ (c + 2·a k)·(3^(a k)·x)`.

**The limit** (`pin_ratio`, `pin_two`, `pin_tends_to_one`, LEAN_PROVED): floor
`c ≥ 2jk` gives error `1 + 1/j`.  Hence along a divergent orbit, for every window
length `k` and every accuracy `j`, some tail window has

> `|log₂ x_{N+k} − log₂ x_N − (a·log₂3 − k)| ≤ log₂(1 + 1/j)`.

Comparison, stated exactly.  `bridge_two_sided` is a **cycle-half** statement: its
error factor is the spread `2^L/3^a` of a closed window, and it has no divergence-half
analogue.  `sched_pin` is the divergence-half one, but leaves the error as an
unevaluated product and can only assert it is a constant "along an orbit growing at
least geometrically".  This evaluates that constant, replaces the geometric-growth
hypothesis by mere divergence, and drives the constant to `1`.

**What it does to Round IX's coupling.**  `r_j = C_j/(3^(A_j)·n)` is exactly the pin
defect, so `pin_ratio` says `r_j ≤ 2·a/c → 0`.  Round IX found the coupling
*collapses to a word invariant on the cycle half*; the divergence half is worse:

> **the coupling tends to `0` on the divergence half.**  Both halves are therefore
> asymptotically word statements, which is the structural reason every route in this
> programme lands in Classes 1–3.

Consequently the divergence half reduces, with error `→ 1`, to the pure word
statement *"every tail window of the orbit's infinite parity word is heavy"* —
`heavy_of_never_drop` (LEAN_PROVED): under a floor `2k ≤ c` and `x ≤ T^k(x)`,
`2^k ≤ 2·3^(a k)`, uniformly in `k`.

**Non-circularity.**  (1) divergence ⇒ F: `pin_tends_to_one` + `heavy_of_never_drop`,
proved from the affine identity and `pow_step_bound` alone.  (2) F ⇒ contradiction:
**not achieved**, and the missing principle is named — a lower bound on the
accumulated valuation `Σ v₂(3y+1)` over some high window.  (3) neither implication
mentions termination.  (4) the independent principle would have to be a **normality**
statement for the 2-adic expansion of `x`; by Terras every finite valuation vector is
realised, so no finite computation can ever supply it.  Reported as step (1) in its
sharpest known form together with the exact shape of step (2) — not as a proof.

**Not a cycle detector** (`cycle_hypothesis_fails`, `bounded_orbit_hypothesis_fails`,
LEAN_PROVED): on a bounded orbit the hypothesis `2k ≤ c ≤ min orbit` is *unsatisfiable*
for `k ≥ 2`.  The device has the opposite polarity to every other filter here: it says
nothing whatever about cycles, so Class 4's `3x+d` cycle witnesses cannot touch it.
What it sees in an orbit that never returns (`deficit_of_growth`): a 2-adic deficit
`3^(a k)/2^k ≥ T^k(x)/(2x)` — **growing proportionally to the archimedean size**,
where on a cycle the same deficit is bounded.

## XVI — The product formula, answered exactly, and it is empty

*Which absolute values carry independent information.*

* `p = 2`: **expanding by exactly 2** on each branch (`|Tx − Ty|₂ = 2|x − y|₂`).  The
  whole topological degree lives here.  `v₂(x_n)` is not free data: it equals the
  length of the run of even steps beginning at `n` (verified, 1 245 989 orbit points,
  zero mismatches).  So the 2-adic size of an orbit point **is** a parity-word
  statistic — Class 3.
* `p = 3`: the odd branch has multiplier `3/2`, so `T` is a 3-adic **contraction** by
  `1/3`.  A contraction has no obstruction; this is `PAdicJoint.three_adic_free` in
  metric form.  Its one archimedean consequence is already in the repository
  (`Records.not_three_dvd_record`, `ThreeObstruction.orbit_not_three_dvd_of_neverDrops`):
  orbit points after an odd step avoid a residue class, tightening "a divergent orbit
  visits `[1,B]` at most `B+1` times" to `(2/3)B + O(1)`.  Useless as a filter, and
  recorded as such.
* `p ≥ 5`: both branches are affine with **unit** multipliers `1/2`, `3/2`, so `T` is a
  `p`-adic **isometry**.  No expansion, no contraction, no dynamics.
* `∞`: multiplier `1/2` or `3/2`.

**The product formula for the multiplier is satisfied step by step, identically.**
Odd step: `log2 (at 2) − log3 (at 3) + log(3/2) (at ∞) = 0`.  Even step:
`log2 − 0 − log2 = 0`.  Of course — the multipliers are the *rational numbers* `1/2`
and `3/2`, and every rational satisfies the product formula.  **Total information
content of the product formula for this map: zero.**  It is not a hard case; it is a
vacuous one.

And the sharp reason it cannot be repaired, which is the diagnosis this desk offers:

> A divergent orbit differs from an arbitrary heavy 2-adic word **only** by the
> integrality of the starting point.  Integrality is a condition at the places
> `p ≥ 3`.  Those are exactly the places where `T` is an isometry (or a contraction).
> **The places that certify integrality are precisely the places where the dynamics is
> trivial.**  That is why no product-formula argument can reach the divergence half.

Per the adversary's brief: the 3-adic side is empty, this is stated, and this branch
stops here.

## XVII — Valuations along the orbit, measured

* `v₃(x_n) = 0` for every `n` after the first odd step; `v₂(x_n)` = the current even
  run.  1 245 989 orbit points from all starts `< 20 000`, zero exceptions.
* The pin ratio `2^k·x_k/(3^(a k)·x)` equals `∏(1 + 1/(3x_i))` **exactly** (it is the
  same identity), measured at `x = 27, 703, 9663, 77671, 113383, 159487, 1027431,
  670617279`: maxima `1.199, 1.210, 1.113, 1.151, 1.108, 1.214, 1.235, 1.183`.  Even
  from small starts the coupling is already within 24 % of `1`.
* `pin_two` checked on 1 138 103 windows drawn from 400 random starts in `[10⁶,10⁷]`:
  zero violations.
* Syracuse budgets `M_K/K = Σv₂(3y+1)/K`: `1.7073 (27)`, `1.7419 (703)`,
  `1.7319 (1027431)`, `1.6649 (670617279)` — all **above** `log₂3 = 1.5850`, which is
  precisely why these orbits terminate.  A divergent orbit must hold this average
  below `1.5850` forever.  That single number is the whole divergence half.
* The observable is unbounded exactly on a divergent orbit and empirically grows only
  logarithmically otherwise: the longest window that is simultaneously never-dropping
  and above `2k` has mean `29.6 / 36.4 / 37.0 / 38.1 / 42.9` at scales
  `10⁶ … 10¹⁸` (60 samples each).  So a finite search sees `O(log x)` of it — the
  reason no computation will ever exhibit the filter failing.

## Failed attempts, with diagnosis

* **A genuinely nonlinear global height `H` with `H(T^k x) < H(x)`.**  Dead before
  writing: any such `H` restricted to the divergence half is, by `pin_ratio`, a
  function of `(word, x)` up to `1 + 1/j`, hence asymptotically a word statistic —
  Class 1/3.  Diagnostic 3 does not even need to be invoked.
* **Northcott / counting on the distinct orbit values.**  The foundational fact gives
  infinitely many distinct integers of bounded height *defect*, and the defect bound
  (`pin_two`) is what makes them distinct-but-indistinguishable: the S-unit lattice
  `3^a/2^k` is dense, so bounded defect bounds nothing.  Northcott needs finite fibres;
  here the fibre is the whole tail.
* **Baker / linear forms in logarithms.**  Applies to the *cycle* half, where the form
  `k log2 − a log3` must be **near zero**.  The divergence half needs the form to stay
  **large and positive** forever — an upper bound on a linear form's persistence, which
  is not a Diophantine statement at all.  Recorded as a permanent classification:
  *linear-forms methods are cycle-half tools by nature.*
* **S-unit equations.**  A cycle closes and produces an equation; a divergent orbit
  introduces one new free integer and one new relation at each step, so the system is
  underdetermined by exactly one degree of freedom forever.  Every classical finiteness
  theorem (Northcott, Siegel, Baker, S-unit) is a statement about *equations*.  This is
  the `Π⁰₁`/`Π⁰₂` split of `collatz_iff_halves` in Diophantine clothing, and it explains
  it: `Π⁰₁` = finitely refutable = equation-shaped.

---

# Round X — why the repository is lopsided

The round's objective was a divergence-half filter.  The first substantive answer is
not a filter but a diagnosis of why there isn't one, and it is sharp enough to reorient
the programme.

## The diagnosis

> **The divergence half is a SAFETY property and wants an INVARIANT.  A ranking
> certificate is sound *and complete* for the whole conjecture, so it can never isolate
> a half.  Termination machinery is liveness machinery.**

That is why a repository this good at *"no finite mechanism supports a cycle"* has
nothing aimed at *"no orbit escapes"*: the tools are pointed at the wrong property
class.  `barrier_complete` proves bounded inductive invariants are sound **and
complete** for the divergence half using no well-foundedness at all; `rank_iff_halting`
proves a ranking is equivalent to the whole conjecture.

## Section VII is unreachable as posed

`rank_target_collapses`: for a **deterministic unary** system on `ℕ`, a ranking valued
in *any* relation with no infinite descending chain exists **iff** one valued in
`(ℕ, <)` exists, iff every orbit halts.  Lexicographic products, ordinal notations,
multiset orders, tree embeddings, matrix orders — the entire hierarchy the brief lists
buys exactly nothing.  A transfinite rank pays off only when the transition relation
*branches*; here the descending chain a rank produces **is** the orbit, whose length is
already a natural number.

So "seek `R : State → W` with `W ≠ ℕ`" is a search for the whole conjecture, and **a
ranking is never a half-filter.**

## The WQO/WSTS family is refuted in one line

It was the right thing to try — the divergence half is literally "every orbit contains
a repetition", a Ramsey-flavoured finiteness statement.  But the WSTS principle *a
monotone map on a well-quasi-ordered space has bounded orbits* is **false**: successor
on `(ℕ, ≤)` is a WQO, strictly monotone, injective, unbounded.

**The gap, named:** Dickson, Higman and Kruskal deliver a *good pair* `xᵢ ⊑ xⱼ`.  The
divergence half needs an *equality* `xᵢ = xⱼ`.  The distance between `⊑` and `=` is the
entire content, and no choice of WQO closes it.

## Size-change termination dies to a new theorem

`mixed_block_self_loop`: for every pair of moduli `2^k, 3^l` and **every** block length
`L`, there is a genuine `n > 1` whose next `L` states are, at every intermediate time,
congruent to `n` at both moduli **and** strictly larger than `n`.  Witness
`n + 1 = 2^(k+2+L)·3^l·s`, whose first `L` steps form one odd run.

Reproduced exactly: `k < 5`, `l < 4`, `1 ≤ L ≤ 8`, `s ∈ {1,5,7}`, zero failures.

This strengthens `TransitionInvariant.exists_congruent_step` twice — one step becomes a
block of arbitrary length, and congruence coordinates become congruence **plus**
magnitude.  So the size-change graph over exactly the coordinates the brief lists
(`log₂ x`, `v₂`, `v₃`, odd-step count, residue complexity, scale distance) has a
multipath of arbitrary length whose entire arc matrix is non-decreasing: no strict arc
in an idempotent loop, hence no SCT, lexicographic, multiphase or disjunctive
certificate.

It also converges with Round IX from a new direction: SCT's arcs must be
*unconditional*, and Collatz's are conditional on the parity word, which Terras leaves
free.  What SCT is missing is exactly the word↔magnitude coupling Round IX named, and
`mixed_block_self_loop` is that gap made explicit as a self-loop.

## What survives, positively

`divergent_record_steps_odd`: along a divergent orbit, for every `N` there is `i ≥ N`
at which the running maximum jumps, the orbit strictly grows, and **the orbit value is
odd**.  The record ladder is carried by odd steps for ever.  Proved from unboundedness,
positivity and "the even branch halves" alone.  Confirmed over all `n < 200000`: all
**594234** record steps odd, mod-4 split 294421 / 299813 — so no finer congruence
restriction holds, and none was formalised.

`orbitMax` is the one genuinely asymptotic object available: non-decreasing, unbounded
exactly when the orbit is, every rung an actual orbit value, and **finite on the cycle
half** — so it is not a cycle detector in disguise.  Read against it, the three natural
coordinate kinds are a complete kill: congruence-definable freezes along the block
above; monotone-in-magnitude strictly increases along it; anti-monotone eventually
freezes on the record ladder.  A certificate needs infinitely many strict arcs on every
infinite run, and none of the three supplies them.

## Round X's objective is met: a divergence-half filter exists

Round IX Part VI named the missing object as *a refuting witness family for the
divergence half* — every filter the programme owned was a cycle witness, so a
divergence mechanism faced no filter at all and there was no way to tell a good one
from a vacuous one.  That object now exists.

> **`expStep x = 3x/2` (even), `(3x+1)/2` (odd).**

It **agrees with the Collatz map on every odd input**, satisfies the same affine law
`2^j f^j x = 3^j x + b` with the odd count **saturated** at `a = j`, is heavy at every
scale, and **every one of its orbits provably diverges** — trivially, since `3x/2 > x`
for `x > 0` and `(3x+1)/2 > x` for `x ≥ 1`, so every orbit strictly increases.  All
four properties verified: agreement on every odd input below `200001`, `b ≥ 0` at every
step from `1, 3, 7, 27, 1000, 99999`.

Hence the divergence-half analogue of `C(w,d) = d·C(w,1)`:

> **Any divergence mechanism whose proof uses only the affine law, the parity word,
> heaviness and positivity — without consuming `oddCount n j < j`, i.e. the even
> branch's contraction — proves a false statement.**

What separates the two maps is exactly that: over 30 steps the Collatz orbit of `27`
has odd count `21 < 30`, and of `703` has `20 < 30`, against `expStep`'s saturated
`30`.  ~~**The even branch's contraction is the whole of the divergence half.**~~

> **RETRACTED (Round XV).  That sentence is false, and I wrote it.**  Consuming
> `oddCount n j < j` is **necessary but nowhere near sufficient**.  Witness
> (`MixWitnessXV.lean`): `mixStep x = (3x+1)/2` for odd `x`, `x/2` for `x ≡ 6 (mod 8)`,
> `3x/2` otherwise.  It agrees with the accelerated Collatz map on **every odd input**
> (checked for every odd `x < 200001`), is positive, obeys the affine law, **contracts on
> the even branch** — the orbit of `6` is `6, 3, 5, 8` with `a = 2 < 3 = j` — and **every
> orbit still diverges**, `f³(x) > x` verified for all `x < 300000`.
>
> Worse for the framing: `expStep` is not the unique deformation but the **degenerate
> member of a continuum**.  Every subset `H ⊆ {x ≡ 6 (mod 8)}` gives a witness — the
> divergence proof needs only `H ⊆ {6 mod 8}`, since a halving forces `x/2 ≡ 3 (mod 4)`,
> which forces the next two steps odd, and `(1/2)(3/2)(3/2) = 9/8`.  `H = ∅` is exactly
> `expStep`.  Round XI's deformation theorem was about the `2×2` affine grid only and does
> not reach this class.
>
> The family's own limit, stated against itself: the `9/8`-per-three-steps device caps
> halving density at `1/3`, so no witness of this type has `a_j/j < 2/3 = 0.6667`, while
> `log₃2 = 0.63093` and Collatz sits near `0.5`.  So the family closes
> `a_j/j ∈ [0.89, 1]` (measured) and **cannot** close `(0.63093, 0.89)`.  That gap of
> `0.0357` is exactly the room the real theorem has to exploit.

Stated weakness, from the agent that built it: `3x+d` differs from `3x+1` in one
constant, whereas `expStep` differs on a whole branch, so this filter kills a coarser
class than the cycle filter does.  Narrowing it is the natural Round XI task, and it is
now sharply posed.

`CLOSURE.md` also gains **diagnostic 4**: a divergence-half filter must be *refuted by
a cycle*.  If a cycle satisfies it, it is capped by the cycle minimum exactly as by a
divergent minimum, hence it is the whole conjecture.  The worked example is the agent's
own first candidate, killed by itself: the never-drop certificate family is
`minNonDrop`, already proved equivalent to the conjecture.  The repair — require
*escaping a scale*, which a cycle cannot do — is what produced the filter.

### The escape record, and why it is a new object

`minEsc B` = least `m ≥ 1` whose orbit rises strictly above `B`.  Measured exhaustively
to `3·10⁶`: `minEsc(2^k) = 2^(0.57 k)` with observed exponents `0.591, 0.603, 0.568,
0.540, 0.577` at `k = 16, 20, 28, 32, 37` (witnesses `703, 4255, 60975, 159487,
2684647`).  That constant is **neither** `0.05004 = 1 − H(log₃2)` (Class 2) nor `0.585`.

Stronger evidence that it is not the frontier reindexed: **`1027431` — asset (a)'s
`L = 182` witness — and `1126015` set no excursion record at all.**  The divergence-half
record function is blind to the frontier witnesses, which is exactly what "the frontier
is a cycle-half asset only" predicts.

### Two more structural results

**The coupling vanishes on the divergence half too.**  Measured relative to a window's
own starting point, the coupling falls off like `1/x₀`: at window length 20 it is
`6.9e−2` from `27`, `2.2e−3` from `10³`, `2.9e−5` from `10⁶`, `8.4e−9` from `10⁹`.
Round IX found it collapses to a word invariant on the cycle half; on the divergence
half it tends to `0`.  **Both halves are asymptotically word statements** — the
structural reason every route in this programme lands in Classes 1–3.

(This is compatible with `Linearizing.coupling_monotone`, and the distinction matters:
that theorem concerns `r_j` from a *fixed* `n`, monotone up from `r_0 = 0`.  This is `r`
over a window normalised by *that window's own start*.  Different objects.)

**The product formula is empty, with a sharp reason.**  `p = 2` carries all the degree,
and `v₂` of an orbit point is a parity-word statistic (Class 3); `p = 3` has multiplier
`3/2` on the odd branch, so `T` is a 3-adic *contraction*; `p ≥ 5` has unit multipliers
on both branches, so `T` is a `p`-adic *isometry*.  The multiplier's product formula
holds step by step identically, because `1/2` and `3/2` are rational.

> **The places that certify integrality are precisely the places where the dynamics is
> trivial.**  That is why no product-formula argument reaches the divergence half.

Two permanent classifications follow.  **Baker / linear forms in logarithms is a
cycle-half tool by nature**: cycles need `k log 2 − a log 3` near zero, divergence needs
it large and positive forever, which is not a Diophantine statement.  And **S-unit
equations** are about *equations* — a cycle closes and yields one, a divergent orbit
adds one free integer and one relation per step and stays underdetermined forever.
That explains the `Π⁰₁`/`Π⁰₂` split rather than restating it.

## The scale ladder, and the death of the scale graph

The last agent built the divergence-half object the brief's sections V–VI asked for,
proved its first theorems, and then killed its own graph.

### The object

`Floor n i k := ∀ j ≥ i, 2^k ≤ T^j(n)`; the **rung** at scale `k` is the first index
where the floor takes hold.  It consumes a per-scale 2-adic bit (`x mod 2`), the
archimedean position `⌊log₂ x⌋`, and the **never-returns** condition — the last is what
no existing device has, and exactly what a cycle cannot supply.

`no_high_floor`: a bounded orbit has no floor above its bound, so a cycle has rungs at
only finitely many scales and the condition is **vacuous on cycles**.  That is
diagnostic 4 satisfied by construction.

**It is also the first mechanism tested against the new divergence-half filter, and it
passes.**  Checked branch by branch: `annulus_odd`, `entry_window` and the even case of
`coupling_bound` each become *false* for `expStep`, whose even step multiplies by `3/2`.
Every theorem in the file consumes `oddCount n j < j`.

### Theorems

* `annulus_odd` — every orbit value in `[2^k, 2^(k+1))` above a floor at `2^k` is
  **odd**.  The mechanism is exact and verified: an even `y` in that octave has
  `T(y) = y/2 < 2^k`, breaking the floor.
* `entry_window` — `2^k ≤ y_k` and `2·y_k < 3·2^k`: the rung sits in the **lower three
  quarters of its octave**, uniformly, at every scale.
* **`coupling_bound`** — `3·2^k·C_j ≤ a_j·(2^j·T^j x)`.  This is `Coupling.lean`'s `r`
  measured across one scale, and it **decays in the scale**.  The one theorem here with
  content, and the first place the `(word, magnitude)` fibre is actually consumed.
* `block_upper` / `block_lower` — a uniform two-sided window on the block multiplier at
  every rung, **with no averaging, no counting, and no `0.05004`**.  `block_lower` is
  the first theorem in this development whose proof genuinely needs `coupling_bound`.
* `climb` — `T^j(2^j E − 1) = 3^j E − 1`, verified for `E ∈ {1,3,5,7,11}`, `j < 14`.

*Measurement caveat, and it matters:* the hypothesis is a **permanent** floor, which
only a divergent orbit has, and Collatz has none known.  So every number reported is
measured on **ascent segments** as a proxy, not on the hypothesis.  The window
reproduces exactly — `u_k ∈ [1.00146, 1.47266)`, all inside the proved `[1, 1.5)` — but
the rung-odd count is convention-dependent: under my extraction it is `70/74`, not
`194/194`, because a local floor is not a permanent one.  The Lean theorem is
unaffected; the *statistics* are proxy statistics and should be labelled as such.

### The negative theorem, and it kills the brief's section VI

`no_finite_scale_invariant`: for **any** `state` function taking fewer than `N` values,
there is a single Collatz orbit and two scales `k₁ < k₂` on it, joined by a segment that
never falls below `2^(k₁)`, carrying the **same** symbol.  The witness is `climb`:
`2^M − 1` ascends about `M/2` scales monotonically — verified, 23 scales climbed in 40
steps from `2^40 − 1`, against `M/2 = 20`.

> So the scale-transition graph on a finite alphabet has a repeated vertex, hence a
> cycle, hence an infinite admissible path.  **Acyclicity is not merely insufficient —
> it is unattainable.**  A scale-based divergence proof cannot be a finite-state
> argument; its well-foundedness must come from an unbounded coordinate, and the only
> unbounded coordinates the ladder offers (`k`, `ℓ_k`) both *increase*.

### Renormalization closes negatively, by its own best result

`coupling_bound` gives `q_k → 0` (measured down to `7·10⁻⁹⁶`).  An earlier hope was
that this forces a `d`-uniform obstruction.  **It is backwards.**  `C` is where `d`
lives, so `q_k → 0` means the renormalized limit is `u_{k+1} = u_k · 3^(a_k)/2^(ℓ_k+1)`
on `[1, 3/2)` — a *pure multiplication with no additive part at all*.  The target window
has log-width `0.585`, `{a·log₂3 − ℓ}` is dense, and 2-adic realizability of any finite
block set is free by Terras.  So the renormalized system has **no fixed point, no
forbidden region, no contraction, no invariant cone, no unstable direction**.

It also explains Round IX's "no filter at all" dynamically: at the renormalized level
the `d`-filter is asymptotically blind, because `d` decays out.

The multiscale-drift hierarchy died the same way and was self-killed: `V_k := a_k log₂3
− ℓ_k − 1` telescopes exactly to `log₂ u_K − log₂ u_0 + O(q)`, hence is bounded in
`[−0.585, 0.585]` for free and carries nothing beyond `entry_window`.  **Any hierarchy
whose members telescope dies identically.**

---

# Round XI, Sections X / XI / XXX–XXXII — the product argument is the frontier, in other coordinates

*Algebra desk.  New file: `Collatz/Strategy/SegmentMonoid.lean` (compiles clean under
`lake env lean`, zero errors, zero warnings, no `sorry`, no `axiom`; `#print axioms`
reports `[propext, Quot.sound]` on all five headline theorems).*

The brief: multiply the local two-sided window `block_lower` / `block_upper` around a
hypothetical cycle into a global contradiction, using the exact closure identity
`1 + r_(i+k) = (1 + r_i)(1 + κ_(i,k))`.  **Answer: no, and the reason is exact, not a
gap in effort.**  What the product argument yields, at full strength, is the
repository's own frontier ledge list.

## 0.  The identity, and the form that matters

Re-verified in exact rationals (1708 `(i,k)` pairs, 12 genuine cycles of
`d = 1, 5, −1, 7, 13, 59`): zero violations of `1 + r_(i+k) = (1 + r_i)(1 + κ_(i,k))`.
`segment_compose` is that identity cleared of division, LEAN_PROVED.

The form that carries the content is not this one.  It is (COMPUTATIONAL, exact
rationals, 2568 windows, zero violations; and `MATHEMATICALLY_PROVED` by induction on
the affine law):

> **`1 + κ(x, k) = ∏_(t < k, x_t odd) (1 + d / (3·x_t))`**

so the cycle closure identity is

> **`2^L / 3^a = ∏_(x odd in the cycle) (1 + d / (3·x))`**   — exactly.

That is the whole of section XXXI.  Everything below is a bound on that product.

## 1.  Equality classification (task 1)

| bound | equality iff | near-equality shape |
|---|---|---|
| `coupling_bound` `3·2^k·C_j ≤ a_j·(2^j·x_j)` | `a_j = 0` (all-even window) only | never approached: it is the **first-order truncation** of `C_j/(2^j x_j) = 1 − 1/(1+κ)`, and `1 − ∏(1+u_t)^(−1) < Σ u_t ≤ a/(3·2^k)` is strict twice over for `a ≥ 1` |
| `floor_coupling` (new, floor `c` general) | same | same; strictly sharper than `coupling_bound` by the factor `c/2^k ∈ [1,2)` |
| `block_upper` `3^a < 3·2^l` | `a = 1, l = 0` — degenerate, no block | requires `y → 2^k` (but the rung is **odd**, `entry_odd`), `x_l → 3·2^k`, **and** `κ → 0` i.e. `a → 0`, which contradicts `3^a → 3·2^l`.  Self-defeating: **`block_upper` is never near-tight** |
| `block_lower` `(3m+2)·2^(l+2) < 9(m+1)·3^a` | never (`m → ∞` limit `4·2^l < 3·3^a`) | rung at `k` at the **top** of its window, `y = (3·2^k − 1)/2`; rung at `k+1` at the **bottom**, `x_l = 2^(k+1) + 1`; and `κ → 0`.  A rigid endpoint pair — the only equality case in the file with content |
| `cycle_frontier` (new) `3n(2^L − 3^a) ≤ a·2^L` | `a = 0` | measured tightness ratio on genuine cycles: `0.25 (d=5,n=187)`, `0.29 (d=13)`, `0.32 (d=59)`, `0.47 (d=7)`.  **Loose by a factor 2–4** |
| distinctness bound (below) | the `a` odd cycle points are **exactly** `n, n+2, …, n+2(a−1)` | attained, with equality, at `d=1 n=1`, `d=5 n=5`, `d=−1 n=5` |

The brief's hoped-for route *cycle ⇒ equality ⇒ rigid word ⇒ contradiction* fails at
the first arrow for every bound in `ScaleLadder`: **a cycle does not come near any of
them.**  The only bound a cycle drives to equality is the distinctness bound, and its
equality case (`n, n+2, …, n+2(a−1)` consecutive) is a genuine rigid-word condition —
but it is attained by three real cycles, so it is not contradictory.

## 2.  The segment monoid, and the death of the rank (task 2)

A **segment** is `(x, l)`, carrying `(word, l, a, start, multiplier 3^a/2^l, coupling κ,
endpoint T^l x)`.  Composition `(x,i)·(T^i x,k) = (x,i+k)` obeys three laws, of which
**two were already in the repository**:

* `AccumulatorArith.oddCount_add` — `a` additive;
* `AccumulatorArith.affineC_add` — `C(S₁S₂) = 3^(a₂)·C₁ + 2^(l₁)·C₂`;
* `SegmentMonoid.segment_compose` (new, LEAN_PROVED) — `1 + κ(S₁S₂) = (1+κ₁)(1+κ₂)`.

*The third is an algebraic tautology given `affine_exact`* — its Lean proof is three
rewrites and an AC-normalisation, with no dynamics.  This caps what it can deliver.

**There is no rank with a strict inequality.**  `rank_compose` (LEAN_PROVED): the
natural rank `R(S) = start/end` telescopes, so `R(S₁S₂) = R(S₁)·R(S₂)` **identically**.
Any rank respecting composition is a homomorphism out of the image of the segment
monoid in `(ℤ,+) × (ℤ,+) × (ℚ_(>0),×)`, and a homomorphism is never strictly
sub-multiplicative.  Task 2's target is unsatisfiable *inside the monoid*.  Strictness
can only live in a **bound** on `κ` that is itself not multiplicative — which is
exactly the distinctness bound of §3, and its measured value is zero (§4).

## 3.  The product argument (task 3): NO, with the exact reason

**Reason 1 — the hypothesis is empty.**  `block_lower`/`block_upper` need a `Floor` and
two consecutive rungs.  `ScaleLadder.no_high_floor`: a bounded orbit has no floor above
its bound.  A cycle therefore has **no rung above its own maximum**, and
`∏ L_i ≤ 1 ≤ ∏ U_i` is a product over an empty index set.  Confirmed empirically:
genuine rung extraction (floor holding for the *whole remaining orbit*) over 68 orbits
including `27, 703, 9663, 77671, 113383, 159487, 1027431, 670617279` and 60 random
starts in `[10⁶,10⁷]` produced **zero** rung-to-rung blocks.  This is the Round X
warning made concrete: `ScaleLadder`'s block statistics can only ever be ascent-segment
proxies.

**Reason 2 — even with the right window, the product is information-preserving.**
A cycle *does* have a permanent floor: its own minimum.  Two new theorems:

* `floor_coupling` (LEAN_PROVED) — `coupling_bound` with an arbitrary floor `c`, not a
  power of two.  Strictly sharper, and the only shape a cycle can feed.
* `cycle_frontier` (LEAN_PROVED) — instantiated at a cycle with minimum `n`:

> **`3 · n · (2^L − 3^a) ≤ a · 2^L`**

and `cycle_frontier_add` for the subtraction-free form.  This is the *complete* yield.
The reason it cannot be improved by multiplying more local bounds: **every local bound
here is a factor of one global product**, `2^L/3^a = ∏(1 + 1/(3x_t))`.  Multiplying the
local bounds reassembles that product with the local slack accumulated.  A product of
bounds on the factors of an identity can be *at best* as strong as the identity, never
stronger.  `prod L_i > 1` would need `3^a > 2^L`, which is anti-heaviness; `prod U_i < 1`
would need `2^L/3^a > ∏(upper bounds)`, i.e. a **lower** bound on the linear form
`L log2 − a log3` exceeding `a·log(1+1/(3n))` — a linear-forms-in-logarithms statement
(Baker), classified in Round X as a cycle-half transcendence tool, not local dynamics.

**Reason 3 — and it is decisive: the answer is already in the repository.**
Running the deterministic finite filter

> `0 < L·log2 − a·log3 ≤ −log(1 − a/(3n))`,  `n ≥ 1086465` (asset (a)),

over all `a ≤ 3·10⁶` leaves `2 091 774` pairs, whose first members are

> **`(2966, 4701), (3631, 5755), (4296, 6809), (4961, 7863), (5626, 8917), (5932, 9402),
> (6291, 9971), (6597, 10456), …`**

— **character-for-character the repository's own frontier ledge list**
(`RealizableFrontier6809.length_ge_6809`, the `4701 → 6809` staircase, and the ledge
multiples `(9402,5932) = 2·(4701,2966)` already recorded in Round III).  The product
argument is `RealizableFrontier6809` in multiplicative coordinates.  **Closed as a
duplicate.**

**Not a duplicate of the product formula.**  Per the hard constraint: `cycle_frontier`
uses the cycle **minimum** (endpoint/magnitude data), the **coupling**, and a floor —
none of it available to a word invariant.  Diagnostic 3 is passed decisively: the
`3x+d` version is `3nG ≤ d·a·2^L`, homogeneous of degree **one** in `d`, and the `d = 1`
statement is **false** on every genuine cycle checked
(`d=5 n=187`: `2 848 513 965 > 2 281 701 376`; also `d=5` at `5,19,23,347`, `d=7 n=5`,
`d=13 n=131`, `d=59 n=133,229`) while each satisfies its own `d`-form.  It is a real
`d = 1` asset — it is simply an asset the repository already owned.

## 4.  Distinctness: the one strict submultiplicativity, worth exactly zero

The `a` odd points of a cycle are **distinct** odd integers `≥ n`, so

> `2^L/3^a ≤ ∏_(j<a) (1 + 1/(3(n+2j)))`  — strictly better than `(1+1/(3n))^a`,

and this bound **is** strictly submultiplicative under segment composition (the second
segment must use larger denominators), supplying the strictness §2 showed the rank
cannot have.  Verified on all 12 genuine cycles; equality at `d=1 n=1`, `d=5 n=5`,
`d=−1 n=5`.

**Measured value at the frontier: zero.**  Over `a ≤ 3·10⁶`, distinctness cuts the
survivor count from `1 870 385` to `876 318` — a factor 2.13 in density — and moves the
**first survivor not at all**: still `(2966, 4701)`.  The reason is quantitative and
final: distinctness only bites when `a ≳ n`, and asset (a) forces `n ≥ 1086464` while
the frontier sits at `a ≈ 4296`, so `2a/n ≈ 0.008` and the bound agrees with the naive
one to first order.  *The one place strictness was available, it is worth a factor of
two in density and nothing at all in the frontier.*

## 5.  Ascent/descent balance (task 4) — closed in one line

Decompose the cycle into maximal ascent runs (odd steps) and descent runs (even steps).
Descent runs have `κ = 0` **exactly** (`affineC_even`), so the coupling is supported
entirely on ascent runs, and the closure identity reads
`3^a/2^L · ∏_i (1 + κ_i) = 1` with `κ_i` the ascent couplings.  This is the same
equation with the terms grouped: `Σ a_i = a`, `Σ(a_i + e_i) = L`, and the product over
ascents is the product over all odd points.  The decomposition adds a partition of the
index set and **no new inequality**, because `disc_append`/`affineC_add` make the data
additive along the word — CLOSURE.md diagnostic 1, applied to the ascent/descent
grouping.  Nothing survives.

## 6.  One positive by-product

`block_ratio_window` (LEAN_PROVED): from the two rung windows **alone** — no
accumulator, no coupling, no interior floor —

> `4·y < 3·T^l y`  and  `T^l y < 3·y`,  i.e. `4/3 < T^l y / y < 3`.

So the *ratio* half of the two-sided block window is unconditional geometry;
`coupling_bound` is spent only on transporting that ratio onto the word datum `3^a/2^l`.
This isolates precisely what the coupling machinery buys in `block_lower`, and it is
less than the file's header suggests.

## Failed attempts, with diagnosis

* **A strictly submultiplicative rank on the segment monoid.**  Dead by
  `rank_compose`: the composition law is an *identity*, and `R(S) = start/end`
  telescopes.  Diagnosis: the brief asked for a strict inequality where the structure
  supplies an equality; strictness cannot live in a homomorphism.
* **Multiplying `block_lower`/`block_upper` around a cycle.**  Dead by
  `no_high_floor` — the index set is empty.  Confirmed by an extraction over 68 orbits
  returning zero blocks.  Diagnosis: `ScaleLadder` is divergence-half by construction,
  exactly as its own header says; the Round X warning about proxy statistics is the
  same fact seen from the measurement side.
* **A second, non-telescoping multiplicative invariant of a segment.**  Every candidate
  built from `(l, a, C, start, end)` is a power product of `2^l`, `3^a`, `start`, `end`
  by `wC_inj` (diagnostic 2) plus the composition laws, hence telescopes.  Dead before
  writing.
* **Forcing `∏ U_i < 1` by a sharper per-block upper bound.**  Reduces to a lower bound
  on `L log2 − a log3`, i.e. Baker.  Round X already classified linear-forms methods as
  cycle-half tools; this is the same wall, reached from the multiplicative side.
* **Using the cycle *maximum* `M` as well as the minimum** (a second endpoint).  Gives
  `2^L/3^a ≥ ∏(1+1/(3M))^a`, a *lower* bound on the linear form of size `a/(3M)`.  With
  the spread bound `M/n > 2^474` at `(4701,2966)` this is smaller than the upper bound
  by a factor `2^474`, so the window `[a/(3M), a/(3n)]` is never empty.  Diagnosis: the
  spread is Class 1 and no `d`-free mechanism bounds it — the same barrier, reached
  from the two-endpoint side.

---

# Round XI, Sections XXI–XXIV — the fibre interaction, measured, and it is empty

*New file: `Collatz/Strategy/CoupledCycle.lean` (compiles clean, no `sorry`/`axiom`,
axiom footprint `[propext, Quot.sound]`).  The file is deliberately short: the
positive half of what I derived was already proved, in this same round, by
`SegmentMonoid`, and I deleted my duplicate rather than leave a second entry point.*

## The verdict on the central conditional

> **`G ∣ C` does not strengthen the coupling bound, and the reason is degeneracy, not
> difficulty: the coupling contains exactly the information `G ∣ C` contains.**

The bridge does exist and is a single inequality.  Generalise
`ScaleLadder.coupling_bound` from the floor `2 ^ k` to a free floor `c` — the
induction never uses that the floor is a power of two — apply it at the cycle
minimum, and substitute the cycle criterion:

> `3 · n · (2 ^ L − 3 ^ a) ≤ a · 2 ^ L`.

I derived this independently, then found it as `SegmentMonoid.cycle_frontier`
(with `SegmentMonoid.floor_coupling` the free-floor generalisation).  **Two
routes — the segment monoid and the scale-ladder coupling — converge on the same
inequality in the same round**, which is itself evidence that it is the unique
content available here.

COMPUTATIONAL, exact integers, `a = ⌊L·log₃2⌋` (the only `a` that can pass: a smaller
`a` enlarges the gap and shrinks the count), asset (a) `n ≥ 1 086 464`:

| bound | constant | first surviving `(L, a)` |
|---|---|---|
| `CycleProduct.cycle_min_bound` | `n·g ≤ 2a·3^a` | `(1539, 971)` |
| `coupling_bound` at a power-of-two floor `2^k ≤ n` | `3·2^k·g ≤ a·2^L` | `(2593, 1636)` |
| free floor `c = n` | `3·n·g ≤ a·2^L` | `(4701, 2966)` |

A threefold gain in reach over the product method, from nothing but dropping the
rounding of `n` down to `2 ^ k` and improving `CycleProduct`'s linearisation constant.
It reproduces `RealizableBound.length_ge_4701` and stops strictly below
`RealizableFrontier6809`.  **The bridge adds no frontier.**

## The arrow that fails, named exactly

The proposed loop was `G ∣ C ⇒ restricted ordering ⇒ stronger coupling ⇒ …`.  **It
fails at arrow 2, and it fails identically rather than marginally.**

Every bound in the table uses exactly one inequality about orbit values, `n ≤ x_t`.
The obvious sharpening is `FloorSchedule.pin_lower`, `3^(A t)·n ≤ 2^t·x_t`, which is
strictly better at every heavy prefix.  Substitute it into the exact closure identity
`∏_t (1 + 1/(3x_t)) = 2^L/3^a`:

`Σ_t 2^t / (3·3^(A t)·n) = C/(3^a·n) = g/3^a`,

because `Σ_t 3^(a−1−A t)·2^t` **is** `C`, the closed form of `affineC`.  The sharpened
inequality is therefore `log(1 + g/3^a) ≤ g/3^a` — a tautology.
MATHEMATICALLY_PROVED; verified in exact rationals on eleven genuine cycles of `3x+d`
for `d = 1, 5, 7, 13, 59, −1`, equality in every case with no rounding.

The structural reason, which is the round's main negative result:

> `2^t·x_t = 3^(A t)·n + C_t` is an **identity**.  Every orbit value of a cycle is an
> exact function of `(word, n)`.  So every lower bound on `x_t` is either the identity
> itself — which returns the cycle equation and nothing else — or the external input
> `x_t ≥ n`.  **There is no third source.**

It is already visible in Lean, in this round's own work: `CouplingNormal.cycle_total_coupling`
("the total coupling around a cycle is `2^L/3^a`") is discharged by
`exact (cycle_affine h).symm`.  The exact closure product, which the brief nominated as
the best lever, **is** the cycle equation — deterministic, finite, and carrying zero
information beyond `G ∣ C`.

## The ordering restriction `G ∣ C` imposes — weaker than heaviness

`CoupledCycle.prefix_gap` (LEAN_PROVED) is the exact ordering consequence, read at the
cycle minimum: for every prefix `j`,

`2^j·C ≤ 3^(A j)·C + g·C_j`,  equivalently  `C_j/C ≥ (2^j − 3^(A j))/g`.

`prefix_gap_of_heavy` (LEAN_PROVED) derives the *same conclusion* from heaviness
`2^j ≤ 3^(A j)` alone, with **no cycle hypothesis, no `g`, no `n`** — the right-hand
side already dominates.  `prefix_gap_at_L` shows the one prefix where heaviness is
unavailable (`j = L`, where `3^a < 2^L` is the ledge) is an *equality*: the cycle
equation restated.  Measured: the minimum's word is heavy at every proper prefix on all
eleven genuine cycles.  Hence

> **`G ∣ C` restricts the ordered odd-step times `t₁ < ⋯ < t_a` strictly *less* than
> ordinary heaviness does.**

That closes Round VIII's localisation from the other side.  Round VIII asked whether the
coupling machinery could finally consume the ordering; the answer is that there is
nothing left to consume, because the divisibility condition does not touch it.

## `G ∣ C ⇒ expStep contradiction`: true, and vacuous

`expStep_no_ledge` / `oddCount_lt_of_ledge` (LEAN_PROVED, two lines each).  A saturated
window (`oddCount x j = j`, the defining property of `expStep`) has `2^j < 3^j` for
`j ≥ 1`, so the cycle criterion's hypothesis `3^a < 2^L` is **unsatisfiable**.  The
requested statement holds and certifies nothing: the ledge condition consumes
`oddCount < j` — the even branch's contraction — in its very statement.

> **Dual to `CLOSURE.md` diagnostic 4:** a *cycle*-half mechanism passes the Round X
> divergence filter automatically, because `G > 0` is already the negation of
> saturation.  The filter is one-directional and must not be cited as evidence for
> cycle-half work.

## Failed attempts, with diagnosis

* **Sharpening the coupling with the ordering bound `x_t ≥ n·3^(A t)/2^t`.**  Returns
  `log(1+u) ≤ u`.  Diagnosis above: the bound is the identity, and feeding an identity
  into itself is a fixed point.  This is the round's cleanest kill and generalises —
  *any* proposed improvement must supply a lower bound on `x_t` that is not a
  consequence of `affine_exact`, and on a cycle only `x_t ≥ n` qualifies.
* **The prefix chain `G·C_j ≥ (2^j − 3^(A j))·C` as `L` new constraints.**  All but one
  are implied by heaviness (`prefix_gap_of_heavy`), and the exception is the cycle
  equation.  Diagnosis: the chain is degree-0 homogeneous under `C ↦ d·C` — both sides
  scale by `d` — so `CLOSURE.md` diagnostic 3 predicted it before it was measured, and
  the genuine `3x+5` and `3x+13` cycles satisfy every member.
* **Reading `G ∣ C` as a restriction on the word set, then measuring the coupling on
  the survivors.**  Not measurable: at every ledge pair inside computation range the
  solution set of `G ∣ C` is *empty* (a solution is a genuine cycle by
  `CycleCriterion`, and `C/g ≤ 2^L/g` puts it inside the verified range).  Diagnosis:
  the fibre the brief asked me to interact with has no computable sample points, which
  is why no measurement in this programme has ever seen it.
* **Hoping the free-floor gain compounds.**  It does not: `c = n` is the largest legal
  floor, so the factor of two recovered from `2^k` is the whole of the gain, once.
* **Applying `GlobalHeight.pin_explicit` at a cycle minimum.**  It *does* apply — the
  hypothesis `∀ i, c ≤ T^i(x)` is satisfied at `c = x = n`, and only the strengthened
  form `2k ≤ c` used by `cycle_hypothesis_fails` is unsatisfiable.  So Round X's
  "the device says nothing whatever about cycles" is an over-claim; but what it then
  says is `n·2^L ≤ (n+2a)·3^a`, which is `CycleProduct.cycle_min_bound` with the same
  constant.  Correction recorded; no new content.

## Where Round XI, XXI–XXIV, leaves it

The bridge between the halves was built, and it is one inequality wide.  Its width is
fixed by a fact that no amount of machinery moves: **on a cycle the orbit is an exact
function of `(word, minimum)`, so the coupling and `G ∣ C` are the same statement in
two coordinate systems.**  The only external input is `x_t ≥ n`, i.e. asset (a), and it
has now been spent three ways — `CycleProduct` (1539), the power-of-two floor (2593),
the free floor (4701) — all short of the realizability frontier at 6809, which spends
the same asset better.

The honest one-line summary: **the fibre interaction the programme has been missing is
missing because it is empty.**

---

# Round XI, Sections III / IV / V / XIV / XVII / XXXVII — the fibre is rank one, and the residual is the accumulator

*Scale desk.  New file: `Collatz/Strategy/ScaleFibre.lean` (compiles clean, zero errors,
zero warnings, no `sorry`/`axiom`; axiom audit shows `propext, Quot.sound` only).*

**Verdict on the round's central question: the decoupling is real, and it is an
identity rather than a limit.**  I set out to break it and could not, for a reason that
is one line long once seen.

## 1.  The exact expansion — there is no expansion (LEAN_PROVED)

Fix a word `w` of length `j`.  `C_j` and `A_j` are functions of `n mod 2^j` alone
(`NewModels.class_iff_count_accum`, already in the repository).  Hence on the fibre over
`w`, the affine law `2^j·x_j = 3^(A_j)·n + C_j` gives

> **`kappa(w, n) = r_j(n) = E(w) / n`  exactly, with `E(w) = C_j(w,d) / 3^(A_j)`.**

Not `kappa_inf(w) + E(w)/n + O(n^{-2})`.  There is **no** `kappa_inf` (the limit is `0`)
and **no** `n^{-2}` term (the remainder is identically zero).  As a function of `n` on
the fibre, `kappa` is: strictly decreasing, strictly convex, positive for `d > 0`,
homogeneous of degree `−1`, and never eventually constant.  Cleared of division this is
`ScaleFibre.fibre_affine`:

    y·(2^j·x_j(x)) = x·(2^j·x_j(y)) + (y − x)·C_j        (x ≤ y, same word)

— the deviation between two magnitudes carrying the same word is a **pure word factor
times a pure magnitude factor**.  The `(word, magnitude)` fibre is **exactly rank one**.
`fibre_second_difference` records the corollary that makes the point unarguable: an
affine function has no second difference, so no rescaling by any power of `n`, any
`log n`, or any discrete difference can produce a *new* limit.  Section V's search for a
nontrivial rescaling is therefore answered negatively **by derivation, not by trial** —
which is what the brief asked for.

## 2.  The correction term and its sign (LEAN_PROVED for `d = 1`; MATHEMATICALLY_PROVED in `d`)

Since `kappa` itself is the correction, the interesting object is the *first place the
correction changes a discrete fact*.  For `i < j`,

    2^(i+j)·(x_i − x_j) = n·D + (2^j·C_i − 2^i·C_j),    D := 2^j·3^(A_i) − 2^i·3^(A_j).

`D` is the pure word term; the bracket is the **explicit finite-scale correction**.  Its
sign is `sign(d)` and **nothing else about the word enters it** — because `C` is
monotone along the window (`Linearizing.coupling_monotone`) and `C(w,d) = d·C(w,1)`.
So the answer to section III's sign question is a clean negative: the sign of
`Delta(w,n)` is *not* determined by the first odd step, the last odd step, run parity,
odd-step ordering, the minimum point, the maximum point, or the scale.  It is `sign(d)`,
full stop, and it is `0` exactly when `a = 0`.

**`ScaleFibre.order_word_determined`** turns the correction into an explicit threshold:
if `2^i·C_j ≤ n·D` then the word decides the comparison.  Replacing `C_j` by the
positional bound `affineC_le` gives the **word-only** threshold
`N(w; i, j) = 2^(i+j−A_j)·3^(A_j) / D` (`order_word_determined_shape`), and at `i = 0`:

> **`ScaleFibre.drop_of_scale`** — if `3^a ≤ 2^L` and `2^(L−a)·3^a ≤ n·(2^L − 3^a)`
> then `x_L ≤ n`.

`two_pow_le_shape` shows `N(w) ≥ 2^L/G` always.  So **the threshold is large exactly when
`G` is small — at the ledges, and nowhere else.**  All residual two-variable content is
concentrated on the frontier, which is a mapped Class 1/Class 3 asset.

COMPUTATIONAL: `drop_of_scale`'s hypothesis was met 119 274 times over `L ≤ 44`,
`n < 4000`, with zero violations.  Over all residues mod `2^L`, the word already decides
the whole-window comparison at the *minimal* admissible magnitude for **80.4 % / 89.3 %
/ 86.8 %** of residues at `L = 12 / 16 / 20`.

## 3.  Ordering-sensitivity: YES, and worthless (LEAN_PROVED)

`E(w) = C/3^a = Σ_{i=1..a} 2^(t_i)/3^i` over Round VIII's ordered odd times
`t_1 < ⋯ < t_a`, so it is manifestly ordering-sensitive.  **`residual_injective`** makes
that sharp: at fixed `(L, a)`, `E` **determines the word**.  This is the strongest
possible ordering-sensitivity — and it is exactly why it is worth nothing.  `E` is a
bijective relabelling of `affineC`, hence determined by `(L, a, C, G)`, hence Class 3 by
`CLOSURE.md` diagnostic 2.  *The hoped-for reconnection of the ordered-times programme
to the coupling machinery exists and is an isomorphism, not a bridge.*  I record this as
the death of my own preferred architecture for the round.

## 4.  The residual, named

> **The first nonzero piece of information that survives after the coupling disappears
> is `E(w) = C(w,d)/3^(a)` — the accumulator itself, in `3`-adic normalisation.**

It is attained at *every* `n`, not in a limit; the correct rescaling is `n·kappa` and no
other; and it is Class 3.  The round's question "what survives the coupling" therefore
has the answer *nothing new*: the residual is the object the development started with.

## 5.  `d = 1`'s extremal behaviour, with its algebraic source

The threshold at which the word takes over scales **exactly linearly in `|d|`**:
`N(w; i, j; d) = |d|·N(w; i, j; 1)`, because the numerator is `d`-homogeneous of degree
`1` and the denominator `D` is `d`-free.  Hence

> **`d = ±1` minimise the set of magnitudes at which the word fails to decide, and among
> `d > 0` the minimiser is unique at `d = 1`.**  MATHEMATICALLY_PROVED.

COMPUTATIONAL confirmation (`L = 40`, all `n < 2·10^5`, all pairs `i < j`): violations of
the word-predicted order number **35 512 (`d = 1`) < 37 450 (`d = −1`) < 65 973
(`d = 5`) < 79 061 (`d = 7`)** — monotone in `|d|` on the positive side, exactly as the
`|d|`-linear threshold predicts.  So `3x + 1` is the **least-coupled** member of the
family: the case in which the parity word dominates the magnitude most completely.  That
is a positive, exact statement of why `d = 1` is hardest here, and it requires no
uniformity in `d`.

A second, sharper `d`-discriminator fell out and is worth recording separately, because
it is a two-variable fact that reduces to a one-variable one:

> **On any cycle of `3x+d`, `sign(2^L − 3^a) = sign(d)`.**  Immediate from
> `G·n = C_L = d·C_L(w,1)` with `C_L(w,1) > 0` and `n > 0`.  So *every* cycle of `3x+d`
> is **light** for `d > 0` and **heavy** for `d < 0`.  Checked: `d = 1` at `n = 1`
> (`(L,a) = (2,1)`, `G = 1`); `d = −1` at `n = 1` (`(1,1)`, `3 > 2`), `n = 5`
> (`(3,2)`, `9 > 8`), `n = 17` (`(11,7)`, `2187 > 2048`).

This is the exact source of a measurement that first looked like a `d = 1` miracle and
is not one.  A window drawn from inside a *heavy* cycle violates the word-predicted
order at every length, and the violation count grows linearly in `L`; a window drawn
from inside a *light* cycle produces a **tie** (`x_L = n`), which is not a violation.
`d = 1`'s only cycle is light, so it contributes ties; `d = −1`'s cycles are all heavy,
so they contribute violations without bound.  Reported because I initially recorded
"`d = 1` has zero order violations at `L = 10, 20, 30`" and it was an artefact of the
`L` window — corrected here by the same computation run at `L = 40`.

## Failed attempts, with diagnosis

* **Break the decoupling by finding an `n^{-2}` term.**  Dead by `fibre_affine`: the
  fibre map is affine, so the second difference vanishes identically.  There is no
  higher-order term to find, at any rescaling.  This kills sections V and XXXVII as
  posed, by derivation.
* **The profile order type as a genuinely two-variable invariant.**  This was my best
  candidate and it is the one worth reporting.  The order type of `x_0, …, x_L` *is*
  magnitude-dependent, and the flip thresholds are explicit rationals.  But every
  threshold is a **phantom**: the threshold for the pair `(i, j)` is exactly the phantom
  `rho(w_{i..j}) = C_sub/G_sub` of the sub-window, evaluated against `x_i` — verified in
  exact rationals over 200 random `(n, L ≤ 18)` and all `L(L+1)/2` pairs, zero
  mismatches.  So the family of thresholds is `PhantomMediant.lean`'s object applied to
  every sub-window, and `PhantomMediant.localisation` makes the comparison a tautology:
  `rho − x_i = 2^(L_sub)·(x_j − x_i)/G_sub`, so `sign(x_i − rho)` *is* `sign(x_i − x_j)`
  times `sign(G_sub)`.  **The threshold does not predict the order; it restates it.**
  Duplication caught before it was written into Lean.
* **Hoping the order type stabilises at every admissible magnitude.**  Refuted by the
  tail: once an orbit reaches the trivial cycle, `x_i ∈ {1,2}` while the word factor
  `3^(A_i)/2^i` keeps moving, so all late pairs violate.  Correct diagnosis: the
  threshold in `order_word_determined` is a bound on the **local** magnitude `x_i`, not
  on `n`, and "the orbit's local magnitude stays above `N(w)`" is the never-drop
  condition — i.e. the conjecture.  Recorded as an instance of `CLOSURE.md` diagnostic 4
  reached from the cycle side.
* **`E(w)` as a bridge from Round VIII's ordered times to the coupling.**  It is an
  isomorphism onto `C`, not a bridge (`residual_injective`).  Killed by diagnostic 2.

## What Round XI's fibre section leaves

One sentence, and it is a closure statement rather than a lead:

> **There is no two-variable information in the `(word, magnitude)` fibre.  The fibre is
> exactly affine over the word, the coupling is exactly `E(w)/n`, the residual is `C/3^a`,
> and the only magnitude-dependent discrete datum — the profile order type — has flip
> thresholds that are the sub-window phantoms, hence restate the comparison they were
> meant to predict.**

The one thing that is *not* closed by this: the threshold `N(w) ≥ 2^L/G` says the residual
freedom is bounded below by the reciprocal gap.  A mechanism that could exploit the fibre
would have to live entirely at `G` small — i.e. it would be a frontier mechanism, and the
frontier is a `d`-free Class 1/3 asset already mapped by Round VIII.  That is the exact
price of the decoupling, stated as an inequality rather than as a hope.

---

# Round XI — the deliverable.  **CORRECTED**: see the postscript

*The section below was written before the adversary reported.  Its verdict survives but
**its central reason does not** — `A`, `B` and `C` rest on a quantifier-order fallacy.
Read the postscript "The decoupling claim was wrong; the closure is not" before citing
anything here.*

# Round XI — the deliverable.  Outcome B: the decoupling is real

The round asked: is there genuinely two-variable information left in the `(word,
magnitude)` fibre?  **No — and not merely in a limit.  It is an identity.**

## A.  The coupling theorem

`C_j` and `A_j` depend only on `n mod 2^j` (Terras, both directions already proved).
So on the fibre over a fixed word they are *constants*, and

> **`κ(w,n) = E(w) / n`  exactly**,  with  `E(w) = C(w,d) / 3^(A_j)`.

Verified: `E(w)` is constant on every residue class mod `2^10` tested.  There is no
`κ_∞` (the limit is `0`), no `n^(−2)` term, and the remainder is **identically zero**.
`ScaleFibre.fibre_affine` is this cleared of division.  **The fibre is exactly rank
one.**

## B.  The asymptotic decomposition

`κ(w,n) = 0 + E(w)/n`, exact at every `n`, monotone decreasing, strictly convex,
degree `−1` homogeneous.  An affine map has no second difference, so **no rescaling by
`n^k`, `log n`, or any discrete difference produces a new limit** — section XVII is
closed by derivation rather than by search.

## C.  The residual

`E(w) = C(w,d)/3^a` — the accumulator in 3-adic normalisation.  Attained at every `n`,
not in a limit.  **Nothing new survives the coupling.**  This sharpens Round IX's
`r_j = (d/n)·W_j(word)` to the statement that the *whole* fibre is that product.

## D.  expStep, classified — and it cannot be narrowed

The minimal separating fact is one affine inequality with no word structure:
`3^a ≤ C + 2^L` (i.e. `C ≥ −G`) is Collatz-true and expStep-false, and its survivor
class is **one word**.  It comes from two exact telescopes, `C + 2^L = D + 3^a` against
`B + E + 2^L = 3^L`, whose sign asymmetry is the whole content of the filter.

Survivor class: **`B(w) = C(w) ⟺ w avoids the factor `10`**, i.e. `E_L = 0*1*` —
cardinality `L+1`, entropy `0`, a 2-state DFA, and **rank one** (`C = 2^m(3^p − 2^p)`),
so the coupling on survivors is not two-variable either.  Verified for all words
`L ≤ 12`.

**Concatenation closure: DISPROVED.**  `uv ∈ E ⟺ u has no odd letter or v has no even
letter`; only `L+K+1` of `(L+1)(K+1)` pairs compose.  The obstruction is the factor
`10` — an even step following an odd one.  Witness: `[1]` and `[0]` both survive,
`10` has `C = 1` but `B = 3`.  So this is **not** the earlier sieve failure repeating:
the safe class does not concatenate.

**And the filter cannot be narrowed by changing the witness.**  Writing a step as
`2f(x) = m(x)·x + c(x)`, there are exactly two deformation coordinates — deform `c` on
odd inputs (`3x+d`, the cycle filter) or deform `m` on even inputs (`1 ↦ 3`, expStep).
Of the four `(m_even, m_odd)` corners only `(3,3)` grows.  **expStep is the unique
divergent corner, so its blind spot is intrinsic.**

## E.  block_lower around a cycle: no

Empty index set (a cycle has no rung above its maximum; genuine extraction over 68
orbits gives zero rung-to-rung blocks), the segment rank telescopes so no strictly
submultiplicative rank exists, and the surviving product argument **is
`RealizableFrontier6809` in multiplicative coordinates** — its filter reproduces the
repo's own ledge ladder character for character.

## F.  The cycle/divergence bridge: no, and worse than no

`G | C` restricts the ordered times **strictly less** than ordinary heaviness does:
`prefix_gap_of_heavy` derives the same conclusion from `2^j ≤ 3^(A j)` alone, with no
cycle hypothesis.  The self-strengthening loop of section XXIV fails at arrow 2 and
fails *identically* — the sharpened inequality collapses to `log(1+u) ≤ u`, verified as
an equality on eleven genuine cycles, because `Σ_t 3^(a−1−A_t) 2^t` **is** `C`.

`G|C ⇒ expStep contradiction` is **true and vacuous**: saturation gives `2^j < 3^j`, so
the cycle criterion's hypothesis `3^a < 2^L` is unsatisfiable.  `G > 0` *is* the
negation of saturation, so **the two soundness filters are orthogonal** — their refuted
classes do not intersect, and neither may be cited as evidence for the other's half.

## G.  Ordering: sensitive, and worthless

`E(w) = Σ_i 2^(t_i)/3^i` over Round VIII's ordered times — and at fixed `(L,a)` it
**determines the word**.  Maximal ordering-sensitivity is bijective relabelling, hence
Class 3 by diagnostic 2.  **The hoped-for bridge to the ordered-times programme is an
isomorphism, not a bridge.**  That kills the round's preferred architecture.

## H.  Product route: stays closed.

## I.  The single remaining lemma, and why it cannot be a verified-range extension

What survives is one inequality: `3nG ≤ a·2^L`, so a ledge pair dies iff
`G/2^L > a/(3V)` with `V` the verified range.  But `G/2^L ≈ E·ln 2` with
`E = ⌈a log₂3⌉ − a log₂3 ∈ (0,1)`, so the **left side is bounded by `ln 2`** while the
**right side grows linearly in `a`**.  Hence the filter is vacuous for

> `a > 3V·ln 2 = 2 259 238` at the current `V`,

and **no fixed verified range can close the ledge** — it can only advance the frontier
one pair at a time, at `Θ(L)` cost each.  That is Round IX's ω-rule finding arriving
from the coupling side.

At the current pairs the margins are `G/2^L = 8.47·10^(−4)` against `a/(3V) =
9.10·10^(−4)` at `(4701,2966)`, and `7.60·10^(−4)` against `1.32·10^(−3)` at
`(6809,4296)` — the survivors are exactly the pairs with anomalously small `E`, i.e.
the record ladder, which is why the filter reproduces it.

> **The single remaining lemma is a lower bound on `L log 2 − a log 3` of size `≳ a/V`
> uniform in `a`.  It is false as stated (the left side is `< 1`, the right grows), so
> the coupling route cannot close the cycle half at all.**

## Verdict

Outcome B of section XXXVI, established rather than suspected.  The coupling route is
**closed**, with a proved reason: the fibre is rank one and the residual is word-only.
The programme returns to the cycle-side ordering problem — and now knows, with a
theorem rather than a hunch, that no coupling-based device can supply the missing
contradiction.

---

# Round XI, adversary — the decoupling theorem: true at fixed window, false in the joint limit

*New file: `Collatz/Strategy/CouplingDecay.lean` (compiles clean under
`lake env lean`, zero errors, zero warnings, no `sorry`/`axiom`; not yet imported into
`Collatz.lean`, which this desk does not edit).*

The brief asked me to **prove the coupling programme doomed**: to establish
`lim_{n→∞} κ(w,n) = κ_∞(w)` with a rate strong enough that no finite-scale accumulation
can matter.  The attempt fails, and the failure is sharp enough to be the round's
answer.

## The master identity — the coupling is the spread, exactly

Read the affine law multiplicatively.  On an even step `2^(j+1) x_(j+1) = 2^j x_j`;
on an odd step `2^(j+1) x_(j+1) = 2^j (3 x_j + 1)` (`step_even`, `step_odd`,
LEAN_PROVED).  Dividing by `3^(A j) n`:

> **`1 + r_j  =  2^j x_j / (3^(A j) n)  =  ∏ over odd steps i<j of (1 + d/(3 x_i))`.**

COMPUTATIONAL, exact rationals, zero mismatches at every step of
`(n,d) = (27,1), (703,1), (9663,1), (187,5), (17,−1), (229,59), (5,7), (131,13)`.
(The same product identity was reached independently this round by the segment-monoid
desk as `2^L/3^a = ∏(1 + 1/(3x_t))`; the two derivations agree.)

Taking logarithms:

> **`log₂(1 + r_j) = log₂(x_j/n) − (A_j·log₂3 − j)`.**

The accumulated coupling **is** the spread, minus a pure word quantity.  So "bound the
accumulation" and "solve the archimedean tracking problem" are the same sentence, and
the whole coupling family is **Class 1 by an exact identity, not by an asymptotic
argument**.  A decay estimate can neither kill the route nor advance it.

## Why the decoupling theorem cannot be proved: the quantifier order

`ScaleFibre.lean` proves the theorem in the form `r_j(n) = E(w)/n` with
`E(w) = C_j/3^(A_j)`, exactly, on the fibre over a fixed word.  **That statement is
Terras**, not decay: `C_j` and `A_j` are functions of `n mod 2^j`, so the coupling is
trivially a word constant over the fibre.  The window length `j` is held fixed while
`n → ∞`, and `E` is unbounded in `j` — `Linearizing.coupling_monotone` makes `r_j`
increase in `j`, hence `E(w_j) = n·r_j` increase too.  Along an actual orbit `j` grows
with `n`, and then (COMPUTATIONAL, exact integers, `j` = full orbit length):

| `n` | `L` | `a` | `E(w)` | `E(w)/n` |
|---|---|---|---|---|
| `27` | 70 | 41 | `5.3689` | `0.19885` |
| `993` | 61 | 32 | `251.37` | `0.25314` |
| `10⁶+1` | 77 | 36 | `6.802e3` | `0.00680` |
| `10⁹+7` | 111 | 51 | `2.0544e8` | `0.20544` |
| `10¹²+39` | 140 | 63 | `2.1776e11` | `0.21776` |

`E(w)` scales **linearly in `n`**: the `1/n` is cancelled exactly, and the full-window
coupling sits at `≈ 0.2` at every scale instead of tending to `0`.  **The two limits do
not commute, and the coupling programme only ever lived in the joint one.**

> **Verdict.  The decoupling theorem is true at fixed window length, where it is
> Terras, and false in the joint limit, where it is the whole problem.  The negative
> result the brief asked for does not exist.**

## The `1/x₀` rate is conditional, and Round X's own four numbers do not show it

The honest rate is governed by the window **minimum**, not its start.  `window_bound`
(LEAN_PROVED): if every point strictly inside the window is `≥ c`, then
`(2^k x_k)·(3c)^a ≤ (3^a x)·(3c+1)^a`, i.e. `κ ≤ (1+1/(3c))^a − 1`.  Unconditionally
`orbit_floor` (LEAN_PROVED) gives only `x ≤ 2^k·T^k x`, so the available floor is
`x₀/2^k` and the uniform bound degrades to `a·2^k/(3x₀)`.  **The loss is attained:**

> **`x₀ = 1365`, `k = 20`: `κ = 716881/331695 = 2.16127` exactly.**  The window minimum
> is `1`; `a/(3x₀) = 0.00122`.  The claimed rate is wrong by a factor of `1770`, and
> `κ` is not small — it exceeds `2`.

Round X's four numbers (`6.9e−2` at `27`, `2.2e−3` at `10³`, `2.9e−5` at `10⁶`,
`8.4e−9` at `10⁹`) do not exhibit a `1/x₀` law on their own terms: the ratios are
`31, 76, 3452` against magnitude ratios `37, 1000, 1000`.  Re-measured (window length
20 Terras steps, 400 random starts per scale): the `27` value reproduces exactly, the
*medians* are `1.06e−2 / 9.71e−6 / 1.07e−8` and the *maxima* are `2.16 / 1.37e−3 /
1.42e−5`.  The mean behaves like `1/x₀`; the supremum does not, and a decoupling
theorem needs the supremum.  `ScaleLadder.coupling_bound` is unaffected — it carries
the floor as a hypothesis and is correct.

## Per-window decay does not imply summable accumulation — a cycle refutes the inference

`cycle_coupling_period` (LEAN_PROVED): around `q` periods of a cycle,
`3^(A_(Lq))·n + C_(Lq) = 2^(Lq)·n`, so `1 + r_(Lq) = (2^L/3^a)^q → ∞`, while every
period's own `κ` is bounded by `a/(3·min)` with `min` the cycle minimum, a fixed
number.  `trivial_cycle_coupling` (LEAN_PROVED) is the concrete case:
`affineC (2q) 1 + 3^q = 4^q`, verified for `q < 40`.  The aggregation law is a
**product**, so summability of `Σκ = Σ 1/(3x_i)` is a *growth hypothesis on the orbit*
— it holds iff the orbit grows faster than linearly in its odd-step index — and is
strictly stronger than divergence.  It is not available for any orbit.

## What survives, and it is the repair: the coupling lives at the bottom

* **The total accumulation is bounded by a universal constant.**  Exhaustively for all
  odd `n < 10⁶`, and for 300 random `n` in each of `10⁶ … 10¹²¹`, the total
  `log(1+r) ≤ 0.2299545`, attained at `n = 993` (**correction:** `1 + r = 1.2531421` exactly, whose log is `0.2256541`; `0.2299545` is the *linear* sum `Σ 1/(3x)`, and the two were conflated).  It does **not**
  grow with `n`.
* **It is concentrated at the bottom.**  Over `99.2 %` comes from odd orbit values
  below `1000`; the part contributed by values *above the start* is `≤ 7.4/n`
  (measured maxima `4.16e−4` at `10⁴`, `4.59e−6` at `10⁶`, `5.17e−10` at `10¹⁰`,
  `5.76e−20` at `10²⁰`).

So Round X's "the coupling vanishes on the divergence half" is correct and **harmless**:
it says the coupling vanishes where the orbit is large, which is exactly where it never
carried anything.  *A coupling mechanism must be a bottom-scale mechanism or it is
measuring `O(1/n)`* — the same place `minEsc` lives.

`octave_sojourn` (LEAN_PROVED) is the first structural theorem in that direction:
**an orbit occupies a dyadic octave for at most two consecutive steps** — an even value
in `[2^k,2^(k+1))` halves out downward, two consecutive odd values multiply by `9/4 > 2`
and leave upward.  Verified over all orbits from `n < 200 000`: maximum run `2`, zero
exceptions.  So the accumulated coupling inside octave `k` is at most
`2·(entries)/(3·2^k)`, and bounding the entries is the remaining content.

## Verdict table for Round XI files

| file | verdict | reason |
|---|---|---|
| `CouplingNormal` | **YELLOW** | `coupling_multiplicative`, presented as "the composition law", is a commutativity rearrangement: it compiles verbatim with `acceleratedOrbit` and `oddCount` replaced by **arbitrary** functions `f, g` satisfying only `g n (i+k) = g n i + g (f i n) k` (probe compiled, `depends on axioms: [propext]`).  It consumes no dynamics; the conversion's content is `one_add_coupling`, which is not composed with it in Lean.  Every number in the docstring recomputes exactly (`2^L/3^a` and `E` at `(2,1), (27,17), (10,6), (24,15), (11,7)`), and the exact conversion reproduces with zero mismatches over 8250 instances at `d = 1, 5, −1, 59, 13, 7`. |
| `SegmentMonoid` | **CLEAN** | `3·187·5077565 = 2848513965 > 2281701376 = 17·2^27` recomputes.  `cycle_frontier` plus asset (a) admits exactly `L = 4701, 5755, 6809, 7863, 8917, 9402, 9971, 10456, …` — reproduced exactly, 10 pairs below `L = 12000`.  Self-flagged as `RealizableFrontier6809` in new coordinates, correctly. |
| `CoupledCycle` | **YELLOW** | The reach table's middle row does not reproduce.  With the stated constant `3·2^k·g ≤ a·2^L` and the best admissible `k = 20` (`2^20 = 1048576 ≤ 1086464`), the first surviving pair is `(4701, 2966)`, **not** `(2593, 1636)`; `(2593,1636)` is the first survivor of `2^k·g ≤ a·2^L`, i.e. the same bound *with the factor 3 dropped*.  So the free floor `c = n` buys `n/2^k = 1.036`, a `3.6 %` improvement, **not** the claimed "threefold improvement in reach" — the two rows give the identical frontier list.  The paper's conclusion ("the bridge adds no frontier") survives and is in fact strengthened. |
| `ScaleFibre` | **YELLOW** | The Lean is correct and the numbers are right, but the headline — "the `(word,magnitude)` fibre carries no two-variable information at all" — is a quantifier-order fallacy: rank one holds at each fixed `j`, with a coefficient `E(w_j)` that is unbounded in `j` and in fact `≈ 0.2·n` at the end of a real orbit (table above).  Secondary: "`N(w)` is large exactly when `G` is small — at the ledges, and nowhere else" is backwards in relative terms — `N/2^L = 1.5^a/G` is `1.94e−4` at `(27,17)` and below `1e−300` at `(1539,971)`, `(2593,1636)`, `(4701,2966)`, `(6809,4296)`.  `drop_of_scale` is **not** vacuous at the ledge pairs (thresholds `26 044`; 526, 760, 174, 292 digits respectively), and is compatible with asset (a) at all of them except `(27,17)`, where the threshold `26 044` is below `1 086 464` anyway. |
| `FilterDecomposition` | **YELLOW** | Compiles clean, axiom-clean, and every numeric claim in its docstring recomputes exactly (`C + 2^L = D + 3^a` and `B + E + 2^L = 3^L` over all 8190 words to `L = 12`; survivor count `L+1`; composing pairs `2L+1`; `C[1,0]=1`, `B[1,0]=3`; `C(0^m1^p) = 2^m(3^p − 2^p)`).  Three defects.  (i) **The citation runs backwards.**  Lines 47 and 540 say the two survivors `0^L, 1^L` are "already eliminated", `1^L` by `ScaleRecord.mersenne_nonDropping` — but that theorem proves `2^k − 1` does **not** drop for `k` steps, i.e. it *exhibits* the survivor.  `ScaleRecord`'s own header flags it as the refutation of "long certificates are impossible".  `1^L` is the realizable hard case, not a handled one.  (ii) **The classification is generic in the constants.**  A probe restating the Part 3–4 chain with `3` replaced by an arbitrary `r ≥ 2` and `2^j` by an arbitrary positive `g j` compiles: `eq_iff_zeroOnes` is the general fact that "multiply on every letter" dominates "multiply on odd letters only", strictly once an even letter follows an odd one.  Nothing about 3, powers of 2, or Collatz enters.  (iii) **No Lean-level contact with the map.**  The file never mentions `acceleratedOrbit`, `affineC` or `Accelerated.oddCount`; its `C`/`B` are freestanding `List Bool` functions in `DeltaSpectrum`, which imports nothing and is nowhere linked in Lean to the affine law.  **Vacuity at the targets:** not one genuine cycle word lies in the surviving class — checked for `3x+5` at `187` and `347`, `3x+13` at `131`, `3x+59` at `229`, `3x−1` at `17`, `3x+7` at `5`, and the `3x+1` cycle, whose word `10` is the file's own `concat_fails` counterexample.  This is forced: a cycle-minimal word begins with `1`, the only `0*1*` word beginning with `1` is `1^L`, and `1^L` needs `2^L > 3^L`.  *Not* a defect: "every survivor is `0^m 1^p`" **is** proved — `zeroOnes` is definitionally that shape and `eq_iff_zeroOnes` is an iff. |
| `CouplingDecay` (this desk) | — | 15 theorems, all `[propext, Quot.sound]`.  `window_bound` non-vacuous: hypothesis satisfied by 55 460 of 60 000 random instances, zero violations; `orbit_floor`, `trivial_cycle_coupling` (`q < 40`) and `octave_sojourn` (`n < 100 000`) all verified with zero exceptions. |

## Failed attempts, with diagnosis

* **Prove `Σ 1/x_i < ∞` along a divergent orbit from injectivity.**  Distinctness of the
  odd orbit values gives only `Σ_{m≤M} 1/(3y_m) ≤ (1/3)Σ_{m≤M} 1/(2m−1) < (1/6)ln M +
  0.4`, i.e. `1 + r_M = O(M^(1/6))`.  Unbounded, so no kill.  *This bound is refuted by
  every cycle* — where `1 + r` grows exponentially in `M` while the values repeat — so
  it does satisfy diagnostic 4; it is simply too weak.  Diagnosis: distinctness bounds
  the *count* per octave by `2^(k−1)`, and `2^(k−1)·2^(−k) = 1/2` per octave, so
  counting alone can never beat a divergent harmonic sum.
* **Refute it with a `3x+d` cycle of large minimum.**  Scaling `(C,x,d) ↦ (λC,λx,λd)`
  maps cycles to cycles and leaves `d/(3x)` **invariant**, so the minimum cannot be
  pushed up while holding the rate down.  Diagnosis: the dimensionless rate is `d/(3x)`,
  not `1/x` — which is also why diagnostic 3 does *not* refute `κ`: it is degree **one**,
  not degree zero, under `C ↦ d·C` at fixed `x`.
* **Close the gap with the octave walk.**  `octave_sojourn` gives sojourn `≤ 2`, so
  `Σκ = ∞` would force the orbit to *enter* octave `k` about `2^k/k` times, hence to
  grow only linearly in time, hence to hold its odd density at exactly `log₃2` forever.
  That is a knife-edge and almost certainly impossible — but "almost certainly" is a
  density statement about the parity word, and Terras leaves every finite parity word
  free.  Recorded as the exact remaining gap, not as a proof.


---

## Round XI postscript — the decoupling claim was wrong; the closure is not

The adversary was asked to *prove* the decoupling theorem.  It refuted it instead, and
the refutation lands on my own deliverable.

### The quantifier-order fallacy

`κ(w,n) = E(w)/n` with `E(w) = C_j/3^(A_j)` is an identity **at fixed window `j`**,
with `n` ranging over a residue class mod `2^j`.  That is Terras, and it is true.  But
`E` is **unbounded in `j`**, and along a real orbit `j` grows with `n`:

| `n` | 27 | 993 | `10^9+7` | `10^12+39` |
|---|---|---|---|---|
| `E(w)` | 5.369 | 251.4 | `2.054·10^8` | `2.178·10^11` |
| `E/n` | **0.199** | **0.253** | **0.205** | **0.218** |

`E` grows **proportionally to `n`**, so the `1/n` cancels exactly.  **`κ → 0` holds at
a fixed window and fails in the joint limit — which is the only regime this programme
has ever lived in.**  Sections A, B and C above are therefore correct as stated and
irrelevant as argued.  (Consistent with Round IX's measurement that `r_L` clusters in
`[0.157, 0.210]` on real orbits — that was the joint limit all along, and it never went
to zero.)

There is also **no unconditional `1/x₀` law**: at `x₀ = 1365`, `k = 20`,
`κ = 716881/331695 = 2.16127`, against a claimed `a/(3x₀) = 0.00122` — off by `1770×`,
and `κ` exceeds `2`.  `ScaleLadder.coupling_bound` carries a *floor hypothesis* and is
correct; the bare rate quoted in Round X is not.  And decay would not give summability
anyway: on a cycle `1 + r → ∞` while every period's `κ` is fixed.

### The route is closed, for a better reason

Taking logarithms of the master identity `1 + r_j = ∏_(odd i<j) (1 + d/(3x_i))`:

> **`log₂(1 + r_j) = log₂(x_j/n) − (A_j·log₂3 − j)`** — verified exact.

**The accumulated coupling *is* the spread.**  Bounding it and solving the archimedean
tracking problem are the same sentence, so the coupling family is **Class 1 by
identity, not by asymptotics**.  A decay estimate can neither kill nor advance the
route, which is why the decay argument was the wrong instrument for a correct verdict.

### The repair, and where a coupling mechanism could still live

Total accumulation is universally bounded — `Σ 1/(3x_i) = 0.2299545` at `n = 993`,
reproduced to seven digits, and **not growing with `n`** across sampled starts to
`10^13`.  Over `99.2%` of it comes from odd values below `1000`.  So "the coupling
vanishes on the divergence half" is true and *harmless*: it vanishes where the orbit is
large, which is where it never carried anything.

> **A coupling mechanism must therefore be a bottom-scale mechanism.**

`octave_sojourn` starts that programme: an orbit occupies a dyadic octave for at most
**two** consecutive steps — verified, worst case exactly `2` over all `n < 200000`,
witness `7 → 26`.  The exact remaining gap: forcing `Σκ = ∞` would need `≈ 2^k/k`
entries per octave, hence linear-in-time growth, hence odd density pinned at exactly
`log₃2` forever.  A knife-edge — but "almost certainly impossible" is a density claim,
and Terras leaves every finite word free.

### One miss of my own

The adversary found the `CoupledCycle` reach table off by a factor 3 in its middle row:
with a power-of-two floor the first survivor is `(4701, 2966)`, not `(2593, 1636)`, so
the free floor buys **3.6%**, not "threefold".  **My own verification printed that
mismatch and I did not flag it** — the line read `power-of-two floor : (4701, 2966)
(agent: (2593, 1636))` and I moved on.  The conclusion survives and is strengthened
(the bridge adds even less than claimed), but the miss was mine.

---

## Round XII, section XXIV — the octave word against the ordered odd times

**Verdict: the two coordinates are compatible, and here is the theorem saying so.**
File `Collatz/Strategy/OctaveOrder.lean` (all LEAN_PROVED, axioms
`propext, Quot.sound` ± `Classical.choice`).

**The forward map** (octave word → ordering).  Every step obeys
`oct (T x) + evenIdx x = oct x + raiseIdx x` (`oct_step_balance`), which telescopes to
`oct (T^j n) + #even(j) = oct n + #raise(j)` (`oct_orbit_balance`) — an identity, no
hypotheses.  Consequences: **the cyclic balance** `#raise = #even` around a cycle
(`cycle_octave_balance`), hence **`L ≤ 2a`** with no archimedean input
(`cycle_length_le_two_mul_oddCnt`), and the **ballot inequality**
`t_i ≤ (i−1) + D(i−1)` (`time_bound_of_no_drop`), which is the complete content of
the map.

**The reverse map**: `oct (T^j n) + (j − a_j) = oct n + #raise(j)`
(`oct_orbit_from_times`); and a step drops the octave *iff* it is even
(`oct_drop_iff_even`), so the octave path determines the parity word outright.

**No incompatibility can exist.**  `octave_word_time_invariant`: prefixing `r` even
steps shifts every odd time by `r` and leaves the octave decoration word *pointwise
unchanged*.  The decoration is a function of the odd-step **index**, never of the
**time**, so no constraint of the form "the octave path wants an odd step near `t`"
is expressible.  Sealed by `ballot_iff_no_drop`: `#even(j) ≤ #raise(j)` **iff**
`oct n ≤ oct (T^j n)` — the ballot inequality is an `iff` with a pure magnitude
statement, i.e. Round VIII heaviness in new coordinates.  **Class 3.**

*Not the Round XI isomorphism.*  `E(w) = Σ 2^(t_i)/3^i` is a bijection onto its image;
this map is a coarsening with a nontrivial invariance group (`n ↦ 2^r n`) acting on
the times.  A coarsening with a transitive invariance group on the conflicting
coordinate cannot be an isomorphism in disguise — and that is exactly why it cannot
obstruct.

**The one new asset.**  For odd `z` the true octave-rise criterion
`2^(oct z + 2) ≤ 3z + 1` differs from the multiplicative one `2^(oct z + 2) < 3z`
**exactly** at the base-4 repunits `z = (4^m − 1)/3`, every one of which reaches `1`.
Hence on a counterexample orbit **the `+1` never changes an octave decision**: the
octave word of a counterexample is exactly that of `x ↦ 3x/2`
(`raise_iff_mult`, `octave_word_multiplicative`).  Consumes d-asset (d) plus
reach-one; correctly refuted at `z = 5` on the `3x+5` and `3x+7` cycles.

**Failed attempts (diagnosis in the file docstring).**  (i) "the decoration is a pure
Sturmian word of slope `log₂3`" — false; departs at odd-step index 13 for `n = 27`,
59 for `n = 10^12+39`, because per-step exactness does not integrate (the accumulated
`+1`s move the phase, and that drift *is* Round XI's coupling).  (ii) "contradict
`2^L > 3^a` with the balance" — `1.5a ≤ L ≤ 2a` (the lower bound composing with
`Octave.O0_forces_O1` from the sibling file) brackets `1.585a` from both sides and
never excludes it.  (iii) "find a cyclic word admissible for the octave path and
forbidden by the ordering" — impossible, by the invariance above.

---

# Round XII, Branch B — the high-scale word model is the frontier filter, and its reach is finite

*New file: `Collatz/Strategy/HighScaleWord.lean` — 11 theorems, compiles clean under
`lake env lean`, zero errors, zero warnings, no `sorry`/`axiom`; `check_integrity.sh`
passes, build green.*

Branch A was already empty (`BottomUnreachable`).  This desk owned the only surviving
branch and closes it.

## 1.  The exact word-only model

Around a hypothetical accelerated cycle of period `L`, odd count `a`, minimum `n`, the
affine law read multiplicatively is `2^L/3^a = ∏_{t<a} (1 + 1/(3 y_t))` over the odd
points.  Every `y_t ≥ n`, so all dependence on the *values* collapses into a window:

> **`1 < 2^L/3^a ≤ (1 + 1/(3n))^a`**   (MATHEMATICALLY_PROVED)

That is the rigid word model, made precise.  Its limit `n → ∞` is the equation
`2^L = 3^a`, which has no solution — which is exactly why the route looks promising.
But the limit is never attained, and the entire content is the window's width `≈ a/(3n)`.
Linearising is `SegmentMonoid.cycle_frontier`, `3n(2^L − 3^a) ≤ a·2^L`.

**Answer to question 1: yes, the high-scale regime forces an exact word-only model, and
that model is `cycle_frontier`.  Nothing else.**

## 2.  The budget reduces to the frontier filter — and is strictly weaker than it

**Round XII's prediction is CONFIRMED.**  `counterexample_word_budget` (LEAN_PROVED) is
the reduction in one line: `cycle_frontier` at the cycle minimum plus
`ge_verified_1086464` gives `3·1086464·(2^L − 3^a) ≤ a·2^L`.

But the reduction lands *below* the frontier, not on it.  COMPUTATIONAL (exact integers,
two independent implementations, zero mismatches, `L ≤ 12000`): the survivors are

`(4701,2966) (5755,3631) (6809,4296) (7863,4961) (8917,5626) (9402,5932)`
`(9971,6291) (10456,6597) (11025,6956) (11510,7262)`

— ten pairs, reproducing `SegmentMonoid`'s list independently.  The first is `4701`,
while `RealizableFrontier6809.length_ge_6809` excludes `4701` *and* `5755`.  Both ends
are now kernel-checked: `budget_admits_4701` and `budget_excludes_3647` (LEAN_PROVED,
no axioms).

> **word budget ⊊ frontier certificate, by two risers.**  The missing information is the
> *ordering* of the parity word, which `Bcap` reads and `(L,a)` cannot.  A word-only
> model is strictly below the tool already in the repository and cannot improve it.

## 3.  Why: the survivor set is generated by the convergents of `log₂3`

With `485/306` and `1054/665`, the consecutive convergents of `log₂3` straddling it
(`485 − 306·log₂3 = +1.4748·10^(−3)`, `1054 − 665·log₂3 = −6.2980·10^(−5)`),
**every one of the ten survivors is `u·(1054,665) + v·(485,306)` with `u ≥ 4`,
`v ∈ {1,2}`** (COMPUTATIONAL, exact, all ten).  The frontier ladder's own spacings —
`A(c)` records at `1636, 2301, 2966, 3631, 4296, 4961`, spaced by exactly `665`;
frontier lengths spaced by exactly `1054` — are the same two convergents.  So
`RealizableFrontier6809`'s "staircase" is literally the continued fraction of `log₂3`,
and the word model adds no arithmetic to it.

## 4.  The filter's reach is finite, and the sharp constant is `2n`

Cleared of subtraction (`budget_cleared`, LEAN_PROVED), the budget is *equivalent* to
`2^L/3^a ≤ 3n/(3n−a)`, i.e. `δ ≤ log₂(3n/(3n−a))` with `δ = L − a·log₂3`.  For a ladder
pair `δ < log₂3` always, and the right-hand side reaches `log₂3` exactly at `a = 2n`.
Hence:

> **`budget_slack` (LEAN_PROVED, `d`-free, no dynamics): if `2^L ≤ 3^(a+1)` and
> `2n ≤ a`, then `3n(2^L − 3^a) ≤ a·2^L`.**

The budget `a/(3n)` grows linearly in the length while the Diophantine defect it must
beat is bounded by `log₂3`: **the filter is monotone in the wrong direction — longer
cycles are easier to admit.**  `budget_iff_ladder_at_2n` (LEAN_PROVED) shows the
constant is not an artefact: at `a = 2n` the budget is *equivalent* to the ladder
condition `2^L ≤ 3^(a+1)`, which every ladder pair satisfies by construction.

Instantiated at the verified range, `budget_vacuous_at_2172928`: the strongest word-only
budget a counterexample admits **excludes nothing with `a ≥ 2 172 928`**.  COMPUTATIONAL
(exact criterion, `Decimal` at 50 digits, `L < 3.5·10⁶`): the largest ladder pair
actually excluded at `n = 1086464` is `L = 3 441 922`, against the proved threshold
`L ≈ 3 444 009` — sharp to `0.06 %`.  Only `2 031 130` of those `3.44·10⁶` lengths are
excluded, so the filter is not even dense below its own reach.

## 5.  High-scale exactness (section XX): the answer is the opposite of the hope

`octave_word_free` (LEAN_PROVED), witness `2^k + (r % 2^j)`: for every `j ≤ k` and every
`r`, the octave `[2^k, 2^(k+1))` contains a point whose length-`j` parity word is that
of `r`.  COMPUTATIONAL (exhaustive): all `2^j` words realised at
`(k,j) = (12,6), (21,8), (14,10), (10,10)`, no exceptions.

**Large `x` does not make transitions deterministic; it makes them maximally
nondeterministic.**  On the parity alphabet the high-scale system is the *full shift*.

## 6.  The symbolic SCC model (section XXXVIII) is unattainable, and here is the pincer

* The alphabet that *has* forbidden words is the three-letter octave-**increment**
  alphabet `{E, O0, O1}`, where `Octave.no_O0_after_O0` forbids `O0 E^m O0`.  It is
  finite, so `ScaleLadder.no_finite_scale_invariant` applies verbatim: repeated vertex,
  cycle, infinite admissible path.  Acyclicity is impossible *by theorem*.
* The alphabet that could carry unbounded information — the parity word — has **no
  forbidden words at all** (`octave_word_free`).

So the brief's question "what unbounded coordinate supplies well-foundedness?" has no
answer on this branch: the obstruction is not a missing coordinate but the presence of
every transition on the only alphabet rich enough to matter.  **No normalized-coordinate
octave SCC model can exist.**

## Assets and refutation tests

Asset (a) is consumed once, in `counterexample_word_budget`.  Everything else is `d`-free
integer arithmetic.  Diagnostics re-run this round from scratch (exact integers):

| cycle | `d` | `L` | `a` | `2^L−3^a` | `sign` match (e) | general `3nG ≤ d·a·2^L` | `d=1` form |
|---|---|---|---|---|---|---|---|
| `17` | `−1` | 11 | 7 | `−139` | ✓ | ✓ | ✓ |
| `5` | `−1` | 3 | 2 | `−1` | ✓ | ✓ | ✓ |
| `5,19,23` | `5` | 2,5,5 | 1,3,3 | `1,5,5` | ✓ | ✓ | ✗ |
| `187`,`347` | `5` | 27 | 17 | `5 077 565` | ✓ | ✓ | ✗ |
| `5` | `7` | 4 | 2 | `7` | ✓ | ✓ | ✗ |
| `131` | `13` | 24 | 15 | `2 428 309` | ✓ | ✓ | ✗ |
| `1` | `1` | 2 | 1 | `1` | ✓ | ✓ | ✓ |

Diagnostic (e) holds on every genuine cycle.  The general budget holds on every genuine
cycle (it is a theorem, so it must); the `d=1` form is violated by every `d>1` cycle,
independently reproducing `SegmentMonoid`'s `3·187·5 077 565 = 2 848 513 965 >
2 281 701 376 = 17·2^27` — degree **one** in `d`, diagnostic 3 passed.  The negative
results of this round are *not* refuted by those cycles and should not be: they are
statements about a filter's weakness, and a filter that admits genuine cycles is correct.

## Failed attempts, with diagnosis

* **A sharper threshold from the linearised budget.**  My first pass computed the
  filter's reach from `δ ≤ a/(3n·ln2)` and reported "the last excluded pair is
  `L = 5 672 137`".  A second implementation using the *exact* criterion
  `δ ≤ log₂(3n/(3n−a))` found **zero** exclusions anywhere in `[5·10⁶, 5.8·10⁶)`.  The
  two disagreed; the exact one is right; the number is withdrawn and recorded as an
  error in the file header.  Diagnosis: `−ln(1−x) ≥ x`, so the linearisation is strictly
  *stronger* than the inequality it approximates and overcounts exclusions.  The correct
  threshold is `a ≥ 2n`, which is then provable outright — the failed measurement led to
  the sharp theorem.  *(Section LIII's discipline caught this; last round's factor-3
  miss did not recur.)*
* **Find an unbounded coordinate for an octave SCC model.**  Abandoned once
  `octave_word_free` was proved: there is nothing to be well-founded *over*, because no
  transition is forbidden on the parity alphabet.  Diagnosis: the brief's warning asked
  for a coordinate; the real obstruction is one level earlier, in the alphabet.
* **Strengthen the budget by using `x_t ≥ 1086464` rather than `x_t ≥ n`.**  Zero gain:
  `n ≥ 1086464` already, so the free floor is `n` and using the constant only weakens
  it.  This is the same `3.6 %` illusion the adversary found in `CoupledCycle` last
  round, now understood structurally: the floor enters only through `3n/(3n−a)`, which
  is *increasing* in `n`, so a larger floor makes the filter **weaker**, not stronger.

## Verdict

> **Branch B is closed.**  The high-scale regime does force an exact word-only model;
> that model is `cycle_frontier`; `cycle_frontier` is `RealizableFrontier6809` in
> multiplicative coordinates but two risers weaker; its universal reach ends at
> `a = 2n`; and the octave symbolic system it would need is the full shift.  Round XII
> had two branches, and both are now empty.  What remains in the repository is what
> remained before it: extend the verified range, or read the *ordering* of the parity
> word better than `Bcap` does.

---

# Round XII — what the constant `0.2299545` actually is

## Sections XXXIX–XLI, and one correction to Round XI that changes the object

### 0. The correction, first

Round XI's postscript says

> `log(1+r) ≤ 0.2299545`, attained at `n = 993` (**correction:** `1 + r = 1.2531421` exactly, whose log is `0.2256541`; `0.2299545` is the *linear* sum `Σ 1/(3x)`, and the two were conflated)

and, two paragraphs later, `Σ 1/(3x_i) = 0.2299545`.  **Those are two different
numbers and only the second one is `0.2299545`.**  Recomputed in exact rationals, two
independent implementations (accelerated map `T`, and the plain map `3x+1`, which visit
the *same* odd values in the *same* order — verified elementwise):

| object at `n = 993` | exact | float |
|---|---|---|
| `S(993) = Σ_{odd x_i} 1/(3 x_i)` | 60-digit / 61-digit rational | `0.229954486122031` |
| `ρ(993) = 1 + r = 2^61/(3^32·993)` | `2305843009213693952/1840049047529878113` | `1.253142144395068` |
| `log ρ(993)` | — | `0.225654112731978` |
| `exp(S(993))` | — | `1.258542727465798` — **this is `exp` of the linear sum, not `1 + r`; `1 + r = 1.2531421`** |

`1.258543` is `exp(S)`, not `1 + r`.  `S` and `log ρ` differ in the **third** digit.
The constant that was measured is `Σ 1/(3x_i)`; every statement below is about that
object, and `ρ` is named separately wherever it appears.

**Map discipline.**  `a` (odd-step count) and the odd-value list are identical for the
accelerated and the plain map, so `S(n)` is map-independent.  `L = 61` is the
*accelerated* orbit length, equal to the number of halvings of the plain orbit; the
plain orbit of `993` has `61 + 32 = 93` steps.  All `L`, `a` below are accelerated.

### 1. The exact value  (section XXXIX)

`S(n)` is **exactly a rational**: a finite sum of `1/(3x)` over the 32 odd values of one
explicit orbit.  It is *not* a logarithm, not a limit, not an extremum of a smooth
family.  The reduced fraction at `993` has a 60-digit numerator over a 61-digit
denominator; the maximum is the value of an explicit finite sum at one explicit integer
and that is all it is.

What *is* closed-form is its companion and dominator.  From
`one_add_coupling` (LEAN_PROVED) with `x_L = 1`:

> **`∏_{odd x_i} (1 + 1/(3 x_i)) = 2^L/(3^a n) = ρ(n)`**,  hence
> **`log ρ(n) ≤ S(n) ≤ ρ(n) − 1`.**

At `n = 993`: `ρ = 2^61/(3^32·993)`, `ρ − 1 = 465793961683815839/1840049047529878113
= 0.2531421…`, and `0.2256541 ≤ 0.2299545 ≤ 0.2531421`.  (Product identity: 0 mismatches
in 2000 random `(n,j)`, exact rationals.  Sandwich: 0 violations in 4000.)

**`ρ` is also maximised at `993`** — checked separately, because the two orderings are
*not* the same: `505` is a `ρ`-record and not an `S`-record.  Max `log ρ` over all
`n ≤ 10^9` is `0.225654112731976` at `993`.

The upper half of the sandwich is now Lean, in `Nat`, in
`Collatz/Strategy/HarmonicCoupling.lean`:

* `couplingTerms_eq_affineC` — **`affineC j n` *is* the sum
  `Σ_{i<j, x_i odd} 2^i·3^(#odd steps in (i,j))`**, as a summation and not a recursion.
* `harmonic_term_le` — termwise, `3^(A_j)·n ≤ 3·x_i·(2^i·3^(A'))`, i.e. the `i`-th
  harmonic term is below the `i`-th coupling term over the common denominator
  `3^(A_j)·n`.

Together: `S_j(n) ≤ affineC j n / (3^(A_j)·n) = ρ_j(n) − 1`, with no rationals in the
Lean and no inequality between infinite objects.  Both `[propext, Quot.sound]`.
`rho_993` and `affineC_993 : affineC 61 993 = 465793961683815839` are kernel-checked
(`decide`, no `native_decide`).

### 2. Why `993`  (section XL)

`S(T n) = S(n) − 1/(3n)` for odd `n`, and `S(2n) = S(n)`.  So **`S` strictly increases
along backward orbits**, and a maximiser must have no odd predecessor.  An odd `m` has
an odd `T`-predecessor iff `2m ≡ 1 (mod 3)`; therefore

> **every odd multiple of `3` is a leaf of the backward tree**
> (`no_odd_preimage_of_three_dvd`, LEAN_PROVED: `3 ∣ m ∧ x` odd `⇒ T x ≠ m`).

`993 = 3·331` is such a leaf (`leaf_993`).  The `S`-record chain over `n ≤ 10^9` is

    1, 3, 7, 9, 559, 745, 993

and its last three entries are one backward chain, each the **smallest** odd predecessor
of the next: `993 = (4·745−1)/3`, `745 = (4·559−1)/3` (`step_993_745`, `step_745_559`,
`smallest_pred_993`, `smallest_pred_745`).  The chain stops because `3 ∣ 993`.

The finite combinatorial pattern is a two-move rule on the backward tree.  For odd `m`,
the odd predecessors are `p_k = (2^k m − 1)/3` for `k` in one residue class mod 2, and
`S(p_k) = S(m) + 1/(3 p_k)`, so the **smallest** child is always the locally best one.
Greedy from `559`: `k = 2` twice, then a leaf.  Every competing branch pays for a larger
`k` and cannot recover it downstream — the branch-and-bound is finite and explicit:

| branch off | `k` | child | `S(child)` | best in that subtree |
|---|---|---|---|---|
| `745` | 2 | **`993`** | **0.229954486** | **leaf — 0.229954486** |
| `745` | 4 | `3973` | 0.229702703 | `3973 → 5297 → 3531` (leaf), 0.229860033 |
| `745` | 6 | `15893` | 0.229639777 | below |
| `559` | 4 | `2981` | 0.229283195 | below |

So `993` wins by `9.4·10^(−5)` over the runner-up `3531`, and the gap between `993` and
the best start *below* it is exactly one term: `S(993) − S(745) = 1/(3·993) = 1/2979`
(exact).

`993`'s own orbit, for the record — 32 odd values, max `2693`, min `5`:

    993 745 559 839 1259 1889 1417 1063 1595 2393 1795 2693 505 379 569 427
    641 481 361 271 407 611 917 43 65 49 37 7 11 17 13 5

`99.283 %` of `S(993)` comes from the 24 odd values below `1000` (Round XI's "99.2 %"
reproduces); `95.0 %` from the 9 values below `100`.

### 3. Isolated maximiser, not a family  (section XLI)

**COMPUTATIONAL, exhaustive:** `993` maximises `S` and `log ρ` over **all `n ≤ 10^9`**
(three independent implementations agreeing — C with a float memo, Python with a float
memo, and Python in exact rationals to `2·10^5`; `S(2n) = S(n)` restricts the search to
odd `n`).  A deeper run to `2·10^10` was started and **aborted before completion**, so
`10^9` is the range actually certified; the aborted run had produced no new record.

The top of the spectrum is *isolated*:

| rank | `n` | `S(n)` | `n mod 3` |
|---|---|---|---|
| 1 | **993** | 0.229954486122 | 0 |
| 2 | 3531 | 0.229860033328 | 0 |
| 3 | 35271 | 0.229836629191 | 0 |
| 4 | 167211 | 0.229834635662 | 0 |
| 5– | 4393983, 10415367, … | 0.2298345… | mixed |

Ranks 5 onward pile up at `λ ≈ 0.22983431`, which is `S` of their common orbit value
`190034444` — an accumulation point of the spectrum `1.2·10^(−4)` **below** the maximum.
So there is no family `n_k` with `S(n_k) → S(993)`: the maximiser is a strict, isolated
finite maximum, and the only other `n` attaining it are `993·2^k`.  (`993` has no odd
predecessor, so no other start has `993` in its orbit at all.)

### 4. The threshold law  (sections XXXIII–XXXIV)

`1000` is not sacred and the cutoff is not a cliff.  Define
`H(n,B) = Σ over odd orbit values x ≥ B of 1/(3x)` and `F(B) = max_n H(n,B)`.
Measured exhaustively over `n ≤ 3·10^7` (C; five entries re-verified in exact rationals
in Python, all matching to every printed digit):

| `B` | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 | 8192 | 16384 | 32768 | 65536 | 2^18 | 2^20 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `F(B)` | 9.65e−2 | 6.21e−2 | 4.06e−2 | 2.11e−2 | 8.85e−3 | 4.32e−3 | 2.81e−3 | 1.86e−3 | 8.99e−4 | 4.70e−4 | 2.33e−4 | 1.20e−4 | 3.89e−5 | 1.15e−5 |
| `B·F(B)` | 3.09 | 3.97 | 5.20 | 5.39 | 4.53 | 4.42 | 5.76 | 7.61 | 7.37 | 7.70 | 7.65 | 7.84 | 10.19 | 12.04 |
| `B·F(B)/ln B` | 0.89 | 0.95 | 1.07 | 0.97 | 0.73 | 0.64 | 0.76 | 0.92 | 0.82 | 0.79 | 0.74 | 0.71 | 0.82 | 0.87 |

> **`F(B) = c(B)·ln B / B` with `c(B) ∈ [0.64, 1.07]`, mean `0.83`, over
> `32 ≤ B ≤ 2^20`.**  (COMPUTATIONAL; `F(1) = F(2) = F(4) = S(993)`; the first drop is
> at `B = 8`, `F(8) = 0.1329` at `n = 123`.)

`F(B) → 0` — but **it is not proved and cannot be proved by the means available here**,
and this is the same wall Round XI hit.  What *is* proved:

* exact, `Nat`: for the segment before the first descent below `B`,
  `H ≤ affineC(segment)/(3^(a)·x_0)` — the segment's own `ρ − 1`
  (`harmonic_term_le` + `couplingTerms_eq_affineC`);
* conditional: `ScaleLadder.coupling_bound` / `window_bound` (LEAN_PROVED) give
  `H ≤ a_B/(3B)` where `a_B` is the number of odd steps taken above `B`.

The gap is exactly `a_B`.  Reading the table backwards, `3·B·F(B) = a_eff ≈ 2.4 ln B` —
the effective number of odd steps that an orbit can spend *just above* `B` grows like
`ln B`, and no theorem in the repository bounds it.  Bounding `a_B` is bounding the
spread of a segment, which Round XI's master identity already showed **is** the
archimedean tracking problem.  So `F(B) → 0` is Class 1, by identity.

Correspondingly, exhaustive search can never *prove* the maximality of `993`:
`S(n) = H(n,B) + S(m)` with `m < B` the first orbit value below `B`, and
`max_{m<B} S(m) = S(993)` for every `B > 993`, so the decomposition is vacuous above the
maximiser.  **Maximality of `993` is CONJECTURE, verified exhaustively to `10^9`.**

### 5. What the constant constrains — honestly, nothing about a counterexample

Every orbit point of a counterexample is `≥ 1086464`
(`RealizableFrontier6809.ge_verified_1086464`, `Search.reachesOne_of_lt_1086464`, under
`¬ReachesOne` — cycles and divergent orbits alike; `Strategy/BottomUnreachable.lean`).
`99.283 %` of `S(993)` comes from odd values below `1000`, and `100 %` from values below
`3000`.  Therefore:

> **`S` is a statistic of trajectories that reach `1`.**  A counterexample never enters
> the region that supplies the constant, so `S(993) = 0.2299545` bounds nothing a
> counterexample must pay.  It is a fact about the trivial behaviour.

What it *does* say, stated as narrowly as it deserves:

1. `S(n) ≤ ρ(n) − 1 = 2^L/(3^a n) − 1` is an **exact** inequality valid for every `n`
   and every window, counterexamples included — but with `ρ` unbounded there, it is
   empty for them.
2. On the reaching-`1` side, `S` is bounded and the bound is attained, so the *sum*
   normalisation of the coupling is finite where the *product* normalisation is `2^L/3^a`.
   The two agree only to two digits, and Round XI's headline conflated them.
3. Any future "bottom-scale coupling mechanism" (Round XI's repair) that is calibrated
   against `0.2299545` is calibrated against a number living entirely below `3000`, i.e.
   entirely inside the region asset (a) has already emptied.  **The repair, as
   calibrated, is also empty.**  A bottom-scale mechanism must be re-anchored at
   `1086464`, and `F(1086464) ≈ 0.83·ln(1086464)/1086464 ≈ 1.06·10^(−5)`: the entire
   coupling budget available to a counterexample, on the measured law, is about `10^(−5)`
   — five orders below the constant that has been quoted as the universal bound.

### Failed attempts, with diagnosis

* **Prove `F(B) → 0` from octave structure.**  `octave_sojourn` (LEAN_PROVED) bounds
  *consecutive* steps in an octave by 2, not the number of *returns*.  Distinctness
  bounds the count in octave `k` by `2^(k−1)`, and `2^(k−1)/(3·2^k) = 1/6` per octave —
  a divergent sum.  Diagnosis: counting arguments are scale-free and the object is not.
* **Prove global maximality of `993` by branch-and-bound on the backward tree.**  Needs
  an upper bound `U(m)` on the sum obtainable below a node.  Children satisfy
  `p ≥ (2m−1)/3`, so a backward chain may *descend* by a factor `2/3` per step; the best
  bound available is `U(m) ≤ (1/3)Σ_d 1/((2/3)^d(m+1)−1) ≈ 1`, versus the `0.23` needed.
  Diagnosis: the bound is off by a factor `4`, and closing it means bounding how deep a
  backward chain can descend — which is the forward ascent problem.
* **Find a closed form for `S(993)`.**  There is none to find: `S` is a finite sum of
  unit fractions over an orbit, the reduced denominator is 61 digits, and it factors
  into the 32 orbit values.  The only structure is the *dominator* `ρ = 2^61/(3^32·993)`,
  which is closed-form and 10 % too large.  Diagnosis: seven reproduced digits were
  evidence of an *extremal integer*, not of an extremal *constant*.
* **Reproduce Round XI's `1 + r = 1.258543`.**  It does not reproduce; it is `exp(S)`.
  Diagnosis: `Σ log(1+t_i)` and `Σ t_i` were interchanged.  Recorded, not glossed.

---

# Round XII — the ledger.  Both branches empty; the bottom is a leaf structure

## 1.  Octave theorem

`octave_sojourn` (`CouplingDecay.lean:373`) was **already a universal Lean proof** — not
a computation, as Round XI's summary and my own Round XII briefing both said.  Pure
arithmetic: both points must be odd, then `4·x_(j+2) = 9·x_j + 5 > 8·2^k`.  Map: the
accelerated `T`.  Sharp, witness `17 → 26` (my earlier "`7 → 26`" read a `(start,
value)` pair as a step pair).

Structure on top of it, all new: the alphabet is exactly **three letters** —
`E = (Δk=−1, even)`, `O0 = (Δk=0, odd)`, `O1 = (Δk=+1, odd)`, exhaustively confirmed
with no fourth.  Entry to a two-step sojourn lies in `r < 4/3`, exit in `r ≥ 3/2`; the
windows are disjoint, and that is the mechanism.

## 2.  Bottom localization

**No counterexample ever takes a value below `1086464`** — cycles and divergent orbits,
forward orbit and reverse tree, accelerated map and plain.  So the round's Branch A is
empty as posed.  `BottomUnreachable.lean` records this and declares itself a
redirection note with no new mathematics (`reaches_of_bottom_visit` duplicates
`BackwardRange.subtree_reaches_one`).

The bottom that is *not* empty: `cycle_frontier` bounds the cycle minimum **above**, so
it lies in a per-ledge band — `[1086464, 1166893]` at `(4701,2966)`, `[1086464,
1884147]` at `(6809,4296)`.  Finite, but unbounded over ledges, and clearing it is
definitionally extending the verified range.

## 3.  Coupling budget

`F(B) = max_n Σ_(odd x ≥ B) 1/(3x) = c(B)·ln B / B` with `c ∈ [0.64, 1.07]`, mean
`0.83`, over `32 ≤ B ≤ 2^20`.  **`F(B) → 0` is not proved and not provable here**: the
proved bound is `a_B/(3B)`, and bounding `a_B` is bounding a segment's spread — which
Round XI's identity says *is* the archimedean tracking problem.  Class 1 by identity.

## 4.  Coupling demand — and the repair is empty as calibrated

A counterexample's coupling is at most `a/(3·1086464)`.  That is `floor_coupling` at a
constant floor, implied by `cycle_frontier` and never conversely.  Its admissible ledge
pairs are the frontier family **cut two risers lower** — it admits `4701` and `5755`,
which `length_ge_6809` excludes — so **the budget cannot even recover the frontier**.
Reason, exact: the budget reads `(L,a)`, word *content*; `Bcap` reads word *ordering*.

And Round XI's "a coupling mechanism must be a bottom-scale mechanism" is quantitatively
empty: anchored at `1086464` the budget is `F(1086464) ≈ 1.06·10^(−5)`, five orders below
the `0.2299545` the constant advertises.

## 5.  The `0.2299545` constant — an extremal *integer*, not an extremal constant

`S(n) = Σ 1/(3x_i)` is **exactly a rational**: at `993` a 60-digit numerator over a
61-digit denominator.  No logarithm, no limit, no closed form.  Seven reproduced digits
were evidence of an extremal integer.  What *is* closed form is its dominator:
`∏(1 + 1/(3x_i)) = 2^L/(3^a n) = ρ(n)`, hence **`log ρ(n) ≤ S(n) ≤ ρ(n) − 1`** —
verified at `993` as `0.225654 ≤ 0.229954 ≤ 0.253142`.

**Why 993.**  `S(Tn) = S(n) − 1/(3n)`, so `S` increases along backward orbits and a
maximiser has no odd predecessor.  An odd `m` has one iff `2m ≡ 1 (mod 3)`, so **every
odd multiple of 3 is a leaf** — and `993 = 3·331` is one.  The record chain is
`3, 7, 9, 559, 745, 993`, the last three a single backward chain with
`993 = (4·745−1)/3` and `745 = (4·559−1)/3`, terminating because `3 ∣ 993`.  The gap to
the next best is exactly one term, `1/2979`.

Isolated, not a family: maximal over all `n ≤ 10^9` by three implementations, runner-up
`3531` at `9.4·10^(−5)`.  But **maximality is a CONJECTURE and no exhaustive range can
close it**, since `S(n) = H(n,B) + S(m)` with `max_(m<B) S(m) = S(993)` for every
`B > 993`.

## 6.  High-scale case — Branch B is empty too

`octave_word_free` (witness `2^k + (r mod 2^j)`): every length-`j` parity word occurs in
every octave `k ≥ j`.  High scale makes transitions **maximally nondeterministic**, the
opposite of section XX's hope.  Pincer: the alphabet *with* forbidden words is the
finite three-letter octave alphabet, where `no_finite_scale_invariant` applies verbatim;
the alphabet that could carry unbounded information has *no* forbidden words.  The
question "which unbounded coordinate is well-founded?" has no answer because the
obstruction is one level earlier, in the alphabet.

## 7.  Local potential / cost

None exists on the branch that matters, because the branch is empty (§2).  `r` is
exactly conserved around any cycle, so it cannot be a potential by construction; `k`'s
balance is exactly `Σ Δk = 0`.

## 8.  Block composition

`block_lower` cannot be accumulated around a cycle: empty index set, the segment rank
telescopes so no strictly submultiplicative rank exists, and the surviving product
argument reproduces the frontier ladder.  Settled in Round XI, unchanged.

## 9.  Ordering connection — inexpressible, not merely absent

`octave_word_time_invariant`: prefixing `r` even steps shifts every odd time by `r` and
leaves the octave decoration **pointwise unchanged**.  The decoration is a function of
the odd-step *index*, never of the *time*, so "the octave path demands an odd step near
time `t`" cannot be stated.  Sealed by `ballot_iff_no_drop`, an *iff* with a pure
magnitude statement — Round VIII heaviness in new coordinates.

The two desks compose to `1.5a ≤ L ≤ 2a`, bracketing the criterion's `1.585a` from both
sides and excluding nothing.

## 10.  What survives

* **The `O0 E^m O0` ban** — no two `O0` adjacent in the odd subword.  Genuinely
  non-local (the even run is transparent), so it *evades* `no_finite_scale_invariant`
  rather than restating it.  Closed by margin: it needs `a/L ≤ 2/3 = 0.66667`, the
  criterion gives `0.63093`, gap `0.0357`.  The escalation `O0 O1 O0` would close it and
  is **false** — 412136 occurrences below `n = 60000`, first at `n = 27`.
* **The repunit asset** — the `+1` changes an octave decision *exactly* at the base-4
  repunits `(4^m−1)/3`, all of which reach 1.  So a counterexample's octave word is
  exactly that of `x ↦ 3x/2`.  Verified for all odd `z < 4·10^6`.
* **Every odd multiple of 3 is a leaf** of the odd backward tree.

## 11.  The single remaining lemma

Every route this round reduced to the frontier ladder, and the ladder's price
compounds: record gaps in `1/E` are `36, 40, 44, 50, 56`, ratios `≈1.11`, so each riser
costs about `11%` more while still buying a fixed `1054`.

Round XI showed the budget-type lemma is *false as stated* (`E < 1` while `a/(3V)`
grows).  This round shows why no budget can substitute: **the budget reads `(L,a)`,
word content; the certificate reads word ordering, and content is strictly less
information.**  So:

> **The single remaining lemma is a bound on the cycle minimum that reads the *ordering*
> of the parity word and beats `Bcap` — uniformly in `a`, not one ledge at a time.**

Nothing in Rounds IX–XII produces one, and three independent routes (coupling, budget,
octave) have now each reduced to the same ladder.

---

# Round XIII — Bcap archaeology, and the number the round has to beat

Section II asks what `Bcap` throws away, before anything else is attempted.  Answer,
found by reading the definition rather than the proof:

`Bcap a = Σ_(i<a) 3^(a−1−i) · 2^(fexp i)` with `fexp i = ⌊i·log₂3⌋`
(`RealizableBound.lean:218`), while the true accumulator over the ordered odd times is
`C(w) = Σ_(i<a) 3^(a−1−i) · 2^(t_i)`.

> **`Bcap` bounds each `t_i` by `fexp i` independently and sums the maxima.**  It is the
> top corner of the heaviness box `t_i ≤ fexp i`, and it discards the ordering by
> assuming every odd step can sit at its individual maximum simultaneously.

## The corner is feasible — so nothing ordering-only can improve it

The top corner `t_i = fexp i` is strictly increasing (`ExtremalWord.fexp_strictInc`),
hence a legal word, and it attains `Bcap` by construction.  **This was already known to
the repository in prose** — `RealizableBound`'s header says the exact feasibility DP
"returns `Bcap a` on the nose at every `a ≤ 758` checked" and that "nothing sharper can
be extracted".  No new Lean was written here; what follows is the quantitative picture
that prose did not carry.

## The quantitative picture (COMPUTATIONAL, exact integer arithmetic)

* **The extremizer is isolated.**  Full enumeration of the heaviness box gives exactly
  **one** word within `1%` of `Bcap`, at every `a` from 3 to 14.
* **Runner-up law.**  `1 − second/Bcap = 0.4623/a`, stable to four digits across
  `a = 20, 40, 80, 160, 320, 640, 1280, 2966, 4296`.  So removing the single extremizer
  buys an `O(1/a)` *relative* improvement, which vanishes.
* **Minimum-phase does not remove it — and now we know why.**  For a cycle word the
  start is forced, `x_0 = C/G`, so minimum-phase is the pure word condition
  `G·C^(i) ≥ (2^(t_i) − 3^i)·C` — no magnitude in it.  **Heaviness *implies* minimum
  phase** (`MinimumInterval.minPhase_of_heavy`, LEAN_PROVED, depending on *no axioms at
  all*): heaviness is `2^(t_i) ≤ 3^i`, so the right-hand side is non-positive while
  `G·C^(i) ≥ 0`, and the inequality holds *before the accumulator term is spent*.
  Verified over every heavy word at `a = 2…9`.  The extremizer satisfies minimum phase
  not by luck but because every heavy word does.  The converse fails —
  `t = (0,1,3,5,6,8)` at `a = 6` is minimum-phase, not heavy, with `C = 1357 > 1085 =
  Bcap 6` — so minimum phase is strictly *weaker* than heaviness and adjoining it gains
  exactly zero, not a small amount.
* **`G | C` does remove it** — the extremizer fails divisibility at every `a` from 2 to
  25 — **but divisibility buys nothing.**  The certificate gives `n ≤ Bcap/G`; imposing
  `G | C` makes `n = C/G` an integer, hence `n ≤ ⌊Bcap/G⌋`, which is the same bound.
  At `a = 10, 17, 29` the floor changes the bound by exactly `0`.

## The number the round has to beat

The certificate excludes a ledge pair when `Bcap/G < c`, `c = 1086464`.  Recomputed:

| `(L, a)` | `Bcap/G` | verdict |
|---|---|---|
| `(4701, 2966)` | `0.802·10^6` | **excluded** |
| `(5755, 3631)` | `1.036·10^6` | **excluded** |
| `(6809, 4296)` | `1358717.7526` | **survives** |

— exactly the observed frontier, which confirms the mechanism.  So:

> **To exclude the frontier pair, `Bcap` must shrink by `20.038%`.  Removing the
> extremizer gives `0.01076%`.  Short by a factor of `1862`.**

*(Corrected.  An earlier draft of this section said `1.296·10^6`, `16.17%` and `1503`.
Those came from a float log-approximation applied to a huge-integer ratio, after an
`OverflowError` that I worked around instead of isolating.  The exact value
`1358717.753` had already appeared **in my own verification earlier the same session**,
in the `RealizableFrontier6809` record table.  Third instance this session of the same
failure mode — seeing a mismatch and moving on — and the one the brief's section LIII
was written about.  The conclusion is unchanged and slightly worse.)*

**An epsilon improvement is therefore worthless.**  The round needs a *constant-factor*
reduction in `Bcap` under the cycle constraints, or a proof that none exists.  Brief
section XXII asks for uniformity in `a`; uniformity is necessary but nowhere near
sufficient — `0.4623/a` is perfectly uniform and three orders too small.

That is the target handed to the five desks, and it is also the reason to expect
section LIII's outcome (sharpness) rather than section LIV's.

---

# Round XIII — the ledger.  `Bcap` is sharp, and the target was never reachable

## 1.  Exact `Bcap` derivation, and what it discards

`Bcap a = Σ_(i<a) 3^(a−1−i)·2^(fexp i)` against `C(w) = Σ_i 3^(a−1−i)·2^(t_i)`: it bounds
each `t_i` by `fexp i` **independently**.  The clean way to see it is the **slack**
`s_i = i·log₂3 − t_i`, in which

> `C = 3^(a−1) · Σ_(i<a) 2^(−s_i)`,  and `max C` is *pointwise* minimisation of each
> `s_i` separately.

Since gaps are integers, `s_i ≡ {i·log₂3} (mod 1)`, and heaviness is `s_i ≥ 0`; so the
minimum is `{i log₂3}` and `t_i = fexp i`.  Two lines, uniform in `a`, no induction over
words.  Byproduct: `Bcap a = 3^(a−1)·Σ 2^(−{i log₂3})`, hence
**`Bcap/(a·3^(a−1)) → 1/(2 ln 2) = 0.7213475`** (measured `0.7216799` at `a = 4296`), with
`a·3^a ≤ 6·Bcap a ≤ 2·a·3^a` proved.

## 2–4.  Minimum phase, the minimum interval, ordered times

**Heaviness implies minimum phase** (`MinimumInterval.minPhase_of_heavy`, zero axioms):
minimum phase is `G·C^(i) ≥ (2^(t_i) − 3^i)·C`, heaviness is `2^(t_i) ≤ 3^i`, so the
right side is non-positive while the left is non-negative — it holds before the
accumulator term is spent.  `M(w) = C/G` exactly, so `C/G` is always the *right endpoint*
of its own minimum interval and **every heavy word survives `C/G ∈ I(w)`**.  Minimum
phase is strictly *weaker* than heaviness (`t = (0,1,3,5,6,8)` at `a = 6` is min-phase,
not heavy, `C = 1357 > 1085 = Bcap 6`), and `max{C : min-phase} = 1.52·Bcap` at `a = 12`.
Strictness buys nothing.  **Sections XLIV–XLVIII closed, reduction identically 0.**

## 5–6.  The extremal ordering, and what removes it

The extremizer is the Sturmian word of slope `a/L`, built only from blocks `10` and
`110` — no `111`, no `00` — with discrepancy width `0.9999`.  Its idealised orbit is
`x_i/n = 2^(i log₂3)` exactly, so **every odd element lies in `[n, 2n)`**.

**It is a genuine cycle.**  With `g = gcd(G, Bcap a)`, `d = G/g`, `n = Bcap a/g`, the
Beatty word closes exactly under `x ↦ (3x+d)/2^v` with minimum `n`.  Smallest case,
kernel-checked: `d = 47`, `n = 85`, `85 → 151 → 125 → 211 → 85`, and indeed
`Bcap 4 = 85`, `2^7 − 3^4 = 47`.  Verified closing at `a = 5, 6, 7, 10, 17, 25, 100`.

Consequently **no `d`-independent constraint can remove it**:

| constraint | verdict | reduction |
|---|---|---|
| minimum phase | implied by heaviness | **0** |
| leaf (no element `≡ 0 mod 3`) | vacuous for *every* word: `C ≡ 2^(t_(a−1)) (mod 3)`, so `3 ∤ C` always | **0** |
| `O0 E^m O0` ban | vacuous: a theorem about *every orbit*, hence forbidding no word.  It is `log₂3 − 1 > 1/2` restated, and its counting content `a/L ≤ 2/3` is weaker than heaviness' `0.63093` | **0** |
| heavy-window | *is* the box | **0** |
| `G ∣ C` | the only one — and using it is circular, since heavy + `G∣C` **is** "this is a cycle word" | 0.05% of the distance |

**This corrects Round XII**, which reported the `O0 E^m O0` ban as a "genuinely new
non-local constraint".  It is non-local in *time* precisely because it is local in the
*odd index*, and locality in the odd index is exactly blindness to the gaps.

## 7.  Uniform improvement: it does not exist, twice over

**(a) The plateau.** `BcapSharp.sharp`: for every selector `S` firing only at two-jump
indices, the lowered word is strictly increasing, heavy, and has `C ≥ (1 − s/a)·Bcap`.
All `2^(0.585a)` subsets are admissible, so a `β`-improvement must exclude
`C(0.585a, βa)` heavy words — `> 10^700` at `β = 0.2, a = 4296`.

**(b) And a constant factor was never enough.**  Exactly
`Bcap/G = (1/(6 ln 2))·a·(1−ε)/ε` with `ε = 1 − 3^a/2^L`, and `ε` returns toward `0`
along the convergents of `log₂3`.  The *surviving fraction* a bound must achieve tends
to zero:

| `a` | `Bcap/G` | required fraction |
|---|---|---|
| 4296 | 1358717.75 | 0.79962 |
| 10281 | 6728242.48 | 0.16148 |
| 14936 | 58068030.82 | 0.01871 |

> **Since `Bcap` is attained, any bound `C ≤ K·a·3^(a−1)` clears only finitely many
> ledges, for every constant `K`.**  A constant-factor improvement was never sufficient
> — and neither is surrendering the whole factor of `a`.

## 8.  Frontier impact

None, and none was available.  Excluding `(6809, 4296)` needs `20.038%` off `Bcap`;
removing the extremizer gives `0.01076%`.  Note the near-miss on record: `(5755, 3631)`
clears by **409** integers of verified range out of `1086464` — `0.038%`.

## 9.  The remaining lemma, restated

The standing formulation — *a bound on the cycle minimum that reads the ordering and
beats `Bcap` uniformly in `a`* — is now **provably unsatisfiable as a bound on `C` over
heavy words**, from both sides of §7.

> **The remaining lemma must read something the parity word does not determine — the
> criterion `G ∣ C` itself, or `Bcap a mod G` — and not the word's ordering, its
> octave decoration, or its gaps.**

Section LIII's outcome, anticipated in the brief, is the actual outcome.  The extremal
family is named: the Beatty corner with any subset of its two-jump coordinates lowered
by one — `2^(0.585a)` words, all heavy, all min-phase, all octave-legal, all leaf-legal,
each a genuine cycle of some `3x+d`.  **The single property separating them from genuine
`3x+1` cycles is `d = 1`.**  There is no dynamical, combinatorial, or octave-level
property that does it.

---

# Round XIV — the target is the conjecture, and the repository has said so since Round IV

Round XIV asks for a concentrated attempt to close the cycle half, with the boxed dream
theorem

> `∀ w nontrivial cyclic, δ(w) > 1`,  equivalently  `G(w) ∤ C₁(w)`.

**That is the cycle half of Collatz restated, not a route to it**, and this is not a new
observation — `CLOSURE.md:203` has said so since Round IV:

> *"`gcd(C, G)`, equivalently `δ(w) = G/gcd(C,G)` — 13 theorems, the least connected
> cluster in the index, and **`δ ≥ 2` is the conjecture restated**"*

with `RESEARCH.md:2333` repeating it.  The chain is one line:
`δ(w) = 1 ⟺ gcd(G,C) = G ⟺ G | C ⟺ w is a 3x+1 cycle word`.

## And the round's framing question has a trivial answer

> *"Why can every other `3x+d` realize the extremal word, but `d = 1` cannot?"*

Because for **any** word, `d = δ(w)` realizes it.  There is nothing special about `d = 1`
except that `1` is the smallest positive integer, and `δ(w) = 1` is the exact coincidence
`G | C`.  Measured on the Beatty-corner extremal family (exact integers):

| `a` | 4 | 7 | 10 | 17 | 25 | 50 | 100 | 300 |
|---|---|---|---|---|---|---|---|---|
| bits of `G` | 6 | 11 | 13 | 23 | 38 | 79 | 158 | 475 |
| bits of `gcd(G,C)` | 1 | 1 | 1 | 1 | 1 | 4 | 1 | 3 |
| bits of `δ` | 6 | 11 | 13 | 23 | 38 | 75 | 158 | 472 |

`δ ≈ G` throughout — the gcd is essentially trivial, and `d = 1` is astronomically far
from the realizable value.  So "the extremal words are cycles for other `d`" is not a
clue about `d = 1`; it is the generic situation, and `d = 1` is the exceptional one *by
being small*, which is exactly the content of the conjecture.

## What this does and does not close

It does **not** mean the round is empty.  It means the deliverable cannot be the boxed
theorem, and any agent that "proves" it has assumed something equivalent.  What remains
genuinely open and non-circular:

* the **rotation identities** — `C(uv)` against `C(vu)`, and whether imposing all `L`
  rotation conditions simultaneously is stronger than imposing one.  Cyclicity has never
  been used globally in this programme;
* the **two-jump family mod `p`** — `C(ε) = Bcap a − Σ ε_i λ_i` is *affine* in `ε`, so
  "does some `p | G` avoid all `2^m` values of `C(ε)`" is a **subset-sum question mod
  `p`**, finite per `(L,a)`, and not the conjecture;
* **exact gcd identities** constraining `gcd(C,G)`, and the valuation picture;
* and the honest audit the brief's sections 57/58/72 demand — *which half is actually
  proved*.

Those are the five desks this round, and the fifth is an integrity auditor whose only
job is to establish what the repository has and has not proved, because the brief
contemplates a completeness claim and the divergence half is — on the evidence of Round
X — wide open.

**Standing instruction for the rest of this programme:** a proposed theorem whose
hypotheses or conclusion are equivalent to `G ∤ C` is the conjecture wearing a
different notation.  `CLOSURE.md` diagnostic 5.

---

# Round XIV — the integrity audit, and the gap stated without softening

The brief's sections 57, 58 and 72 demand that both halves be audited before any
completeness claim.  A dedicated desk did that and did not attack the conjecture.

## The divergence half is OPEN — and provably out of reach of the current toolkit

`Complexity.collatz_iff_halves` is **bookkeeping, not progress**: `DivergenceHalf` and
`CycleHalf` are `def … : Prop`, both directions of the iff are proved, and **neither
conjunct is proved, assumed, or discharged anywhere.**  `Escape.divergent_avoids_verified`
excludes divergence only for starts below `1 086 464`; above that it says only that a
divergent orbit never dips into the verified range.  Every theorem in the library
concluding `¬ Divergent n` carries a hypothesis at least as strong as the divergence
half itself — several are outright *iff*s.

And `ScaleRecord.divergence_filter` proves the toolkit *cannot* close it: `expStep`
agrees with the accelerated map on every odd input, satisfies the identical affine law,
is heavy at every scale, and **every one of its orbits provably diverges**.

## The cycle half is a length *bound*, not an exclusion

`length_ge_6809` asserts nothing about `L ≥ 6809`.  Combining it with
`cycle_length_determined` (`L = ⌊a log₂3⌋ + 1`) and `cycle_min_window` leaves — recomputed
exactly — **169 admissible `a` in `[4296, 20000]`**, beginning `4296, 4602, 4908, 4961,
5267, 5573, 5626, 5932`, and the window is **vacuous for `a ≥ 1.5c ≈ 1 629 696`**
(confirmed: admissible at `a = 1 700 000`, not at `1 600 000`).  The admissible set is
**infinite**.

One scoping gap named: `length_ge_6809` is about `AccIsCycleOf`, while
`Complexity.CycleHalf` is stated for the standard map, and **there is no proved bridge
`Periodic m → AccPeriodic m`** in the repository.  Not a defect — the accelerated
decomposition is sound and complete and the two conjectures are proved equivalent — but
currently an implicit step.

## No circularity, and `δ` is a refutation file

`DeltaSpectrum` does not assume `δ ≥ 2`; `delta_no_growing_bound` **kills** the route,
proving any valid lower bound `f` satisfies `f 27 ≤ 5`, `f 24 ≤ 13`, `f 23 ≤ 79`,
`f 26 ≤ 233`, `f 32 ≤ 499`.  A machine scan of all 2 871 public statements found exactly
one whose unconditional conclusion mentions the conjecture — a `rfl` definitional
identity.  All 233 `chain*` theorems carry named, undischarged hypotheses, and
`Chains/Index.lean` explicitly labels the group *"Equivalent to Collatz … so not
progress"*.

## Integrity

196 files, 51 865 lines, **2 893 declarations**, `0` each of `sorry`, `axiom`,
`native_decide`, `skipKernelTC`, `implemented_by`, `partial`, `unsafe`, `opaque`.  Clean
rebuild from an empty `.lake`: **198/198 jobs, 10 m 07 s**.  Full axiom footprint across
every resolvable declaration is exactly `{propext, Classical.choice, Quot.sound}` — 534
depend on none at all.  No finite bound is presented anywhere as a universal one.

*Prose defects found and now fixed:* `README` claimed 1158 theorems and a `307 200`
verified range (both stale, in the understating direction); the `G(i)` table mixed floor
and ceiling, so `max_{i<4296} G(i)` is `1 086 054`, not `1 086 055`, with margin exactly
`410`; and `Complexity.lean` / `GapSandwich.lean` printed a staircase mixing the `Bcap`
and `Bstar` criteria, whose next rung is `1 358 718` and not `1 359 157`.  None is
load-bearing; all are annotated at the source.

## The gap, stated as the auditor stated it

> This repository proves that Collatz is equivalent to a `Π₂` divergence half and a `Π₁`
> cycle half; that every positive integer below `1 086 464` reaches 1; and that no
> accelerated cycle through a non-reaching point has length below `6809` — leaving
> `L = ⌊a·log₂3⌋+1` with `a ≥ 4296` and an **infinite** admissible set.  It further
> proves the divergence half admits no argument built from the affine law, the parity
> word, heaviness and positivity, and no ranking, WQO or size-change certificate.
>
> **It does not prove either half.  Not one cycle above `L = 6809` is excluded, and not
> one divergent orbit above `1 086 464` is excluded.  The gap is the whole conjecture:
> an unbounded cycle-length exclusion, and a divergence argument that consumes the even
> branch's contraction `oddCount n j < j` — the one datum every mechanism here so far
> avoids.**

---

# Round XV — the toolkit break, and one thing checked before it started

## The brief's main target is the conjecture verbatim

Part X names `∀ n > 1, ∃ k, T^k(n) < n` as the round's main target.  The repository
already proves

> `NeverDrops.collatz_iff_neverDrops : CollatzConjecture ↔ ∀ x, NeverDrops x → x ≤ 1`

and `NeverDrops x` is exactly "no `k` has `T^k(x) < x`".  So the target *is* the
conjecture, not a route to it — the third round running where the headline goal restates
what is to be proved.

**But — and this is the correction Round XIV forced on me — that does not close the
branch.**  The same statement on an explicitly characterized class is a real theorem, and
the live, non-circular form is the brief's own §16:

> find a modulus `M` and finitely many certified descent blocks such that *every*
> sufficiently large `n` in *every* residue class mod `M` has some `k` with `T^k(n) < n`.

That is a genuine theorem for each `M` certified, it is the classical Terras/Everett
route, and it is what the descent desk was actually pointed at.

## The premise the round is built on, restated exactly

`ScaleRecord.divergence_filter` (LEAN_PROVED): `expStep x = 3x/2` (even), `(3x+1)/2`
(odd) agrees with the accelerated map on **every odd input**, satisfies the identical
affine law, is heavy at every scale, is positive — and **every one of its orbits
diverges**.  So

> affine law + parity word + heaviness + positivity ⊬ termination,

and the missing datum is the even branch's exact contraction, `oddCount n j < j`.  Every
desk this round is required to test its results against `expStep` and report the outcome
explicitly; a theorem `expStep` satisfies cannot be the missing mechanism.

## The Mathlib branch

`MathlibAttack/` is a **separate Lake project** with its own `lakefile.toml` and its own
toolchain (`lake update` resolved it to `v4.34.0-rc2` from Mathlib's manifest).  It
defines `T` and the Syracuse map `S n = (3n+1)/2^(padicValNat 2 (3n+1))`.

**Isolation is a hard requirement and is verified**: the root `Collatz` library remains
Mathlib-free, still builds (202 jobs), and contains zero references to `MathlibAttack`.
Build artifacts are gitignored.

The specific reason to want it: `padicValNat` is the one piece of machinery the
hand-rolled branch cannot easily build, and this round's central question is precisely
*what object sees the exact contraction `n ↦ n/2`*.

## Round XV — the first mechanism that sees the even branch, and why it still cannot finish

The covering desk produced the round's real result, and it has two halves that must be
stated together.

### It sees the contraction.  Provably.

Round X's `expStep` showed that affine law + parity word + heaviness + positivity cannot
prove termination, and named the missing datum as `oddCount n j < j`.  **A residue-class
descent certificate consumes exactly that**, and it is the first mechanism in fifteen
rounds that does:

* `oddCount_lt_of_descendsLarge : DescendsLarge k r → oddCount r k < k` — a certificate
  cannot exist without at least one even step;
* `expStep_never_descends (k) : ¬ (3^k < 2^k)` — `expStep`'s `k`-step multiplier is `3^k`
  on **every** class, because its even branch multiplies by `3` too.  **No residue class
  admits a descent certificate for `expStep`, at any modulus and any block length.**

Concretely, on one class, verified exactly: `T^8(256m + 7) = 243m + 8` against
`E^8(256m + 7) = 6561m + 201`.  Same class, same `k`, same affine shape — `243 < 256` for
Collatz, `6561 > 256` for `expStep`.  The certificate is not the wrong object; it is a
consumption of the right one.

A concrete new theorem with a sharp threshold, LEAN_PROVED:

> **`drop_seven_mod_256 : n % 256 = 7 → 263 ≤ n → acceleratedOrbit 8 n < n`.**

(The crude generic threshold would give `n ≥ 2304`; the gap-aware form gives `263`, and
`n = 7` itself is correctly excluded since `T^8(7) = 8 > 7`.)

### And it provably cannot be completed by a finite modulus

`covering_needs_unbounded_blocks : ¬ ∃ K, ∀ n > 1, ∃ i ≤ K, T^i(n) < n`, from
`no_bounded_descent_time (K) : ∃ n > 1, ∀ i ≤ K, ¬ T^i(n) < n` with witness
`2^(K+2) − 1` — verified for `K = 1 … 15`.  A level-`K` certificate uses at most `K`
steps, so **no finite `M` completes the covering, unconditionally and independently of
Collatz.**  Section 16 is closed as posed.

The failure is **uniformity, not density**.  The failing set is exactly the **ballot
set** — parity words whose partial-sum path stays weakly above the line of slope
`θ = log 2 / log 3 = 0.63093` — an exact lattice-path cone, not a statistical statement.
Its classes reproduce the repository's own pillar lists: `{7,11,15}` at `K = 4`,
`{7,15,27,31}` at `K = 5`, 8 classes at `K = 6`, 19 at `K = 8`, **64 at `K = 10`**
(= `survivorsMod1024`), 2114 at `K = 16` — all recomputed exactly.

Density does shrink, at rate `2^(−(1−H(θ))K)` with `1 − H(log₃2) = 0.0500445` — **the
same constant, from a fifth direction**.  But the residual at level `K` is exactly
`{n : σ(n) > K}`, and stopping times are unbounded, so the covering cannot terminate.
The failing residues form a Cantor set of box dimension `0.94996`: uncountable, not
thinning to a point.

*Measurement caveat:* at `K = 16` I measure `log₂(fraction)/K = −0.3096`, far from the
asymptotic `−0.05004`; that is consistent with the desk's own `K^(−3/2)` correction and
its `K = 64, 1000, 4000` values (`−0.1467, −0.0616, −0.0537`), which I did not
independently rerun.  Do not read the small-`K` slope as the exponent.

### What this leaves

The object that sees the even branch is now identified and is not exotic: it is a
residue-class descent certificate.  What is proved impossible is finishing with finitely
many of them.  So the next question is sharper than the round's:

> **not "what sees the contraction" — that is answered — but "what supplies a descent
> certificate whose block length is allowed to grow with `n`".**

## Round XV — the valuation/Beatty bridge, and the reverse tree gets a number

### §14 — an empty concept pair, filled

The index reported `2-adic valuation ↔ Beatty/Sturmian` as an **empty pair**, because
`GapVector` builds the whole run-length calculus over a *free* `g : ℕ → ℕ` and never
instantiates it at a real orbit.  Now instantiated.

The convergents of `log₂3` become shift laws for the Beatty ceiling, generic in the
convergent and then instantiated from `PrimeLedge`'s kernel-checked `3^306 ≤ 2^485` and
`2^1054 ≤ 3^665` — both re-verified, and both shift laws checked for all `i < 6000`:

> `fexp (i + 306) ≤ fexp i + 485`  and  `fexp i + 1054 ≤ fexp (i + 665)`.

These bracket the permitted **even-step density** between `389/665 = 0.5849624060` and
`179/306 = 0.5849673203` — width `4.914·10^(−6)`, containing `log₂3 − 1 = 0.5849625007`.

And the block law lands at a real orbit: `orbit_time_le_fexp` extracts `j ≤ fexp (oddCount
m j)` (proved but never named, inside `no_light_window`), giving `even_steps_per_306` — a
never-dropping `m ≥ 1086464` whose first `j` steps contain exactly `306q` odd steps has
`j ≤ 485q`, hence at most `179q` even steps.  `gapT_gapC_of_orbit` finally instantiates
`GapVector` at an orbit, so the box `gapT g i ≤ fexp i` is **derived rather than assumed**.

**Honest verdict:** the convergents constrain valuations to *precisely the number* they
constrain `(L,a)` to.  `BeattyStability.corner_is_a_real_cycle` says why nothing more is
available — the extremal valuation profile is a genuine cycle of `x ↦ (3x+47)/2^v`, so no
consequence of the valuation profile alone can see `d = 1`.  Class 1 by identity, now
proved on the valuation side rather than assumed there.

### §15 — the reverse tree, with a number attached

Two exact inequalities bracket a reverse path `T^k(x) = y` above a floor `B`, and
linearise (`reverse_pinch_one_bit`) whenever `2a ≤ 3B` to

> `3^a · x ≤ 2^k · y ≤ 2 · 3^a · x`.

Verified on 1500 never-dropping prefixes above the verified range.  Round XIV put the
whole reverse tree of a counterexample above `1086464`, so this holds for every reverse
path with `a ≤ 1 629 696` odd branches; the true window is `a/2 259 238` bits, so shape
freedom does not reach **one bit** until `a ≈ 2.26·10^6`.

> **The reverse tree above a counterexample has essentially one shape `(k,a)` per
> endpoint pair.  All of its `(4/3)^k` branching is in the choice of divisibility class,
> none of it in the shape.**

That converts "the reverse tree is a relabelling" — the conclusion the brief forbade
repeating — into a *ceiling* rather than a contradiction.  Branch stays dead, now
quantified.

### §13 and §18 — duplicates, and the desk deleted its own file

The cocycle-plus-integrality bound was proved and then found to be **verbatim
`CycleProduct.product_invariant`**; the desk deleted `CocycleIntegrality.lean` rather
than add a duplicate.  Generating functions collapse to the accumulator identity exactly
as anticipated, and the desk wrote no new Lean, citing `ForwardReverse` (whose `gf` at
`(1,1)` and `(1,3)` makes forward heaviness and reverse density the *same* function) and
`ExpSum`'s three recorded kills.

### The `expStep` test — and the pattern is the round's real finding

| result | `expStep` |
|---|---|
| `fexp_shift_*`, density bracket | satisfied — pure arithmetic on `log₂3` |
| `orbit_time_le_fexp`, `even_steps_per_306`, `orbit_run_box` | **fails** (`n = 2^k`: `oddCount = 0`, claim `j ≤ 0`) |
| `reverse_shape_pinned` lower half | satisfied — only needs `C ≥ 0` |
| `reverse_pinch_one_bit`, `product_invariant` | **fails** |

**Every discriminating item discriminates for the same reason: it consumes `2·T(x) ≤ x`,
i.e. `oddCount n j < j`.**  Two desks reached that independently this round — the
covering desk through descent certificates, this one through the Beatty ceiling.  It is
the sharpest confirmation yet of Round X's diagnosis.

*Self-caught error worth recording:* the desk first estimated `2^485/3^306 ≈ 1.3667` from
a half-remembered logarithm and designed a theorem around a `4/3` margin.  Exact
arithmetic gives **`1.0010227`** — I re-verified — and the claim was false.  It caught
this before the constant entered a proof, which is the discipline four previous rounds
were written about.

## Round XV — the valuation transition system is the full shift

The 2-adic desk built the object the brief called its priority, and the result is a
decisive negative with a positive attached.

### The system, exactly

A Syracuse step is `SyrStep n r m := n odd ∧ m odd ∧ 3n+1 = 2^r·m` — this *is*
`r = v₂(3n+1)`, with no valuation function needed.  `val_iff_mod` (LEAN_PROVED): for odd
`n`, a step with valuation `r` exists **iff** `(3n+1) mod 2^(r+1) = 2^r`.  So the
valuation is literally one congruence, and `val_class_unique` says at most one odd class
mod `2^(r+1)` has it.  Recomputed exactly: the classes are
`3 mod 4, 1 mod 8, 13 mod 16, 5 mod 32, 53 mod 64, 21 mod 128, 213 mod 256`.

`path_congr` is the heart — Terras determinacy in the valuation alphabet: `n' ≡ n
(mod 2^(S+k+1))` realizes the *same whole word*.  So word-realizability is exactly a
congruence mod `2^(S+1)`.

### The main negative: every valuation word is realized by an integer

> **`word_realizable` (LEAN_PROVED): every finite word of valuations `≥ 1` is the
> valuation word of an actual odd integer.**

Confirmed independently: all `16`, `64`, `256` words in `[1,4]^L` for `L = 2, 3, 4` are
realized by odd `n < 2·10^6`.  So the valuation transition system is the **full shift on
`{1,2,3,…}`** — no forbidden transitions at any order, and **no finite automaton on
valuations can obstruct anything.**  Brief §§8 and 10 are closed.

Note this is the *opposite* of the usual trap.  The standing warning is "do not confuse
symbolic paths with integer trajectories" because symbolic paths usually fail to lift.
Here they **all** lift, which is worse: the symbolic layer carries no information at all.
The remaining obstruction is archimedean — the `2^S` versus `3^L` comparison — not
automaton-theoretic.

The construction also explains the asymmetry: the *backward* map is genuinely
constrained mod 3 (needing `2^r·m ≡ 1 mod 3`), while the *forward* one is free, because
`t ↦ m₀ + 6t` covers every odd class since `gcd(6, 2^(T+1)) = 2`.

### And it sees the even branch — a third independent route to the same place

`expStep`'s halving exponent is **1 at every step regardless of residue**, so its
alphabet is the single letter `{1}`, giving `S = L`.  The drop criterion `3^L < 2^S`
becomes `3^j < 2^j` — false for every `j ≥ 1`.  `expStep_fails_certificate`
(LEAN_PROVED): `expStep` never drops, at any length, from any positive start.

By contrast `letter_realizable`: the genuine Syracuse valuation takes **every** value
`r ≥ 1`, so `S` is not pinned to `L`.  **The drop certificate is exactly the
`oddCount n j < j` datum, in the form `L < S`.**

That is the third desk this round to land on the same datum by an independent route —
descent certificates, the Beatty ceiling, and now the valuation alphabet.

### Section 9, deterministically, replacing the heuristic

`no_drop_bounds` (LEAN_PROVED): if a run does **not** drop then
`(2^S − 3^L)·n ≤ 2^(S−L)(3^L − 2^L)`.

> **A non-dropping start is *bounded* the moment the halving sum has any surplus over
> `L·log₂3`.**  No logarithms, no floats, no independence assumption.

And the answer to "does the exact arithmetic force large valuations" is **no** —
`word_realizable` shows every deficient valuation pattern is realized by integers at
every finite length.

A non-circular restricted-class theorem, kernel-checked and independently verified for
`n < 2·10^5`: **`drop_of_seventeen_mod_64` — every `n ≡ 17 (mod 64)` with `n ≥ 2` drops
within two Syracuse steps.**  Its word is `[2,3]`, so `S = 5` and `2^(S+1) = 64`.

## Round XV — the Mathlib branch, the survey, and one fact about this repository

### Mathlib has nothing, verified

GitHub code search across `mathlib4` and `mathlib3` for `collatz`/`syracuse`/`hailstone`
returns **zero hits** (control queries return hits, so the search works).  Not in
`docs/100.yaml`, `1000.yaml`, or `undergrad.yaml`.  The only "official" Lean statement is
a `sorry` stub in `google-deepmind/formal-conjectures`.  **The AFP has no Collatz entry
either.**

The one piece of genuine leverage the Mathlib branch found is
`le_padicValNat_iff_residue` — `v₂(3n+1) ≥ k ↔ (n : ZMod (2^k)) = −(3 : ZMod (2^k))⁻¹` —
and its verdict is honest: **narrow.**  `padicValNat` is not kernel-reducible, so the
hand-rolled valuation stays better for anything `decide`-driven.  Two reproofs did come
out shorter: the ℤ-valued `cycle_iff` drops all three hypotheses the no-Mathlib version
needs, and Terras surjectivity falls out of counting in ~5 lines against 82.

### The soundness incident, and why the audit was hardened this round

`xrchz/CollatzLean` (July 2026) claims `¬ Conjecture` with **no `sorry`, no `axiom`**, and
its CI passed `leanchecker`, a `--fresh` replay, **and** nanoda with
`permitted_axioms: []`.  It is a deliberate exploit: proof terms built by hand with
`mkProj`, `letE` and raw `addDecl` past the elaborator, exploiting `leanprover/lean4#14576`
plus a second bug in nanoda.  **Two independent kernels accepted a proof of `False` for
about 2.5 days.**

`scripts/check_integrity.sh` now also greps for `addDecl`, `addAndCompile`, `mkProj`,
`ofReduceNat`, `evalConst` and `liftCoreM` — **negative-tested**: it fires on a planted
`addDecl` and passes on the clean tree.  None of these appear anywhere in `Collatz/`.

> **"Zero `sorry`, zero axioms, two independent kernels" is necessary and not
> sufficient.**  That belongs in this project's standing discipline.

### One fact about this repository, stated carefully

The survey's finding: *no* Lean, Coq, Isabelle or ACL2 artifact certifies "every
`n < N` reaches 1" for any interesting `N`; Barina's `2^71` and Oliveira e Silva's tables
are plain C/GPU, argued correct on paper only.  Its measured kernel-honest ceiling for a
naive encoding was `N ≈ 10^4` — `decide +kernel` took 103 s at `N = 5000` and failed to
finish `N = 20000` in eight minutes.

This repository proves `Search.reachesOne_of_lt_1086464` with **zero `native_decide`
anywhere in the library** (re-verified), discharged through `reachesOne_of_blocks` over
`1061` residue blocks — and that module kernel-checks in **1.3 seconds**.

The difference is not compute; it is the same idea the covering desk used this round: a
*certificate per residue class* rather than per integer.  If the survey is right about the
rest of the ecosystem — I have not independently re-checked its whole inventory — then
`1 086 464`, kernel-honest, is the largest verified Collatz range in any proof assistant,
by about two orders of magnitude.

That is worth stating precisely because it is *not* progress on the conjecture.  It is a
finite result, and this repository's own gap statement says so.

### Carried forward

`Papers/Terras1976.terrasDensityOne` is still an unproved `Prop` referenced nowhere, and
`lechmazur/terras_density_one` formalizes exactly it (`HasNatDensity {n | ∃ k,
accelerated^[k] n < n} 1`, sorry-free).  Mathlib has **no natural-density definition for
sets of naturals**, which is why that statement sits unproved here.

## Round XVI — lifting the exponent, built from scratch, and what it does not buy

### The gap `INDEX.md` was pointing at

The concept index reported the 2-adic valuation as the thinnest cluster in the
development — 17 theorems — and listed it as having **no theorem in common** with the
gap `G = 2^L - 3^a`, with `C mod 2^j`, with the parity word, or with residue classes.
Four missing bridges out of one cluster is not a coincidence; it means the branch had no
usable valuation object at all, only valuations spelled out inline as `3n+1 = 2^r * m`.

`Collatz/Strategy/LiftExponent.lean` builds one.  `Val2 n r` is `∃ m, m % 2 = 1 ∧
n = 2 ^ r * m` — an explicit witness rather than a function, matching the convention
already used in `ValuationTransition`.  It is shown unique, total on the positives,
multiplicative, ultrametric on sums with unequal valuations, monotone along divisibility,
and equivalent to both the textbook sandwich `2^r ∣ n ∧ ¬ 2^(r+1) ∣ n` and to the single
congruence `n ≡ 2^r (mod 2^(r+1))`.  That last equivalence is the residue-class bridge:
it makes every 2-adic statement in the file re-readable as a congruence and back.

### The formula

  **`v₂(3 ^ a - 1) = v₂ a + 2` for even `a`, and `1` for odd `a`.**

Mathlib proves this as `padicValNat.pow_two_sub_one`; this branch may not use Mathlib, so
it is proved here from the definition of `Val2` up.  The whole thing turns on `3` having
order `2` modulo `8`: `3^k ≡ 1` or `3` mod `8` by parity of `k`, which fixes the three
base valuations `v₂(3^odd - 1) = 1`, `v₂(3^odd + 1) = 2`, `v₂(3^even + 1) = 1`.  The
ladder is then `3^(2b) - 1 = (3^b - 1)(3^b + 1)`, climbed by induction on `v₂ a`, with
`Val2.mul` doing the adding.  Six numerical checks are in the file, including `a = 6`,
where the valuation *drops* relative to `a = 4` — it tracks `v₂ a`, not `a`.

### The payoff, and the honest limit on it

The formula gives the exact order of `3` modulo `2^L`:

  **`2^L ∣ 3^a - 1 ↔ 2^(L-2) ∣ a`, for `L ≥ 3`** — so `3^a mod 2^L` is periodic in `a`
  with period exactly `2^(L-2)`, minimality included.

That is the first exact `L`-versus-`a` constraint in the development, and it is a genuine
finite-state fact about the tripling side.  Read contrapositively it says a short tripling
count is never trivial mod `2^L`, which bounds how far any `2^L` congruence argument can
reach.

**It is not a cycle obstruction, and the file says so in a theorem.**  A cycle has `a ≤ L`.
From `L = 5` on, `L < 2^(L-2)`, so `a < 2^(L-2)`, so `2^L ∤ 3^a - 1`:
`vacuous_for_cycle_shapes` proves the hypothesis of the bound is **false for every shape a
cycle can have**.  The round supplies an exact formula and zero exclusions, and that is
recorded so a later round does not mistake the one for the other.

### The bridges that did land

- **valuation ↔ residue classes**: `Val2.iff_mod`, plus its numeral faces at `r = 1, 2`.
- **valuation ↔ gap**: `val2_gap` puts `2^L - 3^a` at valuation zero, and `val2_gap_mul`
  draws the consequence — the gap is *2-adically invisible*.  In the affine law
  `(2^L - 3^a)·n = C` that reads `v₂(C) = v₂(n)`: the accumulator of a cycle carries
  exactly the 2-adic content of the cycle minimum, no more and no less.
- **valuation ↔ parity word / transition system**: `Collatz/Strategy/ValuationBridge.lean`
  identifies `SyrStep n r m` with `Val2 (3n+1) r` in both directions, which hands the
  transition system a bound it did not have — `2^r ≤ 3n+1`, one step halves at most
  `log₂(3n+1)` times — and reproves the exact-contraction criterion `r = 1 ↔ n ≡ 3 (mod 4)`
  on the no-Mathlib side, matching what the Mathlib branch found through `padicValNat`.

### Carried forward

The two branches now prove the same lifting-the-exponent statement by different routes:
`MathlibAttack.padicValNat_three_pow_sub_one` through `padicValNat.pow_two_sub_one`, and
`LiftExponent.val2_three_pow_sub_one` from the definition.  The no-Mathlib version is the
one that composes with the rest of this library, and unlike `padicValNat` it reduces in
the kernel.

### What the index says afterwards, precisely

Regenerating `INDEX.md` moves the 2-adic cluster from **17 to 65** theorems and drops
`2-adic valuation <-> gap G=2^L-3^a` and `2-adic valuation <-> finite-state` off the
unbridged list.

Two caveats, because the index is a regex over statement text and not a semantic check.

First, the heuristic had to be *taught the name*: its 2-adic tag matched `v2`,
`two_pow_dvd` and `valuation`, none of which occur in `Val2`.  Adding `\bVal2\b` to that
tag is a fix to the tool — the concept acquired a canonical name in the library this
round — but it is worth flagging that the 17 → 65 jump is partly the tool catching up and
not only new theorems.

Second, `2-adic valuation <-> residue classes` is **still listed as unbridged, and that
listing is wrong**.  `Val2.iff_mod` is exactly that bridge.  It goes unnoticed because the
residue-class tag looks for the strings `Congruence`, `residue` or `_class`, and the
theorem says `n % 2 ^ (r+1) = 2 ^ r` without using any of those words.  The renaming that
would satisfy the regex has not been done: the index is a search aid, and editing names to
please it would cost more than the false entry does.

## Round XVI — the excursion map (proof round)

This is the proof round.  There is no proof of Collatz.

### Target A as written is the full conjecture

`∀ n > 1, ∃ k, T^k(n) < n` is `NeverDrops.collatz_iff_neverDrops` / 
`ExcursionMap.collatz_iff_return`.  A nontrivial cycle's minimum never drops, so
return-below-start kills cycles and divergent orbits together.  The two-half split in
the brief is the right split for *boundedness* versus *trivial cycles*; it is the wrong
split for return-below-start.  Stating them as independent remaining tasks would be a
rename.

### What the free-shift theorem does not say

`word_realizable` is about *finite* words and *varying* starts.  A single integer
determines its valuation word.  That word is generated by the excursion map:

  `n + 1 = 2^v u` (`u` odd),  `W = v₂(3^v u − 1) ≥ 1`,  `e = (3^v u − 1) / 2^W`.

`IsExcursion` / `exists_excursion` / `landing_eq` identify this with the accelerated
orbit.  `W ≥ 1` is the even branch: after a maximal odd run the state is even, and
Collatz divides by two.  `expStep` does `3x/2` there and has no `W`.

### Exact one-step criterion (LEAN_PROVED)

`drop_iff`: the landing is below the start **iff** `3^v u + 2^W ≤ 2^{v+W} u`.
No size lower bound.  `RunDescent.drops_of_excursion` needed `2^{v+W} ≤ n`, which
already fails at `n = 5`.  `drop_needs_surplus`: a one-step drop forces `3^v < 2^{v+W}`.
`no_drop_of_light`: if `2^{v+W} ≤ 3^v` the excursion cannot drop.

Worked checks: `five_drops` (`5 → 1` in one excursion); `seven_first_excursion` /
`seven_no_first_drop` (`7 → 13`, and `2^{4} = 16 ≤ 27`, so the first excursion of a
`3 mod 4` start need not drop).  Lemma X is not a first-excursion statement.

### The class `v = 1`, closed (LEAN_PROVED)

`v_eq_one_iff`: `v = 1` iff `n ≡ 1 (mod 4)`.
`drop_of_v_one`: every odd `n > 1` with `v = 1` drops in one excursion.
The proof uses `W ≥ 1` and is false of any map that does not divide by two on evens.
`even_branch_contracts`: even `n > 1` drops immediately (`n/2`).

Together: Collatz reduces to odd starts `≡ 3 (mod 4)`.  That reduction is not new —
`Reductions.collatz_of_one_pillar` already had it — but it is now reached through the
exact excursion criterion rather than through the residue sieve.

### Lemma X (OPEN)

```
LemmaX :=
  ∀ n, n odd → 1 < n → ∃ e, ExChain n e ∧ e < n
```

Equivalently: along the `(v,u)` orbit of every odd `n > 1`, the inequality
`3^v u + 2^W ≤ 2^{v+W} u` fires at some generation.

`collatz_of_lemmaX` (LEAN_PROVED): Lemma X implies Collatz.
`lemmaX_of_one_mod_four` (LEAN_PROVED): Lemma X holds on `1 mod 4`.
`collatz_of_lemmaX_three_mod_four` (LEAN_PROVED): Collatz follows from Lemma X on
**only** `n ≡ 3 (mod 4)`.

That last class is the first surviving class of the residue sieve.  The remaining
content is not a new obstruction.  It is the same class, now required to produce an
excursion iterate below itself, with the exact arithmetic of `W = v₂(3^v u − 1)` as
the thing a proof must consume.

The cycle half is not a second remaining lemma under this architecture: return-below-start
already forbids a nontrivial cycle minimum.  If a later round proves only boundedness
of orbits, then `CycleHalf` reopens; that is not the present gap.

### Plus-five invariant (LEAN_PROVED)

`n + 5` is a complete invariant of the first excursion of an odd start:

| `v₂(n + 5)` | First excursion | Status |
|---|---|---|
| 1 | `v = 1` | drops (`lemmaX_of_val2_one`) |
| 3 | `v = 2`, `W ≥ 2` | drops (`lemmaX_of_val2_three`) |
| `≥ 4` | `(2, 1)` light clock | fuel countdown; not a first-excursion drop |
| 2 | `v ≥ 3` (`n ≡ 7 (mod 8)`) | leftover |

`collatz_of_lemmaX_plus_five`: Collatz follows from Lemma X on
`{v₂ = 2} ∪ {v₂ ≥ 4}`.

### Two-step exits that consume later `W ≥ 2` (LEAN_PROVED)

Each of these is a drop below the *original* start, not merely below the
landing.  The complementary light-`W` side is a growth law, not a witness.

| Prefix | Next | Drop | Grow |
|---|---|---|---|
| `(3, 1)`, `v₂(e+5)=3` | `v=2`, `W≥2` | `lemmaX_of_v_three_land_three` | — |
| `(3, 1)`, `v₂(e+5)=1` | `v=1`, `W'≥2` | `lemmaX_of_v_three_land_one_heavy` | `W'=1` always (`71 → 121 → 91`) |
| `(3, 1)`, `v₂(e+5)=2` | `v'=3`, `W'≥3` | `lemmaX_of_land_two_v_three` | `W'≤2` always (`487 → 823 → 695`) |
| `(3, 1)`, `v₂(e+5)=2` | `v'=4`, `W'≥4` | `lemmaX_of_land_two_v_four` | `W'≤3` always (`2663 → 4495 → 2845`) |
| two `(2, 1)`, then rem 3 | `v=2`, `W≥2` | `lemmaX_of_two_light_then_three` | — |
| `(2, 1)`, rem 2 | `v'=4`, `W'≥3` | `lemmaX_of_rem_two_v_four` | `W'∈{1,2}` (`155`, `411`) |
| `(2, 1)`, rem 2 | `v'=3`, `W'≥2` | `lemmaX_of_rem_two_v_three` | `W'=1` always (`91 → 103 → 175`) |
| `(2, 1)`, rem 2 | `v'=5`, `W'≥4` | `lemmaX_of_rem_two_v_five` | `W'≤3` always (`27 → 31 → 121`, `539 → 607 → 577`) |

### Still open (honest)

These are the prefixes whose two-step landing is *forced* above the start,
or whose next run is not one of the lengths above:

- `(3, 1)` then rem 1 with `W' = 1` (the `71` family): the second landing
  grows, as a law.  Lemma X needs a later iterate, not a uniform two-step.
- `(3, 1)` then rem 2 with next `v' ≥ 5`.
- `(2, 1)` rem 2 with next `v' ≥ 6` (NineK collision `v₂(k−1) = 3`).
- Longer `(2, 1)` chains before a rem-3 exit: `(9/8)^k · (9/16)` fails for
  `k ≥ 5`.
- Mixed light after a `(3, 1)` exit that grows (`71 → 91 → 103 → …`):
  11-fuel is spent, plus-five fuel can *increase*, so neither ranking
  continues.

### The `(3, 1)` fuel `11n + 19` (LEAN_PROVED)

There is no integer clock on leftover odd runs (`no_nat_clock`).  The
2-adic clock `16(11e + 19) = 27(11n + 19)` still gives a Lyapunov quantity:
each `(3, 1)` step spends exactly four factors of two (`val2_landing`),
fuel starts at `≥ 5` (`val2_ge_five`), and a second `(3, 1)` step needs
fuel `≥ 9`.  After one step the remainder classifies the landing:

| `v₂(11n+19)` | Remainder | Landing | Next run |
|---|---|---|---|
| 5 | 1 | `e ≡ 1 (mod 4)` | `v = 1` (LandOne) |
| 6 | 2 | `e ≡ 3 (mod 8)` | `v = 2` |
| 7 | 3 | `e ≡ 15 (mod 16)` | `v ≥ 4` |
| 8 | 4 | `e ≡ 23 (mod 32)` | `v = 3`, not `(3, 1)` |
| `≥ 9` | — | — | may be another `(3, 1)` |

This is Clock, written for leftover odd `v`.  It kills infinite consecutive
`(3, 1)` chains.  It does **not** force a drop below the original start:
`r = 5` with `W' = 1` is `71 → 121 → 91`, as a law.

### Parallel attacks (LEAN_PROVED devices, not Collatz)

Six independent approaches.  Full `lake build Collatz` succeeds.  None
closes Lemma X.

| Attack | File | Result |
|---|---|---|
| Combined Lyapunov | `ExcursionLyapunov` | No integer translate `an+b` decreases on both lights **and** `121→91`. Mixed step raises both fuels. |
| `(2,1)^k` rem 1/3 | `ExcursionLightK` | Drops for k=2 rem 1; k=3,4 rem 3. Growth **laws** for k=3 rem 1 `W'=1` and k=5 rem 3 `W'=2`. |
| `(4,1)` clock | `ExcursionFourLight` | Fuel `v₂(49n+65)` spends 5 per step. `(4,1)` then `v=1`,`W'≥2` drops; `W'=1` grows (`47→121→91`). |
| 71-family third step | `ExcursionLandOneNext` | After `(3,1)(1,1)`, third `v''=1` always drops; `v''=2` needs `W''≥2`; `v''=3` needs `W''≥3`. **71 itself grows in three steps** (`71→121→91→103`). |
| Telescoping `drop_iff` | `ExcursionTelescope` | Exact 2- and 3-step criteria. New drop: `(2,1)` then `v'=6`,`W'≥4`. Recovers LandOne/RemTwo. |
| Chain remaining set | `ExcursionChain` | `collatz_of_open_remainder`: Collatz iff Lemma X on `OpenRemainder` (71 family, light-`W` rem-2, first `v≥4` leftover, long light chains). |

### Axiom footprint

`exists_excursion`: `propext`, `Quot.sound`.
`drop_iff`, `drop_of_v_one`, `collatz_of_lemmaX`: `propext`, `Classical.choice`,
`Quot.sound`.  Zero `sorry`.  Zero added axioms.


# Round XVII — the affine accumulator campaign, re-run against a brief that predates it

The brief for this round proposed making `affineC` the central research object and
listed twenty-eight lines of attack.  **Most of them were already executed** —
rounds XI–XIII are that campaign.  What follows separates, item by item, what the
repository already holds from what this round actually added, and then reports the
new results with their reach measured rather than asserted.

## 1.  The brief against the repository

| Brief item | Status before this round | Where |
|---|---|---|
| exact closed form for `affineC` | DONE | `AffineExact.affine_exact` |
| positional formula `Σ 3^(a−i) 2^(p_i)` | DONE | `AccumulatorAutomaton.C_eq_Crel` |
| recursive form, cocycle law | DONE | `AccumulatorArith.affineC_add` |
| divisibility: `v₃(C) = 0` | DONE | `AccumulatorArith.affineC_not_three_dvd` |
| divisibility: `v₂(C)` exactly | DONE | `AccumulatorValuation.affineC_valuation` |
| `C` depends only on `x mod 2^j` | DONE | `AccumulatorClass.affineC_congr_of_mod` |
| minimum affine cost `F(a,j)` | DONE | `three_pow_le_affineC`, `affineC_le` |
| Problem A vs Problem B (realizability) | DONE, **and negative** | every word is realized by exactly one residue mod `2^j`; `maxC(compatible) = maxC(all)`, ratio 1.0000 |
| the `C`-sandwich | DONE, **and negative** | compatibility condition *is* the product bound |
| semigroup / matrix formulation | DONE | `DeviceSemigroup`, `AccumulatorAutomaton` |
| noncommutativity of the affine word | DONE qualitatively | `affineC_add` |
| **exchange law with an exact constant** | **MISSING** | added below |
| **the deficit as a named object** | **MISSING** | added below |
| **first positive-deficit crossing** | **MISSING** | added below |
| **`C` versus `R` as growth rates** | **MISSING, and now closed** | added below |

Two items on the brief's "do not do" list were respected: no new floor comparison,
no new constant chasing `log 2 / log 3`.

## 2.  The deficit — `AffineDeficit` (LEAN_PROVED)

`deficit m j = 2^j·m − 3^a·m`, as an integer.  It is the exact compensation the
window demands of the accumulator, and it obeys the mirror image of the
accumulator's own recurrence:

| step | `affineC` | `deficit` |
|---|---|---|
| odd  | `C ↦ 3C + 2^j` | `R ↦ 2R − 3^a·m` |
| even | `C ↦ C`        | `R ↦ 2R + 3^a·m` |

**The accumulator is fed only by odd steps and the demand only by even steps.**
That is the tension of the problem in two lines (`deficit_succ_odd`,
`deficit_succ_even`).

### The decisive identity, and what it closes

`displacement_identity`:  **`affineC j m − deficit m j = 2^j · (T^j(m) − m)`.**

So the accumulator's surplus over the demand is *precisely* `2^j` times how far
above its start the orbit sits.  Immediate consequences:

* `C ≥ R` at `j` ⟺ the orbit is at or above `m` at time `j` (`deficit_le_iff_no_drop`);
* `C = R` at `j` ⟺ the orbit has returned to `m` — a cycle of length `j`
  (`cycle_iff_deficit_eq_affineC`).

**This closes brief item 14.**  "Determine the exact extremal ratio `C_j / R_j`
over admissible patterns" is not an auxiliary measurement to be estimated: the
ratio *is* the orbit's position, re-encoded.  Any bound on the comparison that is
not already a bound on the orbit is impossible.  Comparing `C` against `R` is a
change of variables on the problem, not a route into it.  Recorded so it is not
re-attempted.

### The forced drop, cycle-free and one window at a time

`drop_of_insufficient`: if `3^a·m + 2^(j−a)·3^a < 2^j·m` then `T^j(m) < m`.

No never-drop hypothesis, no cycle hypothesis, a single window — the brief's item
25 in its cleanest available form.  It is the contrapositive of `affine_slack_bound`
with the quantifier removed, and it is the shape any future contradiction has to
take: exhibit one window whose demand exceeds the positional cap.

### The first crossing (brief item 13)

`crossing_step_even`: the demand starts at zero and **can only become positive on an
even step**.  An odd step multiplies `2^j` by two and `3^a` by three, so it cannot
turn a non-positive demand positive.  `crossing_demand_small`: at the crossing the
demand is still at most `3^a·m`, because the window was heavy one step earlier.

### The even-run freeze

Across an even run the accumulator is frozen (`affineC_even_run`) while the demand
doubles each step.  `neverDrops_even_run`: a never-dropper taking `r` even steps
from `j` must satisfy the window condition at `j + r` **with the cap of time `j`** —
smaller by the whole factor `2^r` than what `neverDrops_window_condition` supplies
at the same endpoint.  Two corollaries:

* `heavy_after_even_run` — `2^(j+r) ≤ 2·3^a` from `2^(j−a) ≤ m`, i.e. the
  conclusion of `heavy_while_few_even` at the endpoint from its hypothesis at the
  start of the run.
* `even_run_le_one_of_balanced` — no two consecutive even steps at a window that is
  balanced-or-light with even count at most `log₂ m`.

## 3.  Reach, measured — the honest half

`even_run_le_one_of_balanced` is **sharp as an inequality and empty as a tool.**
Its balance hypothesis `3^a ≤ 2^j` was tested on every no-drop prefix of every odd
start below `200 000`: it holds at `j = 0` and at no later window, for all 99 999
starts.  A never-dropper is *strictly* heavy at every few-even window past the
origin — 143 876 strictly heavy against 29 999 balanced, and the 29 999 are exactly
one per start, namely `j = 0`.  So the corollary reproduces
`oddCount_pos_of_neverDrops` and nothing beyond it.

`heavy_after_even_run` is non-vacuous but narrow: 1 387 windows below `120 000`
where its hypothesis holds and `heavy_while_few_even`'s does not, zero failures.

## 4.  Mirror audit (brief item 21) — the derivation, not the formula

The mirror is `n ↦ (3n−1)/2`, whose accumulator is the *same* `C` with the opposite
sign: `2^j·T^j(x) = 3^a·x − C` (92 969 checks, zero failures).  So
mirror-never-dropping is `C ≤ −deficit` — an **upper** bound on `C` where the
`3n+1` world has a lower one (92 969 checks, zero failures).

**The asymmetric line is the direction of the cap.**  Every `3n+1` derivation in
`AffineDeficit` consumes `affineC_le` (odd steps last, the maximum); its mirror
consumes `three_pow_le_affineC` (odd steps first, the minimum).  The two extremal
arrangements swap roles.

But the even-run statement itself **survives the mirror, and survives it stronger**:
a mirror even run forces heaviness at its end outright, with no cap needed (57 455
checks, zero failures), and the mirror satisfies the balanced corollary too (50 000
checks, zero failures).  Verdict: **the freeze is not a sign-sensitive mechanism.**
The `+1` does not supply it; the `+1` only degrades it, by the slack `2^(j−a)/m`.
It cannot separate `3n+1` from `3n−1`, whose cycle `5 → 7 → 5` it leaves untouched.

## 5.  The exchange law — `AffineExchange` (LEAN_PROVED)

`AccumulatorAutomaton` proved that every time-blind invariant is vacuous but never
quantified the time-dependence.  This does.

`Crel_bump`:  **`Crel (u ++ (t+1) :: v) = Crel (u ++ t :: v) + 3^|v| · 2^t`.**

At the level of words (`C_exchange`) this is the adjacent transposition `OE ↦ EO`:
the two words have the same length, the same odd count and the same valuation
total, and their accumulators differ by exactly `3^(oddCount v) · 2^(|u|)`.  That
is the exact form of the noncommutativity the multiplicative invariant discards,
since `(2^j, 3^a)` is unchanged by the swap.  `C_exchange_lt`: the swap is a
**strict** increase — an odd step taken later always costs more.

From the one law, both extremes and the exact gap between them:

* `Crel_range`: earliest odd steps, `Crel + 2^a = 3^a`;
* `Crel_range_shift`: latest, `Crel + 2^s·2^a = 2^s·3^a`;
* `Crel_extremal_gap`: the spread at fixed `(j,a)` is `(2^s − 1)(3^a − 2^a)`.

These are `three_pow_le_affineC` and `affineC_le` re-derived from a single exchange
identity instead of two separate inductions.  `Crel_mono` gives the majorization
principle: pointwise-later odd times give a larger accumulator, so among windows of
a fixed shape the never-drop inequality is **hardest at the earliest arrangement
and easiest at the latest** (`window_mono`, `window_of_earliest`).

**What it is worth.**  The order-sensitivity is real and now quantified.  It
excludes nothing, and the reason is already in the repository rather than
rediscovered here: every parity word of length `j` is realized by exactly one
residue mod `2^j`, so the extremal arrangement is always realizable, and
`maxC(never-drop compatible) = maxC(all words)` at every level measured.

## 6.  Verdict on the brief's decisive question

> Can the forced affine contribution be reconciled indefinitely with
> `2^j m ≤ 3^a m + C_j` along a never-dropping orbit?

**Yes, and the identity says why.**  `C_j − R_j = 2^j(T^j(m) − m)` makes the
reconciliation an identity, not a coincidence: a never-dropping orbit reconciles
them at every `j` by definition of never-dropping.  The affine accumulator is not
an independent quantity that a divergent orbit must struggle to keep large; it is
the orbit's own position in different coordinates.  That is the precise sense in
which the `+1` was not, after all, information the product invariant discarded —
it is the same information, losslessly re-encoded, which is exactly why
`(oddCount, affineC)` is a function of `x mod 2^j` and the compatible words are
exactly the mod-`2^k` sieve survivors.

The one place the two objects genuinely decouple is the even run, where `C` is
frozen and `R` doubles.  This round extracted that, and the mirror audit shows the
extraction is sign-symmetric.  The `+1` branch of the research tree is therefore
complete in the same sense the floor-comparison family is: understood exactly,
useful as a supporting lemma, and not the source of the missing divergence
information.

## Axiom footprint

`displacement_identity`, `neverDrops_iff_deficit`, `neverDrops_even_run`,
`even_run_le_one_of_balanced`, `heavy_after_even_run`,
`cycle_iff_deficit_eq_affineC`, `C_exchange`, `Crel_mono`, `Crel_extremal_gap`:
`propext`, `Quot.sound`.  `drop_of_insufficient`, `crossing_step_even`: those plus
`Classical.choice`.  Zero `sorry`.  Zero added axioms.  `lake build Collatz`
succeeds, 251 jobs.

# Round XVIII — two new devices, built against the filters rather than around them

This round did not prove Collatz and does not claim to.  It took the Round XIV
audit at its word — *"a divergence argument that consumes the even branch's
contraction `oddCount n j < j`, the one datum every mechanism here so far
avoids"* — and built two devices designed to make that datum unavoidable.

## 1.  The filters, made quantitative — `DeviceCeiling` (LEAN_PROVED)

`RunAlgebra` puts Collatz in the coordinate `u = x + 1`.  This round asks what the
repository's two *soundness witnesses* look like in that same coordinate.  All
three maps turn out to share one branch exactly:

| map | even `u` | odd `u` |
|---|---|---|
| Collatz `3n+1` | `3u/2` | `(u+1)/2` = `⌈u/2⌉` |
| mirror `3n−1` | `3u/2` | `(u−1)/2` = `⌊u/2⌋` |
| witness `expStep` | `3u/2` | `(3u−1)/2` |

(`ceilStep_shift`, `floorStep_shift`, `expUStep_shift`, `branches_agree`.)  So the
whole difference between `3n+1` and `3n−1` is **ceiling versus floor on the
halving branch**, and the whole difference between Collatz and a map all of whose
orbits diverge is the same branch again.  With sizes:

* `mirror_gap`:     `ceilStep u = floorStep u + 1` — a **constant** perturbation;
* `divergence_gap`: `expUStep u = ceilStep u + (u − 1)` — an **unbounded** one.

`filter_separation` packages both.  This turns the repository's per-device mirror
audit into a single computation: locate a device's dependence on the halving
branch and compare it against `1` and against `u`.  Any inequality stable under a
`±1` change of that branch is satisfied by the mirror, hence cannot exclude the
cycle `5 → 7 → 10 → 5`; `ceil_breaks_mirror_cycle` shows that cycle sits at
`u = 4, 6, 9` and turns on the single odd point `9`, where `⌈9/2⌉ = 5` and
`⌊9/2⌋ = 4`.

`ceilOrbit_shift` proves the conjugation exact at every time, so nothing is lost
or gained in either direction — this is a diagnostic, not an inequality.

## 2.  The swap normal form — `DeviceSwap` (LEAN_PROVED)

In the `u` coordinate the growth branch is a pure `3/2`, so a *maximal* run of it
is a pure exponential.  Compressing that run gives a map with no branching:

`swap23 (2 ^ s · w) = 3 ^ s · w`  (`w` odd),   `nu y = swap23 ((y + 1) / 2)`.

Add one, halve, then trade every remaining factor of two for a three.  `nu` sends
odds to odds and fixes `3`.

**`reaches_one_iff_nu` (the normal form of the conjecture).**  For even `x > 0`,

`(∃ j, T^j(x) = 1)  ↔  (∃ k, nu^k(x+1) = 3)`.

Both directions are proved.  The forward one needs `nu_covers`: the `nu` orbit
visits **exactly** the even points of the accelerated orbit, in order — proved
through `nu_run_invariant`, an induction carrying the current block's start.
Checked first on 9 999 starts by exact list comparison, zero mismatches, and the
block bridge on 599 970 instances, zero failures.

### Why this shape was built

`ScaleRecord.divergence_filter`'s witness has no even branch to speak of.  In the
`nu` picture the even branch is not an event that may or may not happen — it is
the clock.  Each `nu` step is exactly `s + 1` accelerated steps: **one halving,
then `s` triplings** (`nu_block`, `nu_block_oddCount`, `nu_block_evenCount`).  So
after `B` steps

`evenCount = B`,  `oddCount = s₁ + ⋯ + s_B`.

A statement about `B` *is* a statement about `j − a`.  **Every device written
against `nu` passes the divergence filter by construction.**  That is the one
structural gain of the round.

### The one-step dichotomy (exact)

`nu_dichotomy`: with `(y+1)/2 = 2 ^ s · w`,

`s ≤ 1 → nu y < y`   and   `2 ≤ s → y < nu y`,

for `y > 3`.  Growth is decided by a single integer, and the conjecture becomes:
the statistic `s = v₂((y+1)/2)` is `0` or `1` often enough.

### The run-length ledger, and the number

`run_length_ledger`: for a never-dropper, a window of `B` blocks with total run
length `S` satisfies `2 ^ B · 2 ^ S ≤ 2 · 3 ^ S` (inside `2 ^ B ≤ m`), so

`S ≥ (B − 1) · log 2 / log(3/2) = 1.7095 · (B − 1)`.

**A never-dropper's odd runs must average at least `1.7095`.**  The mean of `v₂`
over the integers is `1`; measured over 200 000 starts × 12 blocks the actual mean
is `0.9974`.  So a counterexample needs a **71 % bias** in one natural, bounded
statistic.  `run_length_ledger_forces_long_runs`: with every run of length one the
ledger reads `4 ^ B ≤ 2 · 3 ^ B` and fails from `B = 3` — the threshold is `B ≤ 2`,
not `B ≤ 1`, since `16 ≤ 18` still holds.

## 3.  Honest verdict

**Neither half is closed, and neither device closes one.**

* Both are *normal forms*.  `ceilOrbit_shift` and `reaches_one_iff_nu` are exact
  conjugations, so by construction they cannot prove anything the accelerated
  coordinate cannot express.  `run_length_ledger` is `CycleProduct` heaviness in
  new letters; the `1.7095` is `log 2 / log 3` rewritten, not a new bound.
* The gain is structural, not quantitative: the even branch has moved from a
  hypothesis into the time variable.  That defeats
  `ScaleRecord.divergence_filter` — which is necessary, not sufficient.
* **The mirror is untouched.**  `3n − 1` has the same `nu` up to the `±1` of
  `mirror_gap`, so the cycle half is exactly where Round XIV left it.
* What is still missing is unchanged and is not a matter of coordinates: an
  inequality that is *false* for `⌊u/2⌋` and *true* for `⌈u/2⌉`.  Everything in
  this round is stable under that swap except the two `gap` theorems themselves,
  which are statements *about* the swap rather than consequences of it.

## Axiom footprint

`ceilOrbit_shift`, `filter_separation`, `run_length_ledger`: `propext`,
`Quot.sound`.  `reaches_one_iff_nu`, `nu_covers`, `nu_dichotomy`: those plus
`Classical.choice`.  Zero `sorry`.  Zero added axioms.  `lake build Collatz`
succeeds, 253 jobs.

# Round XIX — the target inequality, produced and then measured

Round XVIII closed by naming what was missing: *an inequality false for `⌊u/2⌋`
and true for `⌈u/2⌉`*.  This round produces one, from a single telescoping
identity, and then reports what it is worth.  **It is worth the classical
dichotomy and nothing more.**

## The two laws differ in one character

In the swap coordinate, for odd `y` with `s = v₂((y±1)/2)`:

`2 ^ (s+1) · nu y  = 3 ^ s · (y + 1)`   (`nu_identity`)
`2 ^ (s+1) · mnu y = 3 ^ s · (y − 1)`   (`mnu_identity`)

Both come from one lemma, `swap_law`, applied to `(y+1)/2` or `(y−1)/2`.  That
single character is the whole of `DeviceCeiling.mirror_gap`.

## Telescoping, and the separation

Multiplying along a cycle and cancelling the shared product (`orbProd_rotate`,
`morbProd_rotate`) gives

`2 ^ (S+B) · ∏ yᵢ = 3 ^ S · ∏ (yᵢ + 1)`   (`nu_telescope`)
`2 ^ (S+B) · ∏ yᵢ = 3 ^ S · ∏ (yᵢ − 1)`   (`mnu_telescope`)

with `S` the accelerated odd-step count and `S + B` the accelerated length.  Since
`∏(yᵢ+1) > ∏ yᵢ > ∏(yᵢ−1)`, the same three lines give opposite conclusions:

* **`cycle_light`** — a Collatz cycle has `3 ^ S < 2 ^ (S+B)`;
* **`mirror_cycle_heavy`** — a mirror cycle has `2 ^ (S+B) < 3 ^ S`.

`separation` states them together.  Witnesses, all by `decide`:
`three_cycle_light` (`3 < 4`, the image of `1 → 2 → 1`), `nine_cycle_heavy`
(`8 < 9`, the image of `5 → 7 → 10 → 5`), and `long_mirror_cycle_heavy`
(`2 ^ 11 = 2048 < 2187 = 3 ^ 7`, the four-step mirror cycle `135 → 67 → 33 → 81`,
which is the `3n−1` cycle through `17`).  The last depends on **no axioms at all**.

## What it is worth — the honest measurement

**This is the classical dichotomy, not new mathematics.**  "A `3n+1` cycle is
light, a `3n−1` cycle is heavy" is `a/L < log 2 / log 3` versus `>`, and
`CycleProduct` has carried it since Round IV in the dual form `∏(3 + 1/nᵢ) = 2 ^ L`
over the *odd* elements.  The identity here is the same relation taken over the
*even* elements.  What the round adds is provenance: the dichotomy is now visibly
one character in one law, so it cannot be confused with anything else.

**And the bound it gives is the weaker of the two.**  Comparing:

| product over | bound on `2 ^ j / 3 ^ a` | exponent at `a ≈ 0.63 j` |
|---|---|---|
| even elements (this round) | `(1 + 1/m) ^ (j−a)` | `0.37 j / m` |
| odd elements (`CycleProduct`) | `(1 + 1/(3m)) ^ a` | `0.21 j / m` |

So the new identity is a **better explanation and a worse bound**, by a factor of
about `1.75`.  It excludes nothing `CycleProduct` did not already exclude.

## Why the swap device stops here

`DeviceSwap.run_length_ledger` cannot be sharpened by asking which run-length
sequences are arithmetically realizable, because **all of them are**: every
sequence `(s₁, …, s_B)` over `{0,1,2}` is realized by some residue class, checked
exhaustively for `B ≤ 4`.  That is the swap-coordinate form of the parity-word
bijection already recorded in the compression result, and it means the ledger is
extremal as it stands.

## The wall, restated with the round's own numbers

A light cycle needs `2 ^ j / 3 ^ a` within `O(1/m)` of `1` from above.  Separating
`2 ^ j / 3 ^ a` from `1` quantitatively is a linear-forms-in-logarithms problem;
that is exactly the route `CycleLength2593` and `length_ge_6809` already take, and
it leaves an infinite admissible set of `a`.  Nothing in Rounds XVII–XIX touches
that, and no elementary identity in the swap coordinate can, because every such
identity is a conjugation of one already present.

**Status of the two halves after this round: unchanged.  Both open.**

## Axiom footprint

`mirror_cycle_heavy`: `propext`, `Quot.sound`.  `cycle_light`, `nu_telescope`,
`separation`: those plus `Classical.choice`.  `long_mirror_cycle_heavy`: none.
Zero `sorry`.  Zero added axioms.  `lake build Collatz` succeeds, 254 jobs.

# Round XX — stop building, measure the wall; then prove the measurement

Rounds XVII–XIX each added a device and each landed on the same wall.  This round
does the opposite thing: no new device, one measurement, one theorem.

## The question that had never been asked in numbers

`CycleProduct.neverDrops_product_bound` excludes an odd-count `a` when
`2 ^ L · m ^ a ≤ (3m + 1) ^ a` **fails**.  Round XIV recorded that the admissible
set is infinite.  It did not ask: **does extending the verified range help?**

## Measured (60-digit arithmetic)

With `L = ⌊a log₂ 3⌋ + 1`, write `δ(a) = L log 2 − a log 3 ∈ (0, log 2)`.
Admissibility is `δ(a) ≤ a log(1 + 1/3m)`, and `δ` equidistributes because
`log₂ 3` is irrational.  So the admissible density at scale `a` is
`min(1, a/(3m log 2))`, giving three predictions — a horizon at `3m log 2`, mean
density `1/2` below it, and an admissible count `≈ (3 log 2 / 2) m ≈ 1.0397 m`:

| verified `c` | predicted horizon `3c ln 2` | measured density below it |
|---|---|---|
| 1 086 464 | 2 259 238 | 0.5032 |
| 4 345 856 | 9 036 954 | 0.4997 |
| 17 383 424 | 36 147 814 | 0.4950 |

**Verification does not converge.**  Doubling `c` doubles the window and holds the
survivor density at one half, so it doubles the surviving odd-counts.  The
method's reach grows exactly as fast as the problem it creates.  This is the
sharp form of "the admissible set is infinite", and it is a *worse* fact than the
old phrasing suggested: more computing is not slow progress, it is no progress.

Side note, to be checked against Round XIV: the sharp bound used here leaves
**85** admissible `a` in `[4296, 20000]` (`4296, 4961, 5626, 5932, 6291, …`),
where Round XIV recorded 169 from a linearised form.  Different inequalities, not
a contradiction; the sharp one is the one proved below.

## Proved — `ProductCeiling` (LEAN_PROVED)

**`product_bound_vacuous`: `0 < m → 3m ≤ a → 2 ^ K ≤ 3 ^ a →
2 ^ (K+1) · m ^ a ≤ (3m+1) ^ a`.**

The hypothesis `2 ^ K ≤ 3 ^ a` is exactly the `L = K + 1` a cycle has, by
`cycle_length_determined`.  So **the product family excludes nothing at or above
`a = 3m`**, for every `m`, unconditionally.  The proof is Bernoulli in the one
form that inducts without subtraction (`pow_add_one_ge`:
`N ^ k (N + k) ≤ (N+1) ^ k N`) plus its corollary `two_mul_pow_le`
(`N ≤ a → 2 N ^ a ≤ (N+1) ^ a`): the factor the bound may spend is
`(1 + 1/3m) ^ a`, and past `a = 3m` that already exceeds `2`, which is all the
room `2 ^ L / 3 ^ a < 2` ever needs.

`product_bound_bites` (`m = 2, a = 1`: `8 > 7`, and `1 < 6 = 3m`) shows the
ceiling is a real boundary, not an artefact.  `horizon_not_attained` (`m = 2`,
`a = 4`) shows `3m` is an upper limit on where exclusion can stop, not a claim it
survives that far.  Both by `decide`; the first depends on **no axioms**.

## What Round XX settles

The three previous rounds concluded "the remaining content is
linear-forms-in-logarithms" by argument.  This one shows it by a theorem plus a
constant: the product family has a **hard horizon at `a ≈ 2.079 m`**, its survivor
density below the horizon is **exactly `1/2`**, and both scale **linearly** with
the verified range.  Closing the cycle half cannot come from this family, and
cannot come from more computation.  It needs a lower bound on
`|L log 2 − a log 3|` beating `a / 3m`.

**Status of the two halves: unchanged.  Both open.**

## Axiom footprint

`product_bound_vacuous`, `pow_add_one_ge`, `two_mul_pow_le`: `propext`,
`Quot.sound`.  `product_bound_bites`: none.  Zero `sorry`.  Zero added axioms.
`lake build Collatz` succeeds, 255 jobs.

# Round XXI — the horizon constant, proved instead of measured

Round XX proved vacuity at `a ≥ 3m` and *measured* the true horizon at
`3m·log 2 ≈ 2.079 m`.  A constant read off a computation is not a theorem.  This
round removes the computation.

## The idea

Vacuity needs `(1 + 1/N)^a ≥ 2` with `N = 3m`.  Bernoulli
(`ProductCeiling.pow_add_one_ge`) gives `(1 + 1/N)^k ≥ 1 + k/N`, reaching `2` at
`k = N` — the constant `1` of Round XX.  But Bernoulli can be applied at exponent
`k` and the result **compounded** `p` times:

`(1 + 1/N)^(k·p) ≥ (1 + k/N)^p`,

so any `k` with `(1 + k/N)^p ≥ 2` suffices, at cost `a = k·p`.  Optimising `k` at
fixed `p` gives the constant `c_p = p·(2^(1/p) − 1)`:

`c_1 = 1`, `c_2 = 0.8284`, `c_3 = 0.7798`, `c_4 = 0.7568`, … , `c_p → log 2`.

**The measured constant is the infimum of a family every member of which is a
theorem.**  `two_mul_pow_le_gen` is the family; `two_pow_two`, `two_pow_three`,
`two_pow_four` instantiate it, each needing one integer power comparison —
`289 ≥ 288`, `250047 ≥ 250000`, `200533921 ≥ 200000000` — and nothing else.

## The proved horizons

| `p` | condition on `k` | horizon `a ≥` | as a multiple of `m` |
|---|---|---|---|
| 1 | — | `N` | `3 m`  (Round XX) |
| 2 | `12k ≥ 5N` | `5N/6` | `2.5 m` |
| 3 | `50k ≥ 13N` | `39N/50` | `2.34 m` |
| 4 | `100k ≥ 19N` | `19N/25` | **`2.28 m`** |
| ↓ | | `N log 2` | `2.079 m` (the measurement) |

`product_bound_vacuous_sharp` is the `p = 4` form: the product family excludes
nothing at or above `a = 2.28 m`, proved.

Two structural facts make "horizon" mean something:

* `two_mul_pow_upward` — the vacuity condition is **upward closed in `a`**, so
  there is a genuine threshold and the `k·p` lattice of the family covers all `a`.
* `two_pow_ne_three_pow` — `2 ^ L ≠ 3 ^ a` for `L ≥ 1`, by parity.  This is the
  irrationality of `log₂ 3` in the only form the argument uses, with no analysis
  anywhere, and it is what makes Round XX's `δ(a)` never vanish (`delta_pos`).

## What is still measured, stated plainly

The **density `1/2`** below the horizon is not proved.  It follows from Weyl
equidistribution of `{a log₂ 3}`, which needs the irrationality proved here plus
an analytic ingredient this development does not carry.  Everything else from
Round XX — the horizon, its linear scaling in `m`, and the conclusion that
extending verification does not converge — is now a theorem.

**Status of the two halves: unchanged.  Both open.**

## Axiom footprint

`two_mul_pow_le_gen`, `two_mul_pow_upward`, `product_bound_vacuous_sharp`,
`two_pow_ne_three_pow`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added
axioms.  `lake build Collatz` succeeds, 256 jobs.

# Round XXII — the external input, named; and the proof that naming it is not enough

Five rounds concluded that what remains is an effective lower bound on
`|L log 2 − a log 3|`.  This round names that input, proves what it yields, and
proves where it stops.

## The input

Writing a cycle's gap as `2 ^ L = 3 ^ a + G`, an effective linear-forms bound is a
function `f` with

`EffectiveGap f  :=  ∀ L a G, 1 ≤ a → 0 < G → 2 ^ L = 3 ^ a + G → 3 ^ a ≤ f a · G`.

Baker–Wüstholz / Matveev supply such an `f`, polynomial in `a`.  Nothing here
assumes which one.

## What it buys — `conditional_cycle_bound` (LEAN_PROVED)

For a cycle of minimum `m` and odd-count `a = A + 1` obeying the product bound,
in the range `2a ≤ 3m`:

**`EffectiveGap f → 3m ≤ 2 · a · f a`.**

With `f a = a ^ C` (`baker_polynomial`): `3m ≤ 2 a ^ (C+1)`, i.e.
`a ≥ (3m/2) ^ (1/(C+1))`.  **A lower bound on the odd-count, not an exclusion** —
the shape of the Steiner / Simons–de Weger results already at `length_ge_6809`.

Two new elementary estimates carry the proof:

* `pow_succ_diff` — `(x+1) ^ (a+1) ≤ x ^ (a+1) + (a+1)(x+1) ^ a`, binomial
  telescoping;
* `pow_ratio_le` — `(x+1) ^ A · (x − A) ≤ x ^ (A+1)`, written subtraction-free as
  `(A+y+1) ^ A · y ≤ (A+y) ^ (A+1)`.  This is the **reciprocal Bernoulli**, the
  upper bound on `(1 + 1/x) ^ A` that Bernoulli itself does not give, and the
  exact converse of the `HorizonSharp` family.  Its corollary `pow_le_two_mul`
  (`2A ≤ x → (x+1) ^ A ≤ 2 x ^ A`) is what removes the `+1`.

## What it does not buy — and this is the result

The side condition `2a ≤ 3m` is not a convenience.  Round XXI proved the product
bound **vacuous** for `a ≥ 0.76·(3m) = 2.28 m`, so beyond the horizon it is not a
constraint and `conditional_cycle_bound` has nothing to consume — **for any `f`
whatsoever**.  `regions_disjoint` proves the two side conditions are outright
incompatible: no `a` satisfies both `k·4 ≤ a` (past the horizon) and `2a ≤ 3m`.

| region | status |
|---|---|
| `a ≤ 1.5 m` | `EffectiveGap f` gives `3m ≤ 2 a f a` |
| `1.5 m < a < 2.28 m` | covered by neither |
| `a ≥ 2.28 m` | product bound provably vacuous; **no `f` helps** |

**An effective linear-forms bound, fed into the product family, provably cannot
reach cycles of large odd-count.**  That is not a limitation of Baker's theorem;
it is a limitation of the family it would be fed into.  Closing the cycle half
requires a second constraint surviving past `a ≈ 2.28 m`, and no such constraint
exists anywhere in this repository.

This is the specification a solution must meet, and it is now a theorem rather
than a summary.  **Status of the two halves: unchanged.  Both open.**

## Axiom footprint

`conditional_cycle_bound`, `baker_polynomial`, `regions_disjoint`,
`pow_ratio_le`, `pow_succ_diff`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero
added axioms.  `lake build Collatz` succeeds, 257 jobs.

# Round XXIII — the product bound forgets that cycle elements are distinct

The first strictly *stronger* result in seven rounds, rather than another map of a
wall.  It comes from an input the repository has never used.

## The gap

`CycleProduct.neverDrops_product_bound` is `2 ^ L · m ^ a ≤ (3m+1) ^ a`.  The
`m ^ a` treats all `a` odd elements of a cycle as if each equalled the minimum.
They do not.  A cycle's elements are **distinct**, and they are **odd**, so sorted
increasingly the `j`-th satisfies `n_j ≥ m + 2j`.  A grep confirms the words
`distinct`, `Pairwise`, `Nodup` appear nowhere in the cycle-bound files.

## The staircase bound (LEAN_PROVED)

From the classical cycle identity `2 ^ L · ∏ nᵢ = ∏ (3nᵢ + 1)` together with
`n_j ≥ m + 2j`:

**`stair_product_bound`: `2 ^ L · ∏_{j<a}(m + 2j) ≤ ∏_{j<a}(3(m+2j) + 1)`.**

The engine is one termwise inequality, `cross_step`: `y ≤ x → (3x+1)y ≤ x(3y+1)`,
which is the monotonicity of `3 + 1/n`, multiplied along the staircase
(`cross_prod`).  `stair_le_seq` supplies the domination: strictly increasing odd
numbers from an odd `m` satisfy `n j ≥ m + 2j`, because consecutive odds differ by
at least two.  The old bound is the degenerate case where every step is taken at
`m`.

## How much it buys — the horizon moves by a factor of 15

The old bound caps `Λ = L log 2 − a log 3` by `a·log(1 + 1/3m) ≈ a/(3m)`, which is
**linear** in `a` and passes the ceiling `log 2` at `a ≈ 2.079 m`.  That is the
Round XXI horizon.

The staircase caps `Λ` by `Σ_{j<a} log(1 + 1/(3(m+2j))) ≈ (1/6)·log(1 + 2a/m)`,
which is **logarithmic**.  It passes `log 2` only at `1 + 2a/m = 2 ^ 6 = 64`, i.e.

`a ≈ 31.5 m`.

**Horizon `2.079 m → 31.5 m`, a factor of `15.2`.**  Distinctness turns a sum of
`a` equal terms into a harmonic sum, and a linear cap into a logarithmic one.

## The gain is a theorem, not an estimate

`sharpening_is_strict`, by `decide`, at `m = 3`, `a = 9`, `L = 15` (legitimate:
`2 ^ 14 ≤ 3 ^ 9 < 2 ^ 15`, `exponent_nine`):

* old bound **holds**: `2 ^ 15 · 3 ^ 9 = 644 972 544 ≤ 10 ^ 9` — it excludes
  nothing, and `ProductCeiling.product_bound_vacuous` proves it cannot, since
  `a = 9 = 3m` is exactly at the old horizon;
* staircase bound **fails**: `stairPlus 3 9 = 18 596 395 417 600 <
  21 454 162 329 600 = 2 ^ 15 · stair 3 9` — so it excludes.

`sharpening_is_strict` and `witness_values` depend on **no axioms at all**.

## Honest scope

* This is a strictly stronger cycle bound.  It is **not** a proof of anything
  about Collatz, and both halves remain open.  It moves a horizon; it does not
  remove one.  Past `a ≈ 31.5 m` the staircase is vacuous exactly as the old bound
  was past `2.079 m`, and `ProductCeiling`'s argument applies verbatim there.
* `stair_product_bound` is stated about any sequence satisfying the cycle identity
  and the staircase domination.  **The bridge from the repository's own cycle
  representation to a sorted enumeration of its odd elements is not built.**
  Until it is, this bound is not plugged into `MinimalCycle` and the admissible-`a`
  count of Round XX is unchanged in the repository's own terms.  That bridge is the
  next piece of work and it is ordinary, not deep.

## Axiom footprint

`stair_product_bound`, `cross_prod`, `cross_step`, `stair_le_seq`: `propext`,
`Quot.sound`.  `sharpening_is_strict`, `witness_values`, `exponent_nine`: none.
Zero `sorry`.  Zero added axioms.  `lake build Collatz` succeeds, 258 jobs.

# Round XXIV — the spacing principle, and the second unused fact

Round XXIII replaced the constant `m` by the staircase `m + 2j` because cycle
elements are distinct.  This round isolates the mechanism and feeds it a second
fact the repository already proves but has never used.

## The principle

`seq_product_bound`: for **any** lower staircase `s` with `n_j ≥ s_j`,

`2 ^ L · ∏_{j<a} s_j ≤ ∏_{j<a} (3 s_j + 1)`.

Taking logarithms caps `Λ = L log 2 − a log 3` by `Σ log(1 + 1/(3 s_j))`.  If the
elements are forced a distance `s` apart, that cap is `≈ (1/(3s))·log(1 + sa/m)`,
which reaches the ceiling `log 2` only at

`a ≈ m · (2 ^ (3s) − 1) / s`.

**The horizon is exponential in the spacing.**

| spacing | source | horizon |
|---|---|---|
| `s = 0` | constant `m` | `2.079 m` (Rounds XX–XXI) |
| `s = 2` | distinct and odd | `31.5 m` (Round XXIII) |
| `s = 3` | **and coprime to 3** | `170 m` (this round) |

## The second unused fact

`CycleModThree.mod_three_ne_zero_of_accCycle` proves every element of an
accelerated cycle is coprime to `3`.  The product bound has never consumed it.

`gap_six`: three increasing odd numbers with both gaps `2` are `n, n+2, n+4`,
whose residues mod `3` are `n, n+2, n+1` — all three residues, so one is divisible
by `3`.  **Two consecutive gaps of two are impossible**, so every two steps advance
by at least `6`, and `stair3_le_seq` gives `n_j ≥ (m−1) + 3j`.
`stair3_product_bound` is the resulting bound.  Against the `2j` staircase it is
termwise larger from `j = 1` on (`three_beats_two`).

There is no arithmetic in `gap_six` beyond the observation that three consecutive
odd numbers cover every residue class mod `3`.

## Where the room runs out

`s = 3` is the **last** spacing available from local congruences: odd and coprime
to `3` is `2` residues in `6`, and finer moduli add nothing — mod `9` still leaves
`6` of `9`, and the elements are unrestricted mod any prime `> 3`.  Beating `s = 3`
requires a **non-local** sparsity statement: that a cycle's elements cannot cluster
just above the minimum.  Structurally that is plausible — from an element near `m`
an odd step multiplies by about `3/2` and cannot return below `m` — but no such
statement exists in this repository, and it is the natural next target.

## Honest scope

* Still a horizon, at `170 m` instead of `31.5 m`.  **Collatz is not proved, and
  neither half is closed.**
* As in Round XXIII, the bridge from the repository's cycle representation to a
  sorted enumeration of its odd elements is **not built**, so neither staircase is
  plugged into `MinimalCycle` and the admissible-`a` count of Round XX is unchanged
  in the repository's own terms.

## Axiom footprint

`seq_product_bound`, `cross_prod_gen`, `gap_six`, `stair3_le_seq`,
`stair3_product_bound`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added
axioms.  `lake build Collatz` succeeds, 259 jobs.

# Round XXV — the literature, read at last; and most of Rounds XI–XXIV is 1997

The instruction was to read the research.  Doing so settles several open questions
in this file, and settles them against us.

## Halbeisen–Hungerbühler 1997

*Optimal bounds for the length of rational Collatz cycles*, Elem. Math. 52.
Their `φ : S → ℕ` is

`φ(⟨⟩) = 0`, `φ(s0) = φ(s)`, `φ(s1) = 3φ(s) + 2^{l(s)}`.

**That is `AffineExact.affineC`, character for character.**  Also present in that
paper, or in Lagarias 1985 which it cites:

| their result | this repository |
|---|---|
| (3) `φ(s) = Σ_j s_j 3^{s_{j+1}+⋯+s_l} 2^{j−1}` | positional formula, `AccumulatorAutomaton.C_eq_Crel` |
| (4) `φ(s s̄) = 3^{n(s̄)}φ(s) + 2^{l(s)}φ(s̄)` | cocycle law, `AccumulatorArith.affineC_add` |
| Lemma 2 (Lagarias) `x₀ = φ(s)/(2^l − 3^n)` | `CycleAccumulator.cycle_eq_div` |
| **Lemma 4** (dominating partial sums ⟹ larger `φ`) | **`AffineExchange.Crel_mono`** — and their proof is the same adjacent transposition as `C_exchange` |
| **Lemma 5 + Cor. 1**: minimiser is the Beatty word `s̃ᵢ = ⌈in/l⌉ − ⌈(i−1)n/l⌉`, `M_{l,n}` explicit | Round XIII's extremal work, **not** in this optimal form |

**So the affine-accumulator programme of Rounds XVII–XIX, and much of XI–XIII, is
Lagarias 1985 and Halbeisen–Hungerbühler 1997.**  Recorded so it is not
rediscovered a third time.

Their cycle-length result: **≥ 102 225 496**, conditional on verification to
`2.12 × 10^14`.  Against `length_ge_6809` here — four orders of magnitude ahead.

## Verdict on Rounds XXIII–XXIV: the staircase is subsumed

`M_{l,n}` is the **exact** minimum of `φ` over shape `(l, n)`, so every valid
constraint linking a cycle's minimum to `(l, n)` is implied by it.  The staircase
bounds are such constraints, derived from distinctness and coprimality — both true
of the rational cycles their theorem covers.  **They are implied by, and no
stronger than, Halbeisen–Hungerbühler.**  The horizons `31.5 m` and `170 m` are
improvements only over this repository's own weaker starting point, not over the
literature.  That is the answer to "is the staircase refinement known": yes, in a
stronger form, since 1997.

## collatz-lab.org — the same wall, found independently

A Lean 4 (Mathlib) development proving `no_nontrivial_cycle_phase59` **conditionally**
on three unproved inputs: `BakerSeparation` (a strengthened working conjecture, not
a published theorem), `BarinaVerification` (`n < 2^71`), and a project-derived
`DerivedLargeKBound`.  Its **δ8 lemma** states that *no uniform algebraic bound
`F(k) < 2^71` follows unconditionally from product-bound methods alone*.

**That is `ProductCeiling.product_bound_vacuous` / `HorizonSharp`, found
independently.**  Their central obstruction is `Λ = S log 2 − k log 3`, the same
one Rounds XVII–XXII converged on.  Two independent developments reaching the same
wall by different routes is the strongest evidence yet that the wall is real.

## What is formalised this round — `HalbeisenHungerbuhler`

The Beatty word without division, as a running remainder (`beattyRem`,
`beattyBit`): add `n`, subtract `l` and emit `1` on overflow.  `beattyRem_lt`,
`beatty_invariant` (`remainder + l·weight = i·n`) and `beatty_count_eq`
(weight is exactly `n`) establish it is an element of `S_{l,n}`.  `hhMin` is
`M_{l,n}` by their Corollary 1.  `HHExtremal` names Lemma 5 as an explicit
hypothesis — **not proved here** — and `hh_min_bound`, `hh_min_large` draw the
consequences that are certainly correct.

## Gap 2 closed: criterion (5) recovered, and the previous reading was inverted

Section 4.4 of the paper, read this round.  Their inequality (11) is

`min C ≤ M_{l,n} / (2^l − 3^n)`,

an **upper** bound on the cycle minimum.  The earlier reading in this file had it
as a lower bound and was wrong.  The reason for the true direction: `M_{l,n} = φ(s̃)`
is the *largest* value the rotation-minimum of `φ` attains over `S_{l,n}` — Lemma 5
proves `φ(s̃) ≥ min_{t' ∈ σ(t)} φ(t')` for **every** `t` — and a cycle's minimum
element is `min_σ φ(σ)` over the gap.

**Theorem 4 (their optimal criterion), now formalised as `hh_criterion`:** if
`M_{L,n}` over the gap falls below the verified bound `m`, every cycle of length `L`
has minimum strictly below `m`, hence reaches `1` (`hh_no_cycle_below`).  Run over
all `L < 102 225 496` with `m = 2.12 × 10^14`, that is their result.

Their route also fixes what to compute: Crandall's criterion (Lemma 8), Eliahou's
(Theorem 2, giving `k(2^40) = 17 087 915`), their improvement (Theorem 3, the same
bound with `m` reduced by 10%), and then Theorem 4 for the final `10^8`.

## The wall, published in 1997

Their final remarks, in substance:

> All estimates on the length of Collatz cycles given so far are valid for
> **rational** Collatz cycles… but since the minimum of rational cycles grows at
> least linearly in terms of their length, **such an approach cannot be successful
> to prove (A)**.  The only chance to achieve further progress would hence involve
> number theoretical arguments.

That is `ProductCeiling.product_bound_vacuous` and `HorizonSharp`, stated by the
authors thirty years ago; the linear growth is their Remark 1,
`1/20 ≤ M_{l,n(l)}/(n·3^n) ≤ 7/10`.  The escape they name — "number theoretical
arguments" — is the Baker route of Round XXII.  Their Lemma 9,
`gcd(φ(t) : t ∈ σ(s)) = gcd(φ(s), 2^l − 3^n)`, is exactly the `δ` of
`DeltaSpectrum` and `RepetitionDescent`.

**Every wall this repository mapped in Rounds XVII–XXII appears in this one 1997
paper.**  That is worth knowing and is now recorded.

## The one gap that remains

### Remaining: Lemma 5 only

**Lemma 5 is the only thing still unproved** (`HHExtremal`).  Its proof needs the
rotation argument `σ_{k₀}` together with their Lemma 4, and Lemma 4 *is* available
here as `AffineExchange.Crel_mono`.  Everything else in their chain — the Beatty
word, its weight, `M_{l,n}`, Theorem 4, and the exclusion — is now formalised and
axiom-clean.

## The honest reframing

Closing (1) and (2) would replace `length_ge_6809` with something near `10^8` —
a four-order-of-magnitude gain, achievable, and known to be reachable because
someone has already done it on paper.  That is worth more than any device invented
in Rounds XVII–XXIV.  **Both halves of the conjecture remain open, and nothing in
this round changes that.**

## Axiom footprint

`beattyRem_lt`, `beatty_invariant`, `beatty_count_eq`, `hh_min_bound`,
`hh_min_large`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added axioms.
`lake build Collatz` succeeds, 260 jobs.

# Round XXVI — Lemma 5 reduced to the cycle lemma, and part 2 turns out to be free

Halbeisen–Hungerbühler's Lemma 5 has three parts:

1. every word of shape `(l, n)` has a **rotation whose partial sums dominate the
   line `kn/l`** — the Dvoretzky–Motzkin cycle lemma;
2. **`s̃` is minimal among dominating words**;
3. **Lemma 4**: larger partial sums ⟹ smaller `φ`.

Part 3 has been in this repository since Round XVIII as
`AffineExchange.Crel_mono`.  This round supplies part 2 — and part 2 turns out to
be free.

## The observation

In *time* coordinates the domination condition has no ceilings in it.  For odd-step
times `t₀ < ⋯ < t_{a−1}`, the partial-sum condition `Σ_{i≤k} wᵢ ≥ ⌈kn/l⌉` for all `k`
is equivalent to

`t_j ≤ ⌊j·l/n⌋`   for all `j`,

because `Σ_{i≤k} wᵢ ≥ ⌈kn/l⌉ ⟺ ∀ j, t_j < min{k : kn > jl} ⟺ ∀ j, t_j ≤ ⌊jl/n⌋`.
`dom_iff_mul_le` records the division-free form, `t_j · n ≤ j · l`.

So part 2 is **pointwise domination of time lists** — precisely the hypothesis
`AffineExchange.Dom` that `Crel_mono` already consumes.  `dominating_Crel_le` is
therefore a one-line consequence:

**`(∀ j < a, t j ≤ ⌊jl/n⌋) → Crel (times t) ≤ Crel (tildeList l n a)`.**

`tildeTime l n j = j * l / n` is the extremal time list; `hhMinTime` is `M_{l,n}`
in these coordinates.  Supporting lemmas `Dom_append_singleton` and
`Dom_of_pointwise` transfer domination through `List.range` maps.

## The state of the chain

| link | status |
|---|---|
| Beatty word, division-free (`beattyRem`, `beattyBit`) | proved |
| its weight is exactly `n` (`beatty_count_eq`) | proved |
| `M_{l,n}` (Corollary 1) | defined |
| Lemma 4 (`Crel_mono`) | proved (Round XVIII) |
| **Lemma 5 part 2** (`dominating_Crel_le`) | **proved this round** |
| Theorem 4 criterion (`hh_criterion`) | proved from `HHExtremal` |
| exclusion below verified bound (`hh_no_cycle_below`) | proved |
| **Lemma 5 part 1** — the cycle lemma | **the only gap** |

## The one gap

> Every word of shape `(l, n)` has a rotation whose times satisfy `t_j ≤ ⌊jl/n⌋`.

Its standard proof rotates at the index maximising `kn/l − Σ_{i≤k} wᵢ`, which is a
fold-maximum of exactly the kind `Discrepancy.discMax` already performs here.
Discharging it discharges `HHExtremal`, and with it the whole criterion chain.

**Both halves of the conjecture remain open.**  What this round changes is that the
distance to a published `10^8` cycle bound is now one named combinatorial lemma
with a known proof, rather than an open problem.

## Axiom footprint

`dominating_Crel_le`, `Dom_of_pointwise`, `Dom_append_singleton`: `propext`,
`Quot.sound`.  `dom_iff_mul_le`: `propext`.  Zero `sorry`.  Zero added axioms.
`lake build Collatz` succeeds, 261 jobs.

# Round XXVII — the cycle lemma, proved from first principles; the last link closes

Round XXVI reduced Halbeisen–Hungerbühler Lemma 5 to its part 1, the
Dvoretzky–Motzkin cycle lemma.  This round proves it, from scratch, and the proof
needs no list surgery at all.

## The derivation

For a `0-1` word `w` of length `l` with `n` ones set `S(k) = Σ_{i<k} w(i)` and

`d(k) = l·S(k) − k·n`.

Then `d(0) = d(l) = 0`, and with `w` extended periodically **`d` is periodic with
period `l`** (`disc_period`): the `l·n` gained over a full period is exactly the
`l·n` subtracted.  Rotating by `r` replaces `S(k)` by `S(r+k) − S(r)`, hence `d(k)`
by `d(r+k) − d(r)`.  So **the rotation at the minimiser of `d` has every rotated
discrepancy non-negative**, and by periodicity a minimum over `[0, l)` is already
global (`disc_min_global`).

No rotation of lists, no permutation reasoning: index shifting on a periodic
function and a fold (`argMin`) that finds the minimiser.

**`cycle_lemma`**: `∃ r < l, ∀ k, k·n + l·S(r) ≤ l·S(r+k)` — stated without
subtraction.

## And in time coordinates it is immediate

Round XXVI showed domination is `t_j·n ≤ j·l` in time coordinates.  If `t` is a
position of the rotated word with exactly `j` ones before it, `cycle_lemma` at
`k = t` gives `t·n + l·S(r) ≤ l·S(r+t) = l·S(r) + l·j`, hence `t·n ≤ j·l`
(`rotation_time_dominates`).  `cycle_lemma_time` packages this against
`ExtremalTime.dom_iff_mul_le`, producing exactly the hypothesis
`ExtremalTime.dominating_Crel_le` consumes.

## Tested before formalising

Exhaustively, over **every** `0-1` word of length `l ≤ 14` with any number of ones
— 32 752 words — in both the partial-sum form and the time form: **zero failures**.
Periodicity of `d` verified over four periods for `l ≤ 11`: zero failures.

## The chain, complete except for plumbing

| link | status |
|---|---|
| Beatty word, division-free | proved (XXV) |
| its weight is exactly `n` | proved (XXV) |
| `M_{l,n}` | defined (XXV) |
| Lemma 4 (`Crel_mono`) | proved (XVIII) |
| Lemma 5 part 2 (`dominating_Crel_le`) | proved (XXVI) |
| **Lemma 5 part 1 (`cycle_lemma`)** | **proved (XXVII)** |
| Theorem 4 (`hh_criterion`) | proved from `HHExtremal` |
| exclusion (`hh_no_cycle_below`) | proved |

**Every mathematical link of the Halbeisen–Hungerbühler chain is now proved in
this repository.**  What is left is plumbing, not mathematics: `HHExtremal` is
stated about the repository's `AccIsCycleOf` representation, while `cycle_lemma`
and `dominating_Crel_le` are stated about words and time lists.  Connecting them
needs the parity word of a cycle extracted as a periodic `w : Nat → Nat` with
`partialSum w L = oddCount x L`, and `Crel` of its times identified with
`affineC`.  Both halves of that bridge use machinery already present
(`Accelerated.parityVector`, `AccumulatorAutomaton.C_eq_Crel`).

**Both halves of the conjecture remain open.**  What is now in reach, and was not
before this round, is the published `10^8` cycle-length bound in place of
`length_ge_6809`.

## Axiom footprint

`cycle_lemma`, `cycle_lemma_time`, `disc_period`, `disc_min_global`, `argMin_min`,
`rotation_time_dominates`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added
axioms.  `lake build Collatz` succeeds, 262 jobs.

# Round XXVIII — the orbit's odd elements as a list, and the identity both halves needed

Two things were blocked on the same missing object: plumbing the
Halbeisen–Hungerbühler chain into `AccIsCycleOf`, and extending the staircase of
Rounds XXIII–XXIV from cycles to never-droppers.  Both need the odd elements of an
orbit prefix as an actual list with the telescoping identity.  Built.

## The identity

`oddElems x k` collects the odd values among `x, T(x), …, T^{k−1}(x)`.  Telescoping
`n ↦ (3n+1)/2` and `n ↦ n/2` along the prefix gives

**`orbit_product`: `2^k · T^k(x) · ∏ nᵢ = x · ∏ (3nᵢ + 1)`.**

Two specialisations:

* **`cycle_prod_eq`** (`T^L(x) = x`): `2^L · ∏ nᵢ = ∏ (3nᵢ + 1)` — the classical
  `2^L = ∏(3 + 1/nᵢ)`, now available in this repository with the elements present
  rather than bounded away.
* **`neverDrops_prod_le`** (`T^k(x) ≥ x`): `2^k · ∏ nᵢ ≤ ∏ (3nᵢ + 1)`.

Plus `oddElems_length` (`= oddCount`), `oddElems_odd`, and `oddElems_ge` (every
element at least the start, under never-dropping).

## Why the never-dropper form matters

`CycleProduct.neverDrops_product_bound` bounds every element below by the minimum,
giving `2^k · m^a ≤ (3m+1)^a` and a density deficit of order `1/m` — a **constant**,
which is exactly why `ProductCeiling` finds a horizon at `2.079 m`.

With the elements themselves in hand, and their **distinctness** (a non-periodic
orbit repeats no value), the staircase of Round XXIII applies here too, and the cap
on `Λ = k log 2 − a log 3` becomes `Σ_{j<a} log(1 + 1/(3(m+2j))) ≈ (1/6)·log(1+2a/m)`.
The deficit then has order `log k / k` and **tends to zero** instead of sitting at
a constant.

That is a strengthening of the **divergence-half** toolkit, which the staircase
rounds did not touch.  It does not close the divergence half: every bound here is
an *upper* bound on `Λ`, and a divergent orbit is free to send `Λ → −∞`.

## What is still missing, precisely

`neverDrops_prod_le` and `cycle_prod_eq` are the hypotheses
`StairThree.seq_product_bound` consumes.  Two facts remain:

1. **distinctness** — a non-periodic orbit's values are pairwise distinct, so
   `oddElems` is duplicate-free;
2. **ordering** — the staircase compares against *sorted* elements, so the list
   must be sorted or the comparison recast as counting.

Neither is deep.  Both are the same obstruction that has blocked the cycle-half
plumbing since Round XXIII, and they are now the single remaining item for both
halves' bookkeeping.

**Both halves of the conjecture remain open.**

## Axiom footprint

`orbit_product`, `neverDrops_prod_le`, `cycle_prod_eq`, `oddElems_length`,
`oddElems_odd`, `oddElems_ge`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added
axioms.  `lake build Collatz` succeeds, 263 jobs.

# Round XXIX — the sorted staircase and distinctness; one mechanical step left

Round XXVIII named one item blocking both halves' bookkeeping: the elements of
`oddElems` must be known **distinct**, and the staircase comparison needs them
**ordered**.  Both are done here, and the ordered comparison turned out to be a
three-line induction once the staircase is peeled from the right end.

## Peel the staircase from the small end

`StairBound.stair` peels the *largest* step.  The induction needs the *smallest*:

`stair m (a+1) = m · stair (m+2) a`,
`stairPlus m (a+1) = (3m+1) · stairPlus (m+2) a`

(`stair_peel`, `stairPlus_peel`).  In that form the comparison is immediate.  For a
strictly increasing list `y :: t` of odd numbers all at least an odd `m`: the head
satisfies `m ≤ y`; every later element is `> y` and odd, hence `≥ y + 2 ≥ m + 2`, so
the induction hypothesis applies at base `m + 2`; and the two heads are compared by
`StairBound.cross_step`, the statement that `3 + 1/n` decreases.

**`sorted_stair_bound`:**

`∏ (3yᵢ + 1) · ∏_{j<a} (m + 2j) ≤ ∏ yᵢ · ∏_{j<a} (3(m+2j) + 1)`

for any strictly increasing list of odd `yᵢ ≥ m`, `m` odd.  Composed with
`OrbitProduct.neverDrops_prod_le` or `cycle_prod_eq`, this is the staircase bound
against the orbit's **actual** elements — for cycles *and* never-droppers.

## Distinctness

`oddElems_mem`: every listed value is `T^i(x)` for some `i < k`.
`oddElems_nodup`: injectivity of the orbit on `[0, k)` gives a duplicate-free list.
Injectivity holds outright for a divergent orbit, and for a cycle of minimal
period on one period.

## The single remaining step, and it is mechanical

Turning `oddElems x k` — now known duplicate-free — into a **strictly increasing**
list with the same `prod` and `shiftProd`.  Insertion sort suffices; the product
invariance is one induction each (`prod (insert y l) = y · prod l`, likewise for
`shiftProd`), and strict sortedness of the output follows from duplicate-freeness
of the input.  No `List.Perm` machinery is needed, because only the two products
have to be preserved, not the list up to permutation.

With it: `HHExtremal` is dischargeable, the whole Halbeisen–Hungerbühler criterion
plumbs into `AccIsCycleOf`, and the never-dropper density deficit drops from a
constant `O(1/m)` to a vanishing `O(log k / k)`.

**Both halves of the conjecture remain open.**

## Axiom footprint

`sorted_stair_bound`, `oddElems_nodup`, `oddElems_mem`, `stair_peel`,
`stairPlus_peel`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added axioms.
`lake build Collatz` succeeds, 264 jobs.

# Round XXX — the mechanical step taken; the staircase now runs on real orbits

The insertion sort is in, and with it the chain from Round XXVIII closes.

## The sort

Only the two products must survive sorting — `prod` and `shiftProd` — not the list
up to permutation, so **no `List.Perm` machinery appears**.  Each invariance is one
induction (`insertSorted_prod`, `insertSorted_shiftProd`), and strict sortedness of
the output follows from duplicate-freeness of the input (`insertSorted_sorted`,
`sortList_sorted`).  Length and membership transfer likewise.

## The payoff

**`neverDrops_staircase`**: for an odd never-dropper `x` whose orbit is injective on
`[0, k)`, with `a = oddCount x k`,

`2 ^ k · ∏_{j<a} (x + 2j)  ≤  ∏_{j<a} (3(x + 2j) + 1)`.

**`cycle_staircase`**: the same on one period of a minimal cycle.

These replace `CycleProduct.neverDrops_product_bound`'s `2^k · x^a ≤ (3x+1)^a`,
which bounds every element below by the minimum.  The staircase uses the fact that
the elements are **distinct** — the input the constant bound throws away.

The assembly: `OrbitProduct.neverDrops_prod_le` gives `2^k · ∏ nᵢ ≤ ∏(3nᵢ+1)` with
the orbit's actual elements; `SortedStair.oddElems_nodup` gives distinctness from
injectivity; `sortList` orders them preserving both products;
`SortedStair.sorted_stair_bound` compares them against the staircase; the common
factor `∏ nᵢ` cancels because it is positive.

## What it changes

The old bound caps `Λ = k log 2 − a log 3` by `a·log(1 + 1/3x) ≈ a/(3x)`, **linear**
in `a`.  That constant deficit of order `1/x` is exactly what produces the
`ProductCeiling` horizon at `2.079 x`.  The staircase caps it by
`Σ_{j<a} log(1 + 1/(3(x+2j))) ≈ (1/6)·log(1 + 2a/x)`, **logarithmic**, so the density
deficit has order `log k / k` and **tends to zero**.

For the cycle half this is subsumed by Halbeisen–Hungerbühler (Round XXV).  For the
**divergence** half it is not: those results are about cycles, and none of them
applies distinctness of a *never-dropping* orbit's elements.  This is the first
statement in this development that improves the divergence-half toolkit by an input
the literature surveyed in Round XXV does not use.

## Honest scope

It does not close either half.  Every bound here is an **upper** bound on `Λ`, and a
divergent orbit is free to send `Λ → −∞`; what improves is how tightly the density
is pinned from below, not the exclusion of divergence.  The injectivity hypothesis
is discharged for free by divergence and by minimal periodicity, but is carried
explicitly rather than assumed.

**Both halves of the conjecture remain open.**

## Axiom footprint

`neverDrops_staircase`, `cycle_staircase`, `sortList_sorted`,
`insertSorted_sorted`, `insertSorted_shiftProd`, `prod_pos`: `propext`,
`Quot.sound`.  `sortList_prod`: `propext`.  Zero `sorry`.  Zero added axioms.
`lake build Collatz` succeeds, 265 jobs.

# Round XXXI — Hercher's merging lemma, and Device 17 was right all along

Searched the literature for the strongest cycle result and found Hercher, *There
are no Collatz m-cycles with `m ≤ 91`*, J. Integer Seq. 26 (2023), Art. 23.3.5
(arXiv:2201.00406).  Extracted and read.  One of its lemmas repairs a device this
repository discarded.

## The repository's own failed device

`CounterexampleDescent.Psi n = (n − 1)/2` is Device 17.  It is recorded there as
failing — `not_psi_preserves_firstGrows`, and the file's own summary,
*"neither intertwines `T`"*.

**Hercher's Lemma 9 says intertwining is the wrong thing to ask for.**  Under one
hypothesis the two orbits **merge**, and merging is all a descent argument needs.

## The statement (`merge`)

For odd `n` with `n + 1 = 2^(j+1)·u`, `u` odd — so exactly `j+1` odd steps follow
`n` — and at least two even steps after them:

`T^(j+3)(n) = T^(j+2)((n − 1)/2)`.

`merge_transfer`: from the meeting point the two orbits agree forever, so every
tail-property transfers to the strictly smaller `(n−1)/2`.

## The derivation, in one line

Put `A = 3^j·u`, odd.  `DeviceSwap.run_climb` gives `T^(j+1)(n) = 3A − 1` and,
since `(n−1)/2 + 1 = 2^j·u`, also `T^j((n−1)/2) = A − 1`.

The hypothesis `4 ∣ 3A − 1` forces `A ≡ 3 (mod 4)` — `A` is odd and `3·3 ≡ 1
(mod 4)` — hence `A − 1 ≡ 2 (mod 4)` and `(A−1)/2` is **odd**.  That is the whole
content:

* larger: `3A − 1 → (3A−1)/2 → (3A−1)/4`, two even steps;
* smaller: `A − 1 → (A−1)/2` even, then an **odd** step to `(3(A−1)/2 + 1)/2 =
  (3A−1)/4`.

The smaller trajectory arrives at an odd number exactly when the larger one has a
second halving to spend, and they land together.

## The divergence-half consequence (Hercher, Remark 10)

`unbounded_descends`: if `n`'s orbit is unbounded, so is `(n−1)/2`'s.  Hence **a
smallest divergent start has `ℓ = 1`** — exactly one even step after its opening
odd run.  Supporting `orbitMax`/`le_orbitMax` supply the only bookkeeping needed,
that an unbounded orbit has witnesses arbitrarily late.

This is a structural constraint on a minimal counterexample obtained from the
literature rather than invented here, and it is a **divergence-half** result — the
half the Round XXV survey found least covered.

## Also learned this round

* **`ccchallenge.org`** is an organised effort formalising the Collatz literature,
  currently **1 of 367 papers** complete (Böhm–Sontacchi 1978), with Tao 2022,
  Eliahou 1993, Bernstein–Lagarias 1996, Hercher 2023 and two 2025 papers awaiting
  audit.  Worth tracking; the present development overlaps its Eliahou and Hercher
  entries.
* Hercher's Lemma 8 — a run of `k` odd steps forces `n ≡ −1 (mod 2^k)` — is
  `DeviceSwap.run_climb`, already here since Round XVIII.
* Barina's verified range is `704 · 2^60`, against the `1 086 464` this repository
  uses.

## Testing

`merge` was checked on every odd `n < 400 000` meeting its hypothesis — 100 002
cases, zero failures — before formalising.

**Both halves of the conjecture remain open.**

## Axiom footprint

`merge`, `merge_transfer`, `unbounded_descends`, `le_orbitMax`: `propext`,
`Quot.sound`.  Zero `sorry`.  Zero added axioms.  `lake build Collatz` succeeds,
266 jobs.

# Round XXXII — Barina's range, named rather than assumed

A request to replace the verified-range constant `1 086 464` by Barina's
`704 · 2 ^ 60`.  Investigated first, because the answer determines whether the
change is legitimate.

## The finding that shaped the work

`Search.reachesOne_of_lt_1086464` is a **theorem** here, not a constant.  It is
established by kernel `decide` over `1061` sieve blocks — about `1.09` million
values, minutes of build time — with axiom footprint `propext, Quot.sound`; no
`sorry`, no `native_decide`.

Barina's `704 · 2 ^ 60 ≈ 8.12 · 10 ^ 20` is an external C/GPU computation.
Reproducing it by this development's method needs about `7.9 · 10 ^ 17` blocks
against `1061` — a factor of `7 · 10 ^ 14`, on the order of `10 ^ 10` years of
kernel time.  **A literal substitution would replace a proved theorem by an
unproved claim** and turn every downstream unconditional result conditional.

So the constant was **not** replaced.  Barina's range is named as an explicit
hypothesis, in the style already used for `BakerConditional.EffectiveGap`, and
everything derived from it carries that hypothesis in its statement.  The proved
`1 086 464` results are untouched and remain unconditional.

## `Search/BarinaRange` (LEAN_PROVED, plus one named hypothesis)

* `barinaBound = 704 * 2 ^ 60` — the single canonical definition; the numeral
  appears nowhere else.  `barina_value` pins it to `811 656 739 243 220 271 104`
  (no axioms), `barina_gt_verified` records the widening is strict.
* `BarinaVerified` — the external result as a hypothesis, **not proved**.
* `barina_subsumes`, `proved_range_is_weaker` — the hypothesis is a strict
  strengthening of the proved theorem, not a different claim.
* `counterexample_ge_barina`, `ge_verified_barina` — the payoff, each carrying the
  hypothesis.  The second copies the shape of `CycleLength2593.ge_verified_768000`,
  whose own comment notes the proof is insensitive to the constant.

## What a wider range would actually buy

`excludedLength_mono` (unconditional): the exclusion test is **monotone in the
verified range** — a length excluded at `c` is excluded at every `c' ≥ c`.  That is
the mechanism that moved this repository's cycle bound `520 → 1539 → 2593` as the
range grew, and `excludedLength_at_barina` transfers every existing exclusion to
Barina's range for free.

Measured outside Lean with exact integer arithmetic: the raw product bound first
fails at `L = 2593` at the proved range, and fails **nowhere below `L = 40 000`** at
Barina's.  So `BarinaVerified` would move the cycle-length bound by more than an
order of magnitude.  That is a measurement, not a theorem, and is labelled as such
in the file.

`excludedLength_mono_witness` (`L = 2`, `c = 1` versus `c = 1 086 464`) shows the
monotonicity is not vacuous at kernel-checkable size; the same phenomenon at
`L = 2593` is what the hypothesis would buy.

## Engineering checks

`Nat` is arbitrary-precision, so there is no overflow.  Kernel arithmetic at
Barina scale is cheap — `barina_value` and `barina_gt_verified` decide in under a
second.  The `O(L²)` scan of `excludedLength` does **not** survive at these lengths
(`decide` on `excludedLength 1086464 2593` exhausts recursion depth); the
repository's own `CycleLength2593.excludedFast` is the route for any future sweep,
as its header already says.

**Both halves of the conjecture remain open.**

## Axiom footprint

`barina_value`, `counterexample_ge_barina`: none.  `excludedLength_mono`,
`excludedLength_at_barina`, `ge_verified_barina`: `propext`, `Quot.sound`.
Zero `sorry`.  Zero added axioms.  `lake build Collatz` succeeds, 267 jobs.

# Round XXXIII — the verified range as a parameter, and the Barina sweep certified

Following the audit brief.  Three categories kept strictly apart throughout.

## 1. The audit

Every consumer of the verified range falls into one of three shapes.

**(a) Genuinely tied to the proved constant** — only
`Search.reachesOne_of_lt_1086464` and `counterexample_ge_1086464` themselves.
Both are theorems about a finished computation.

**(b) Generic in the bound — the large majority.**  Every theorem of shape
`hc : 1086464 ≤ m → P m` uses the constant only as a lower bound and never
inspects the numeral: `ValuationBeatty.orbit_time_le_fexp`, `even_steps_per_306`,
`orbit_run_box`, `orbit_gapC_le_Bcap`, `RealizableFrontier6809.no_light_window`,
`TropicalDefect`'s light-window bound, and the `BackwardRange` family.
`BottomUnreachable.bottom_unreachable` is already explicitly parametric.
*Caveat*: several consume a numeric certificate keyed to the constant
(`cert_1086464`), a finite table checked by `decide`; those are generic in
statement but their certificates would need recomputing at another bound.

*Later: not at a larger bound.*  `Strategy.CertMonotone.cert_mono_c` shows the
raw checker is monotone in the range, and `bank_mono` shows the unpacked form
these lemmas actually consume is too — the multiplier `2·2^(fexp i) − 3^i` is
positive by `lt_fexp`, so raising `c` only slackens the inequality.  So
`cert_1086464` and its siblings apply verbatim at any larger range with no
recomputation; `cert_barina_4296` is the instance.  A *smaller* bound is a
different matter and is not claimed.

**(c) Free transfer** — since `1086464 ≤ barinaBound`, every shape-(b) theorem
applies verbatim to a `BarinaVerified` counterexample.  `ge_barina_ge_proved` is
the one-line bridge; **no theorem needed restating, and none was
conditionalised.**

## 2. The parameter

`VerifiedBelow c` — every positive `n < c` reaches `1`.  `verified_1086464` is the
proved instance; `BarinaVerified` is the hypothetical one.  The orbit lemma that
had been written out once per constant — `ge_verified_768000`,
`ge_verified_1086464`, `ge_verified_barina` — is now the single `ge_verified_of`,
plus `counterexample_ge_of` and `verifiedBelow_mono`.  No abstraction beyond that;
the existing files were left alone.

## 3. The cycle machinery, certified

`excludedFast` (two bignum comparisons) is used throughout — `decide` on
`excludedLength 1086464 2593` exhausts recursion depth, `excludedFast` does not.

**`barina_sweep` is unconditional and depends on NO AXIOMS**: every length from
`1` to `40 000` passes the exclusion test at `barinaBound`.  It mentions no orbit;
it is a fact about `2`, `3` and `704 · 2 ^ 60`.  `BarinaVerified` enters only in
`cycle_length_ge_40001_of_barina`, through the cycle minimum.

**Conditional cycle bound: `L ≥ 40 001`**, against the unconditional `2593` of
`CycleLength2593` — a factor of **15.4**.

Kernel cost, measured: `5 000` in `7 s`, `20 000` in `15 s`, `40 000` in `36 s`,
`100 000` in `4 m 15 s`.  The committed sweep is `40 000`; `100 000` is reachable
but would double the whole build.  Exact integer arithmetic outside Lean confirms
`excludedFast barinaBound L` holds for every `L ≤ 60 000`, and the true crossover
is near `√c ≈ 7 · 10 ^ 10` — so the limit is compute, not mathematics.

## 4. Can Barina's result be certified compactly?  No, and here is why

A certificate must be checkable far below the cost of the computation it replaces.
Barina's range is a universally quantified statement over an **unstructured**
predicate — `n` reaches `1` — and the only known reason each residue descends is
that it was run.  Sieving cuts the constant (this development's level-`10` sieve
keeps `64/1024`, leaving `≈ 5 · 10 ^ 19` survivors) but not the asymptotics.  A
short certificate would amount to a proof of the range, and the range is a finite
fragment of the conjecture itself.

**The smallest missing object is therefore not a certificate but the computation.**
Two honest options: extend the kernel-checked sieve — cost `4×` per doubling,
payoff `√c` — or keep Barina as the named hypothesis.

## The strongest theorem in each category

| category | statement |
|---|---|
| **kernel-proved, unconditional** | `barina_sweep` — every `L ≤ 40 000` excluded at `704 · 2 ^ 60`; **no axioms**.  And `CycleLength2593.length_ge_2593` / `RealizableFrontier6809.length_ge_6809` for cycles. |
| **conditional on `BarinaVerified`** | `cycle_length_ge_40001_of_barina` — a nontrivial accelerated cycle has length `≥ 40 001`. |
| **externally measured** | `excludedFast barinaBound L` for all `L ≤ 60 000`; a `100 000` sweep passes the kernel in `4 m 15 s`; the true crossover is near `7 · 10 ^ 10`. |

**Both halves of the conjecture remain open.**

## Axiom footprint

`barina_sweep`, `sweep_is_strictly_stronger`: **none**.  `verified_1086464`,
`ge_verified_of`, `excludedLength_of_lt_40001`,
`cycle_length_ge_40001_of_barina`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero
added axioms.  `lake build Collatz` succeeds, 268 jobs.

# Round XXXIV — eight parallel investigations; two survivors, both negative, both verified

Eight independent tracks were dispatched in parallel.  Five died on an external
rate limit and one on a disk-full condition; four returned.  **Every claim below
was re-verified by independently written code before being recorded** — the
subagent that produced a result is never the one that confirmed it.

## What the wave returned

**Track 2 (2-adic / parity runs) — sharp negative, verified.**
The full-shift claim is *stronger* than this repository states: every run-word is
realised by **exactly one** residue class mod `2 ^ (S+B+1)` — existence *and*
uniqueness.  That matters, because `ValuationTransition` infers "no finite
automaton can obstruct" from `word_realizable`, which gives **existence only**;
existence alone permits wildly unequal class densities, which is exactly where a
sieve could still bite.  The licensing fact is uniqueness, and it is not proved
here.

Two consequences, both reproduced independently:
* **Bit-counting is dead by a factor of ten.**  `y = 55` — six bits — sustains a
  21-step non-dropping run whose word occupies **59 bits** of 2-adic depth.
* **No congruence obstruction mod `2 ^ k` can exist**, witnessed by the 2-adic
  integer `−9`: `−9 + 1 = −8 = 2 ³ · (−1)`, so its letter is `2` forever and it is
  a fixed point.  `2 ^ k − 9` never drops, with the run growing in `k` (40 steps at
  `k = 128`).

Sharpest sentence of the round: every periodic never-dropping word has a
**negative rational** realiser, so the missing obstruction must separate positive
integers from negative rationals *inside one residue class mod `2 ^ k`*.  No
congruence can do that.

**Track 6 (parity-word combinatorics) — negative, with a methodological
correction that matters.**  The naive heuristic `Σ C(l,n)/D` predicts ~47 cycles
below `l = 42`, making the observed zero look like a `10 ^ −19` miracle.  But a
cycle is *one* word — the rotation at the minimum — not `l` of them.  Correctly
normalised by dominating words: expected **3.46**, `P(0) = 0.031`.  **The absence
of cycles below `l = 42` is not evidence of hidden structure.**  Any future
counting argument on this track must use that null model.

`gcd(φ(w), D)` behaves exactly like a random integer's; the Sturmian heavy-prefix
condition is a `1/l` thinning excluding **zero** shapes; several striking apparent
congruence obstructions (e.g. `(14,6)`, `p = 101`, *no* word with `101 | φ`) are
mirages once rescored against necklaces.

One positive artifact, **re-verified here** (98 304 splittings, 0 failures; and
18 400 checks of the corollary, 0 failures): the exact rotation identity

`2 ^ |u| · φ(vu) = 3 ^ (ones u) · φ(uv) + (2 ^ l − 3 ^ n) · φ(u)`,

whence `e | φ` is a rotation-class invariant for every `e | 2 ^ l − 3 ^ n`.  A
clean exact form of Halbeisen–Hungerbühler Lemma 9 that this repository lacked.

**Track 7 (merging / splicing) — the round's theorem, now formalised.**  See below.

**Track 8 (novel) — a new obstruction, verified.**  See below.

## `HercherChain` (LEAN_PROVED) — the merge fires exactly once

`HercherMerge.merge` needs `(3 ^ (j+1) · u) % 4 = 1`.  The partner `(n−1)/2` has
`(n−1)/2 + 1 = 2 ^ j · u` — same odd cofactor, one fewer power of two
(`partner_shift`) — so *its* merge hypothesis is `(3 ^ j · u) % 4 = 1`.  Since
`3 ≡ −1 (mod 4)`, the two residues are opposite:

**`no_chain`: `(3 ^ (j+1) · u) % 4 = 1 → (3 ^ j · u) % 4 = 3`.**

The hypothesis at `n` is exactly the negation of the hypothesis at the partner.
In Hercher's `ℓ`-language: `ℓ(n) ≥ 2 ⟹ ℓ((n−1)/2) = 1`.  **`ℓ = 1` is not a
shrinking exceptional set — it is half of every level, and it is precisely where
the merge is unavailable.**

Verified independently before formalising: over every odd `n < 400 001`, `100 002`
have `ℓ ≥ 2`, `50 002` of those have an odd partner, and **zero** of those
partners again have `ℓ ≥ 2`.  Density of `ℓ ≥ 2` is `0.49998`.

And the harder negative, also reproduced independently.  Call `m < n` an *early
merge* of `n` if its orbit meets `n`'s orbit **before** `n`'s orbit drops below `n`
— the only kind a minimal-counterexample argument may use.  Then

`n = 27, 703, 871, 1695, 2215, 35655`

have **no early merge at all**, checked against every smaller `m`.  About 44.6 % of
odd `n` have none, and conditioning on longer excursions plateaus at 0.84–0.85
rather than approaching 1.  **No merge-based descent, at any depth, can be made
into a covering argument.**

## The `Z[√−2]` obstruction (verified, not yet formalised here)

Track 8's survivor, independently re-verified in full:

Take `π = √−2` (norm 2), `μ = 1 + √−2` (norm 3), and `T x = x/π` if `π ∣ x`, else
`(μx + 1)/π`.  Then `N(μ)/N(π) = 3/2`, so the critical ratio is `log 3 / log 2`
exactly, and — crucially — **`μ − π = 1`, so the shifted coordinate `u = x + 1` and
the sign of the `+1` are preserved**, unlike the `3n − 1` mirror.

Verified here from scratch: the shift identity `π(Tx + 1) = μ(x + 1)` holds on the
odd branch (29 646 points, 0 failures) exactly as `2(Tx+1) = 3(x+1)` does; and a
census of 111 074 starts of norm `≤ 50 000` finds **exactly three cycles** — the
fixed point `−1`, a 5-cycle through `1`, and a **13-cycle** with minimum
`7 − 4√−2` (norm 81), max norm 776, `a = 8` odd steps, `2 ^ 13 / 3 ^ 8 = 1.2486`.

The one ingredient that fails is the master bound, and its failure localises: at
`w = −5 − 6√−2`, on the cycle, `N(w) = 97 ≥ 81 = N(m)` but `N(w+1) = 88 < 96 =
N(m+1)`.  `Z[√−2]` is not formally real, so it admits no ring order and the step
`m ≤ w ⟹ m+1 ≤ w+1` has no substitute.

**The two filters are orthogonal.**  The `3n−1` mirror preserves order and breaks
the sign; `Z[√−2]` preserves the sign and breaks the order.  Together they say a
proof must use **both**, and the master bound is the only place in this development
where order enters.

## Axiom footprint

`no_chain`, `not_both`, `partner_shift`, `chain_length_one`: `propext`,
`Quot.sound`.  Zero `sorry`.  Zero added axioms.  `lake build Collatz` succeeds,
269 jobs.

**Both halves of the conjecture remain open.**

# Round XXXV — wave two: four fresh directions, one theorem, one circularity found

Four independent tracks on radically different mathematics.  All four returned.
As before, nothing is recorded that was not checked independently of the agent
that produced it.

## The theorem — `NoWindowObstruction` (LEAN_PROVED)

`Accelerated.parityVector_surjective_mod_pow_two` is already proved here: every
`0-1` word of length `k` occurs as a parity vector.  Made positive
(`parity_prefix_surjective`, via `parityVector_mod_pow_two` on `a + 2 ^ k`), it
yields

**`no_finite_window_obstruction`: if a property of `0-1` words holds on the
length-`k` parity word of every positive integer, it holds on *every* `0-1` word of
length `k`.**

So a test inspecting a bounded prefix of the parity word and satisfied by all
positive integers separates nothing at all.

**Corollary — no subshift of finite type.**  An SFT is a finite set `F` of
forbidden words; let `L` be the longest.  Any `f ∈ F` is, by
`no_forbidden_prefix`, the parity prefix of a genuine positive integer, so
forbidding it excludes that integer.  Hence `F = ∅`, the subshift is the full
shift, and it contains the never-dropping words too.  **No subshift of finite type
contains every positive integer's parity word and excludes the never-dropping
ones.**

This closes the *combinatorial* branch of symbolic dynamics outright, from a
theorem rather than from measurement.  It leaves weighted automata untouched — and
there the obstruction is different and was identified this round: `affineC` depends
on the positions of *all* earlier odd steps, so no finite-state device computes it,
and a bounded-window surrogate has error that is bounded but does **not** vanish.

## The circularity — my own proposed pigeonhole was wrong

I had suggested: a non-dropping orbit of length `j` visits `j` distinct integers
`≥ n`, so if it stays below `M` then `j ≤ M − n`, which should contradict the affine
law.  **This is circular twice over**, and the ergodic track found both holes:

1. "visits `j` **distinct** values" needs the orbit not to cycle above `n` —
   ruling out a cycle at height `≥ n` is a restricted case of the conjecture;
2. the bound needs an a priori ceiling `M`, and producing `M` for all `n` is the
   hard half of the conjecture, not an input to it.

The pigeonhole converts one open problem into an equally open one.  Recorded so it
is not proposed again — including by me.

## Ordered rings: the `Z[√−2]` question answered, and it does not help

Wave one found that `Z[√−2]` carries every structural theorem of this development
**and** a nontrivial 13-cycle, its only failing ingredient being the order.  The
obvious follow-up: do **ordered** (real quadratic) analogues have cycles?

Searched all class-number-one imaginary quadratic orders and `Z[√d]`,
`Z[(1+√d)/2]` for `d ≤ 21`, for pairs `π` (norm `±2`), `μ` (norm `±3`) with `μ − π`
a unit.  Two findings:

* **The structure is rare, not generic.**  Almost no ring admits such a triple;
  `Z[√−2]` is essentially the unique imaginary one.  Real cases exist only at
  `d = 3, 6, 7`.
* **In all three ordered cases: zero nontrivial cycles.**  But the mechanism is
  not "order forbids growth".  Tracing orbits shows the integer norm `|N(x)|`
  grows exponentially while the **real embedding stays bounded and oscillates** — a
  Pell-like compensation by the conjugate embedding.  The orbits are
  bounded-but-not-visibly-periodic: **exactly the open shape of the original
  conjecture.**

So order does suppress cycles in the tested range, but the ordered analogue is a
problem of the same difficulty, not an easier one.  CONJECTURE, not theorem, and no
proof mechanism was extracted.

## Lyapunov: nothing survived, and the failures were shallow

Every candidate family (odd part of `n+1`, `v₂(n+1)`, `v₂(3n+1)`, odd part of
`3n+1`, odd-run length, and residue-class-fitted product potentials) failed against
the *plain map* before any soundness filter was needed — 25–75 % of random `n`
increase.  The fitted potential dies at `n = 4 477 015` for every `(j, k)` tried.
Useful byproduct: the `Z[√−2]` 13-cycle norm sequence
`81,137,225,353,531,776,388,194,97,153,227,324,162,81` was reproduced
independently, a third confirmation.

## Axiom footprint

`parity_prefix_surjective`, `no_finite_window_obstruction`, `no_forbidden_prefix`,
`no_separating_window`: `propext`, `Classical.choice`, `Quot.sound`.  Zero `sorry`.
Zero added axioms.  `lake build Collatz` succeeds, 270 jobs.

**Both halves of the conjecture remain open.**

# Round XXXVI — wave three: two programmes closed by one witness

Four more tracks.  Two produced the numeric deliverables asked for, and those two
turn out to fail for **the same reason**, which is now formalised.

## The shared witness — `SurvivorWitness` (LEAN_PROVED)

Both negatives reduce to `n ≡ −1 (mod 2 ^ k)`, i.e. `n + 1 = 2 ^ k · u`.  By
`DeviceSwap.run_climb` such an `n` takes `k` consecutive odd steps, each
multiplying the shifted coordinate by exactly `3/2`.

* **`no_drop_within`** — for every `i ≤ k`, `n ≤ T^i(n)`.  The proof is one line
  after `run_climb`: the shifted value is `3 ^ i · w` against `2 ^ i · w`, and
  `3 ^ i ≥ 2 ^ i`.
* **`survivor_exists`** — `2 ^ k − 1` is such an `n`, at every level `k ≥ 1`.
* **`no_covering_by_powers_of_two`** — hence there is no `k` for which every
  residue class mod `2 ^ k` drops within `k` steps.
* **`block_ratio_witness`** — on the same family `T^k(n) + 1 = 3 ^ k`, so the block
  growth ratio is exactly `(3/2) ^ k`.

## What the two tracks measured, and why the witness explains both

**Covering / density.**  With `S_j = #{r < 2 ^ j : r does not drop within j steps}`,
the parity-vector bijection gives exactly

`S_j = Σ_{a : 3 ^ a ≥ 2 ^ j} C(j, a)`

(binomial law `#{r < 2^j : a odd steps} = C(j,a)` verified by brute force for
`j ≤ 13`, zero exceptions).  Measured: `S_10 = 176`, `S_20 = 137 980`,
`S_30 = 107 636 402`, `S_60 ≈ 2.99 · 10 ^ 16`, and `log₂(S_j)/j = 0.9122` at
`j = 60`, climbing to the binary entropy `H₂(log 2/log 3) = 0.94996`.

**The density goes to one and the survivor count goes to infinity.**  `d_j → 1` but
`S_j ~ 1.9318 ^ j`.  So no covering system can finish; the residual is of vanishing
density and unbounded size.  The survivor tree has no dead ends — every survivor has
a surviving child.

**Cross-check that matters:** `H₂(log 2/log 3) = 0.94996` is *exactly* the Hausdorff
dimension `≈ 0.95` of the never-dropping set in `ℤ₂` computed independently in wave
one, by a completely different method.  Two unrelated computations agreeing to three
decimals is the strongest internal validation this project has produced.

**Block Lyapunov.**  For each `k ≤ 20` the optimal achievable sup-ratio of
`V(T^k n)/V(n)` over bounded residue-class weightings `g` is exactly `3 ^ k / 2 ^ k`,
attained at `2 ^ k − 1`: `1.5, 2.25, 3.375, 5.063, …, 3325.257`.  **It does not
approach `1` from above — it diverges geometrically.**  No `V(n) = n · g(n mod 2 ^ k)`,
`n ^ α · g`, or `log n + h` can work, for any `k ≤ 20`, and the reason generalises:
the all-odd class is present at every level and on it the map does the worst thing
available.

## The two weaker tracks

**Graph-theoretic** — correct but near-trivial: the forward Collatz graph is
*functional* (out-degree exactly `1`), so the separator framing is vacuous — there
is only ever one forward path from `n`.  Pushed to the inverse tree it dies for the
same equidistribution reason already proved dead for parity windows.  One useful
measurement: bit-length level revisits grow **linearly** in orbit length
(≈ 0.58 per step), so unboundedly many crossings of every level is generic for
*convergent* orbits — killing "bounded level crossings" as a divergence signature.
The agent honestly flagged that it did not complete the `x ^ 0.84` work.

**Fresh invention** — three ideas, all dead.  The `u = n+1` ceiling/floor
reformulation is a true but empty conjugacy.  The "ceiling defect" co-state
`D_k = u_k − u_0·(3/2)^a/2^{k−a}` is **unbounded** (≈ 1369 after 40 steps), because
each ceiling correction is multiplied by `3/2` at every later odd step.

That last one has a closed answer the agent did not have: **`D_k · 2 ^ k` is exactly
`RunAlgebra.runA`**, the repository's shifted accumulator — verified here, 59 970
checks, zero failures.  So its proposed follow-up (is the *normalised* defect
`D_k/L_k` bounded?) is already settled by `AffineExact.affineC_le`, which gives
`runA ≤ 3 ^ a (2 ^ t − 1)` and hence `D_k/L_k ≤ (2 ^ t − 1)/(n+1)` — **not** bounded,
since `2 ^ t` grows.  Verified, zero failures.  The direction is closed.

## Axiom footprint

`no_drop_within`, `survivor_exists`, `block_ratio`, `block_ratio_witness`,
`no_covering_by_powers_of_two`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added
axioms.  `lake build Collatz` succeeds, 271 jobs.

**Both halves of the conjecture remain open.**

# Round XXXVII — revolutionary-mathematics wave: five deep theories, five verdicts

Five genuinely new starting points, none previously touched here.  All five
returned.  Nothing recorded that was not re-verified independently.

## The theorem — `MatrixReducible` (LEAN_PROVED)

A trajectory is a word in the semigroup generated by

`E = [[1,0],[0,2]]` (even), `O = [[3,1],[0,2]]` (odd).

`RunAlgebra` notes the correspondence in prose.  The question joint-spectral-radius
theory asks first was never asked: **is the pair irreducible?**

**It is not.**  `common_eigenvector`: `E` and `O` share the eigenvector `e₁ = (1,0)`
with eigenvalues `1` and `3` (axiom-free).  So the semigroup splits into two
one-dimensional pieces, and `diag_eq` gives the consequence:

**the diagonal of any product is `(3 ^ a, 2 ^ n)` — depending only on the letter
counts, never on their order.**

All ordering information sits in the single off-diagonal entry, which is
`affineC`.  The growth factor is `3 ^ a / 2 ^ n`, equal to `1` exactly at
`a/n = log 2/log 3` — so the critical density is an **algebraic** consequence of
reducibility, not a heuristic.

**Why this closes a real gap.**  Barabanov's extremal-norm theorem requires an
*irreducible* family.  A Barabanov norm was the one shape of Lyapunov certificate
the pointwise impossibility results of `SurvivorWitness` did **not** exclude — a
certificate existing for the semigroup while invisible pointwise.  Reducibility
removes it: the joint spectral radius is `max(3,2) = 3`, attained by the
single-letter cycle `O`, finiteness holding trivially.

The hoped-for separation — admissible words avoiding the extremal `O ^ k`, giving
restricted radius `< 1 <` unrestricted — is also false, by a witness already here:
`SurvivorWitness` gives `n ≡ −1 (mod 2 ^ (k+1))` taking `k` consecutive odd steps,
so `O ^ k` is admissible for every `k`.  Restricted and unrestricted coincide.

**That residue class has now closed four programmes**: covering systems, block
Lyapunov functions, the JSR separation, and the extremal-word question.  It is the
sharpest single obstruction this development has.

## The four other verdicts

**Furstenberg ×2×3 rigidity — inapplicable, at the definitional step.**  Rigidity
constrains sets invariant under *both* maps; a Collatz orbit is one forced path
carrying an unbounded additive drift (`C_j = 1, 5, 5, 23, 85, …, 2.7·10^7` by
`j = 20`, never returning to `0`).  No free `×2,×3` semigroup action is induced.
Sharper than the agent stated: in the coordinate `u = n+1` the odd branch **is**
homogeneous, `u ↦ 3u/2` — the affineness does not vanish, it relocates to the even
branch as `u ↦ ⌈u/2⌉`.  The `+1` cannot be conjugated off both branches at once,
which is what `DeviceCeiling` localises.  Also worth recording: the *topological*
Furstenberg theorem is **proved** (1967); only the zero-entropy measure case is
open.

**Cohomology — no obstruction, and the reason is exact.**  `C` **is** a coboundary,
tautologically, with primitive `f = id`: the relation `2·T(x) = 3^{a(x)}·x + a(x)`
*is* the coboundary equation.  So there is no cohomological obstruction at the
`1`-cocycle level.  The genuine content is a two-place mismatch — `f = id` is
bounded on the compact `ℤ₂` but unbounded archimedean — which is a reframing, not a
theorem.  The Livsic reading recasts "no nontrivial cycles" as the gap `2^L − 3^a`
never dividing `C_L(w)` consistently, i.e. the Baker route again.

**Model theory — kills the non-standard hope, leaves a design constraint.**
Transfer makes `Π₁`/`Π₂` facts about standard `n` rigid across every elementary
extension: no non-standard-only counterexample and no non-standard-only proof;
overspill merely restates verified bounds inside `*N`.  `*N`'s order is not
well-founded, so it is *worse* than `ℕ` for induction.

The valuable part: Conway (1972) and Kurtz–Simon (2007) undecidability is about the
*family* with moduli and multipliers as unbounded input; `3n+1` fixes both.  So it
forbids any uniform syntax-driven method over the family — **a proof of `3n+1` must
use structure specific to the pair `(3,2)` that does not generalise.**  Notably
`H₂(log 2/log 3)` and the `(3/2) ^ k` witnesses are exactly such facts.  It is *not*
evidence that `3n+1` itself is undecidable.

**Divergent-trajectory characterisation — a challenge to Round XXXVI, checked and
resolved in its favour.**  The agent observed that the never-dropping set needs the
ballot condition at *every* prefix, not the endpoint condition, and measured
exponent `≈ 0.89`, questioning the recorded `0.94996`.  Recomputed here to `j = 400`:

| `j` | ballot | endpoint |
|---|---|---|
| 50 | 0.835 | 0.901 |
| 100 | 0.880 | 0.918 |
| 200 | 0.908 | 0.932 |
| 400 | **0.926** | **0.940** |

Fitting `count ~ C·2^{0.94996 j}·j^{−p}`: ballot gives `p ≈ 1.09, 1.12` at
`j = 200, 400`; endpoint gives `p ≈ 0.47, 0.45`, the standard `1/√j` binomial
correction.  **Same exponential rate, different polynomial prefactors** — exactly
what ballot/reflection theory predicts.  Round XXXVI stands and is now better
supported.

The agent also confirmed exactly, over 8 178 periodic words to `L = 12`: the sign
of the realizer is governed entirely by the sign of `2^L − 3^a`, and for
never-dropping words the denominator in lowest terms is exactly `|2^L − 3^a|`.

## Axiom footprint

`common_eigenvector`: **none**.  `diag_eq`, `growth_factor`,
`extremal_word_admissible`: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added
axioms.  `lake build Collatz` succeeds, 272 jobs.

**Both halves of the conjecture remain open.**

## Round XXXVII, correction after adversarial review

The referee pass on `MatrixReducible` returned **OVERSTATED**, and it is right.
The correction is recorded here and in the module.

**Withdrawn:** "reducible ⟹ no Barabanov norm ⟹ the JSR route is closed."  That
inference is invalid.  Barabanov's theorem supplies an extremal norm for
*irreducible* families; irreducibility buys **uniqueness** and is not known to be
necessary for **existence**.  The usual mechanism by which a reducible family has
no extremal norm is that its invariant subspace grows *strictly slower* than the
ambient joint spectral radius — and here the invariant line is the **dominant**
block, realising `ρ = 3` exactly.  So the non-existence claim needed a separate
proof and did not have one.

**Strengthened, by the same review:** reducibility is *forced*, not incidental.
Representing an affine map `n ↦ αn + β` on `(n,1)` always leaves the constant line
invariant, and every polynomial functor — `Symᵏ`, `⊗ᵏ`, `∧ᵏ`, duals — inherits an
induced invariant flag.  `Sym²E` and `Sym²O` were computed and are again
simultaneously triangular.  **No finite-dimensional affine-embedding representation
escapes**, so the obvious repair is unavailable.

**What stands:** `common_eigenvector` (axiom-free) and `diag_eq` are theorems.  The
joint spectral radius is `3`, attained on the invariant subspace by `O`.  And
`SurvivorWitness` makes `O ^ k` admissible for every finite `k`.

**What the review adds, correctly:** the joint spectral radius was never the right
quantity.  It is a supremum realised only by the infinite all-odd word, which is
reached only in the `2`-adic limit `n → −1` and by no positive integer.  So `ρ = 3`
bounds worst-case *transient* growth and is silent about descent.

**And what the review's proposed escape actually is.**  The referee offers the
typical exponent — subradius, or Lyapunov exponent under the natural measure, with
geometric mean `√3/2 ≈ 0.866 < 1` — as a surviving route, noting reducibility makes
it an elementary scalar computation.  That is correct as computation but is **not a
new route**: it is precisely the Lagarias–Terras negative-drift heuristic, and
Round XXXV already established it admits no deterministic bridge, the drift living
on `ℤ₂` where the never-dropping set has dimension `0.94996` while descent is a
statement about one integer.

**Net:** the theorem survives, one inference drawn from it does not, and the
strengthening (reducibility is forced for all affine embeddings) is a genuine gain
from the attack.  Recording this because the alternative — leaving an overstated
claim in place because it compiles — is exactly the failure mode this development
is supposed to avoid.

# Round XXXVIII — generic Baker is vacuous here, and the known bounds are convergents

The Diophantine pass returned the session's most substantive finding, and it
corrects the framing this development has carried since Round XXII.

## Generic Baker / LMN gives nothing — quantified

The explicit two-logarithm bound has the shape

`log|Λ| > −30.9 · D⁴ · (max{log b′ + 0.38, 21/D, 1/2})² · log A₁ · log A₂`

(Laurent–Mignotte–Nesterenko 1995).  Specialising to `(γ₁,γ₂) = (2,3)`, `D = 1`,
`b′ ≈ 1.541 L`: the `log b′` term does not overtake the floor `21/D` until
`L ≈ 5.85 · 10^8`, so below that the bound is pinned at

`log|Λ| > −30.9 · 21² · log 3 = −14 970.7`,  i.e. `|Λ| > 2.1 · 10^(−6502)`.

The cycle relation needs `Λ < a/(3m)`, about `4.2 · 10^(−13)` at `m > 2^68`,
`a ≈ 3.7 · 10^8`.  **The generic bound is ~6 489 orders of magnitude too weak**, and
its `(log b′)²` growth never closes that at any humanly relevant `L`.

**Consequence for this repository.**  Round XXII framed the remaining content as
"a lower bound on `|L log 2 − a log 3|`, i.e. Baker theory", and `BakerConditional`
names `EffectiveGap f` as the hypothesis.  That is right in form but wrong in
substance for the *generic* instantiation: `EffectiveGap (fun a => a ^ C)` with `C`
from LMN is a true but **empty** hypothesis.  The module docstring is corrected.

This also explains something that had looked like an oversight: Halbeisen–Hungerbühler
reach `10^8` by continued-fraction analysis plus brute-force verification, with **no
Baker-type bound anywhere in their proof**.  That was not a missed opportunity — it
was the only viable route with 1997-era constants, which are still current.

## The lever that is not vacuous

An **irrationality measure**: `|Λ| > C · L^(−μ)` with `μ ≈ 5`–`8.6` for
`ℚ·log 2 + ℚ·log 3` (Rhin 1987; Wu 2003; Salikhov 2007).  A power law beats the
`10^(−6502)` floor at every practical `L`, and `BakerConditional.baker_polynomial`
consumes exactly that shape.  What is missing is the **explicit constant `C`**,
which the published statements do not make easily extractable.

**That is the concrete open computation this route needs** — and it is a different
object from generic Baker, which is the correction.

## The known bounds are convergent numerators — verified here

The continued fraction of `log₂ 3` is `[1; 1,1,2,2,3,1,5,2,23,2,2,1,1,55,1,4,3,1,1,15,…]`.
Recomputed at 200-digit precision:

| `k` | `a_k` | `p_k` | `q_k` | `|q_k x − p_k|` | identification |
|---|---|---|---|---|---|
| 9 | 23 | 24 727 | 15 601 | `2.6·10^(−5)` | Crandall-era dangerous region |
| 13 | 1 | **301 994** | 190 537 | `9.3·10^(−8)` | **Lagarias's bound** |
| 15 | 1 | **17 087 915** | 10 781 274 | `1.8·10^(−8)` | **Eliahou's `k(2^40)`** |

with the large partial quotient `a₁₄ = 55` sitting between them and driving the jump
to Halbeisen–Hungerbühler's `102 225 496`.  **The known Collatz cycle-length bounds
are literally numerators of convergents of `log₂ 3`.**

Large partial quotients occur at `k = 9, 14, 20, 22, 29, 31, 33, 36, 44` with values
`23, 55, 15, 9, 8, 11, 20, 10, 37`; each opens the next dangerous tier.  The
dangerous pairs below any bound are a finite, explicitly enumerable list — which is
exactly the mechanism Halbeisen–Hungerbühler exploit, and it can be pushed further
at the cost of computation plus deeper verification.

## Axiom footprint

No new Lean this round; the findings are numerical and bibliographic, and per the
standing instruction weak material is not formalised merely because it would
compile.  `BakerConditional`'s docstring is corrected.  `lake build Collatz`
succeeds, 272 jobs.

**Both halves of the conjecture remain open.**

## Round XXXVIII, correction — the irrationality measure is not the lever either

Computed before chasing the constant, and the result kills the direction proposed
one round earlier.

Halbeisen–Hungerbühler's criterion excludes a length when
`M_{L,n}/(2^L − 3^n) < m`.  With their Remark 1 bound `M_{l,n} ≤ 0.7·n·3^n` and
`2^L − 3^n = 3^n(e^Λ − 1) ≥ 3^n·Λ`, that is `Λ > 0.7n/m`.  A power law
`|Λ| > C·L^(−μ)` therefore excludes exactly

`L < (2.265 · C · m)^(1/(μ+1))`,  using `n ≈ 0.6309 L`.

At Barina's `m = 704·2^60 ≈ 8.12·10^20` with a **perfect** constant `C = 1`:

| `μ` | source | excludes `L <` |
|---|---|---|
| `8.616` | Rhin 1987 | **163** |
| `5.1163` | Salikhov 2007 | **2 997** |
| `2` | conjectural, unproven for `log₂ 3` | `1.2 · 10^7` |

Against this repository's **unconditional `6 809`** and Halbeisen–Hungerbühler's
**conditional `102 225 496`**.

**So the known irrationality measures deliver less than is already proved here**,
and even the conjectural `μ = 2 + ε` remains an order of magnitude short of `10^8`.
Extracting the explicit constant `C` — named last round as "the concrete open
computation" — would have been wasted effort.  That framing is withdrawn.

**The structural reason, which is the real content.**  A uniform bound
`Λ > C·L^(−μ)` treats *every* `L` as though it were as bad as the worst convergent.
The dangerous `L` are **sparse**: they cluster at convergents of `log₂ 3`, at the
large partial quotients `a_k` for `k = 9, 14, 20, 22, 29, 31, 33, 36, 44`.
Halbeisen–Hungerbühler check those individually and let every other `L` through
cheaply, and that sparsity is worth many orders of magnitude.  No uniform
Diophantine bound can express it.

**Conclusion: the continued-fraction method is not a weaker substitute for
approximation theory — for this problem it is strictly stronger, because the
obstruction is sparse rather than uniform.**  The route forward is `hh_criterion`
evaluated at the dangerous convergents, using machinery already present here modulo
`HHExtremal`; it is not the extraction of any Diophantine constant.

Two self-corrections in consecutive rounds (Barabanov, then this) — both caught by
computing the consequence before committing to the direction.

# Round XXXIX — a definitional bug in my own work, found and fixed; and a real range bound

The wave aimed at discharging `HHExtremal` did not discharge it.  It did something
more useful: it exposed that the chain this log claimed was complete had **four**
gaps, one of them a definitional inconsistency between two modules written here.

## The bug, and the correction to Round XXVII

Round XXVII recorded: *"Every mathematical link of the Halbeisen–Hungerbühler chain
is now proved in this repository."*  **That was wrong.**  The two ends of the chain
used different and unequal definitions of `M_{l,n}`:

* `HalbeisenHungerbuhler.hhMin` — built from `beattyRem` started at `0`, which
  generates the **floor** word (ones as late as possible);
* `ExtremalTime.hhMinTime` — `Crel` of the list `tildeTime l n j = ⌊jl/n⌋`, the
  **ceiling** word (ones as early as possible).

These are different — indeed reversed — extremal words.  Measured: **136 mismatches**
over `2 ≤ l ≤ 17`, e.g. `l = 3, n = 2` gives floor-word `[0,1,1]` with `hhMin = 10`
against ceiling-word `[1,1,0]` with `hhMinTime = 5`.

Halbeisen–Hungerbühler's `s̃ᵢ = ⌈in/l⌉ − ⌈(i−1)n/l⌉` is the **ceiling** word, so
`hhMin` as defined here was the wrong object.  I had noticed the floor/ceiling issue
while writing `ExtremalTime` and did not carry the fix through.

**Fixed:** `beattyRem l n 0 = l - 1` instead of `0`.  With that one change the two
agree exactly — **0 mismatches** over the same 136 shapes.  `beattyRem_lt`,
`beatty_invariant` (now `remainder + l·weight = (l−1) + i·n`) and `beatty_count_eq`
all still hold and still compile.

No *proved* theorem was false: `hh_criterion` is conditional on `HHExtremal`, which
is an assumed `Prop`, and nothing claimed the two `M` definitions agreed.  But the
**narrative** was wrong, and a plan built on it would have failed at exactly this
join.

## The four real gaps to `HHExtremal`

Now stated properly, since "only the rotation argument remains" was optimistic:

1. the `w`/`word_x` bridge with `partialSum (w x) L = oddCount x L` — mechanical;
2. an `affineC`-to-`Crel` correspondence connecting the `List Bool` apparatus
   (`AccumulatorAutomaton`) to the `Nat → Nat` apparatus (`CycleLemma`,
   `ExtremalTime`) — **absent from the repository**;
3. a rotation law transporting the *minimality of `x`* across rotations — the real
   mathematical gap, since `cycle_lemma` selects its own rotation, not the one where
   `x` sits;
4. `hhMinTime = hhMin` — now true after the fix above, but still unproved in Lean.

## The range-valid bound on `Λ` (verified, not yet formalised)

The sparsity track produced a genuine reduction.  With `Λ(a) = L·log 2 − a·log 3`
and `L = ⌊a·log₂3⌋ + 1`, so `Λ(a) = log 2 · (1 − {a·log₂3})`:

* **Parity split.**  Only convergents with `p_k/q_k > log₂3` are dangerous — the
  other parity gives `Λ ≈ log 2`, never small.  Dangerous `k` are the odd indices
  `1, 3, 5, 7, 9, …`.
* **Range bound.**  For a dangerous `k` and *every* integer `a` with
  `q_k ≤ a < q_{k+1}` (next dangerous denominator), `Λ(a) ≥ Λ(q_k)`, and
  `Λ(q_k) > log 2 / (q_{k+1} + q_k)`.

Verified independently here: **72 520 points, 0 violations** on the dangerous
parity, and the second inequality holds at all 27 convergents tested.  (A first
test of mine appeared to refute it with 353 554 violations — that run wrongly
included the safe parity.  Recorded because the failure mode is instructive.)

**What it buys:** checking `Λ(a)` for every `a ≤ N` — `O(N)` work — becomes
enumerating the `O(log N)` convergent denominators and applying one lemma per
interval.  A single application covers the whole `a₁₄ = 55` gap, about `10.6`
million values of `a`.

**What it does not buy:** the partial quotients of `log₂3` have no known closed
form, so the continued-fraction data remains empirical input to the theorem rather
than derivable.  The three-distance theorem does not rescue this — it bounds the
*number* of gap lengths (`≤ 3`), not their values, and the values are exactly the
CF data.

## Two other tracks, both shallow, one useful diagnosis

**Divergence half:** four necessary conditions on a minimal divergent start
(odd; exactly one even step after the opening odd run; sustained super-critical odd
density; merge-avoidance) — all real, all *restricting to the same*
dimension-`0.94996` set.  They are re-derivations of one membership condition from
different angles, not independent constraints, so they do not multiply.

**Fresh hunt:** the adelic idea is dead for a clean reason — `3n+1 ≡ 1 (mod 3)`
always, so `v₃(3n+1) = 0` unconditionally, while the branch decision is `n mod 2`.
**The 2-adic and 3-adic pictures never interact.**  That narrows the standing
diagnosis: the missing constraint cannot be `2`-adic × `3`-adic; it must be
`2`-adic × **archimedean** — parity against size — which is exactly what the
`Z[√−2]` filter demands when it says a proof must use the order of `ℤ`.

## Axiom footprint

`beatty_invariant`, `beatty_count_eq`, `beattyRem_lt` unchanged in status after the
correction: `propext`, `Quot.sound`.  Zero `sorry`.  Zero added axioms.
`lake build Collatz` succeeds, 272 jobs.

**Both halves of the conjecture remain open.**

## Round XL — the bridge, and three interface tracks that died

The corrected diagnosis from Round XXXIX said the missing constraint must be
`2`-adic × **archimedean**.  Four tracks were run against that specification.
One produced a theorem.  Three produced precise dead ends, recorded here so the
elimination is not repeated.

### What was built: `Strategy/HHBridge`

The repository had grown two descriptions of the affine accumulator and never
joined them: the **word** side (`DeltaSpectrum.accC`, `C`, `gap`) folding
`c ↦ 3c + 2^j` along a `List Bool`, and the **orbit** side
(`AffineExact.affineC`, `oddCount`, `CycleLemma`) reading the same recursion off
`acceleratedOrbit`.  The missing sentence is that they are the same recursion
driven by two sources of parity bits.  `HHBridge` supplies it:

* `w x i = acceleratedOrbit i x % 2` — the orbit's word as a `Nat → Nat`.
* `w_periodic` — on a cycle it is periodic, which is exactly `CycleLemma`'s hypothesis.
* `partialSum_eq_oddCount` — `CycleLemma.partialSum (w x) L = oddCount x L`.
* **`affineC_eq_C : affineC L x = C (word x L)`** — the two accumulators are the
  same number.
* `oddCount_word`, `gap_word` — and the two odd-counts agree, so
  `gap (word x L) = 2 ^ L − 3 ^ oddCount x L`.

Axioms: `propext`, `Quot.sound`, `Classical.choice`.  Zero `sorry`.

This closes gaps (1) and (2) of the four separating `CycleLemma` from
`HHExtremal`.  **It does not close (3) or (4), and `HHExtremal` remains an
assumed `Prop`.**  Still open: `hhMinTime l n n = hhMin l n l` — numerically
true for `2 ≤ l ≤ 17` after the Round XXXIX ceiling fix, but a genuine
sum-reindexing induction (sparse fold over one-positions against a full fold with
zero-weighted gaps); and the rotation law transporting minimality of `x` across
the rotation `cycle_lemma` selects for itself.  Nothing downstream of
`HHExtremal` has become unconditional.

### Dead end 1: heights and the product formula

The canonical object coupling the `2`-adic and archimedean places, and the
obvious candidate.  A periodic word's realizer is `x*(w) = C(w)/(2^L − 3^a)`.
The hoped separation was a height inequality dividing "positive integer" from
"negative rational with denominator `|2^L − 3^a|`" inside one `2`-adic cylinder.

**It fails, and cleanly.**  The height of the realizer is governed by
`gcd(C(w), 2^L − 3^a)`, which is uncontrolled.  Verified exhaustively at
`L = 16`: of `6848` primitive words with negative realizer, `652` have reduced
height strictly below `log|2^L − 3^a|` — e.g. the word `0010111111111101`
(`a = 12`, denominator `465905`) reduces to `−320596/42355`, a collapse of
`0.37` nats.  The extreme case is the all-ones word, which gives `x* = −1` for
**every** `L` while `|2^L − 3^L| → ∞`.  Since these are all degree-1 points,
Lehmer/Dobrowolski bounds say nothing, and the only available lower bound is
saturated by a genuine admissible point.  **No height obstruction of the form
"large denominator ⇒ large height" exists here.**

The `{2,3,∞}`-restricted adelic norm was also computed along orbits: it equals
the part of `n` coprime to `6`, is neither conserved nor monotone, and is
elementary.  The full product formula is identically `1` and says nothing.

### Dead end 2: bit-length against `2`-adic depth

The measured phenomenon — a `6`-bit integer sustaining a run needing `59` bits of
depth — invited the law `B ≤ c · b` (non-dropping run length against bit-length).
Measured for **every odd `y < 2^27`**, taking the record-holder at each bit-length:

| `b` | 5 | 8 | 10 | 14 | 18 | 21 | 24 | 27 |
|---|---|---|---|---|---|---|---|---|
| max `B` | 36 | 24 | 50 | 65 | 77 | 140 | 180 | 231 |
| `B/b` | 7.2 | 3.0 | 5.0 | 4.6 | 4.3 | 6.7 | 7.5 | 8.6 |

**`B/b` climbs across the whole measured range** — roughly `3` at `b ≈ 8` to `8.6`
at `b = 27` — with no sign of levelling.  A linear bound would force the ratio to
plateau or fall; it does the opposite.  The data therefore *refutes* the hoped
inequality rather than failing to confirm it.  (Evidence only, `b ≤ 27`; the true
growth rate of `maxB(b)` is not pinned down, with everything from a steeper line
to `b^1.77` consistent.)

The mechanism is worth keeping.  For every record-holder from `b = 10` up, the
odd density `S/B` converges tightly to `log₂3 ≈ 1.585` — the records sit almost
exactly on the critical threshold where a non-dropping run can exist at all.  What
defeats the bound is that *bits of `y` consumed per run-step keeps shrinking*
(`≈ 0.2` at `b = 10`, `≈ 0.12` at `b = 27`): larger integers find more room per
step to stay near critical density.  The record-holders share a signature — a long
run of trailing `1`s, i.e. `y ≡ −1 mod 2^k` for growing `k`, behind a sparser
prefix — which is the `n ≡ −1 (mod 2^k)` class yet again, but they fit no closed
form and look like lattice local optima rather than a family.

### Dead end 3: the size/valuation coupling is Terras

The most promising-looking lead was that an odd run multiplies `u = n+1` by `3/2`
while consuming exactly one factor of `2` from `v₂(u)` per step — an apparent
lockstep of magnitude and valuation.  Checked for all odd `n < 200000` with zero
mismatches: the maximal odd run starting at `n` has length exactly `v₂(n+1)`.

**This is the classical Terras run-length theorem**, restated.  Any quantity built
linearly on it — `Φ(n) = log n − c·v₂(n+1)` and relatives — reduces to the standard
drift heuristic `E[Δ log n] = log₂3 − 2 < 0`, which is a *statistical* statement
about the run-length distribution, not a pointwise invariant, and is precisely
what the block-Lyapunov exclusion already kills.  Marked as rediscovery.

### The standing diagnosis, unchanged

Three independent attempts to instantiate "`2`-adic × archimedean" produced two
rediscoveries and one clean impossibility.  The specification is still the right
one, and still unmet.  Nothing here narrows it further; what it does establish is
that the two most natural formalisms for coupling the places — heights over the
adeles, and valuation-weighted Lyapunov functions — are both spent.

### Axiom footprint

`lake build Collatz` succeeds, **273 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round XLI — three of the four gaps close, and a claim of mine is refereed down

### `HHExtremal`: gaps (1), (2), (3) closed, (4) reduced

`HHExtremal` is still an assumed `Prop`.  Everything downstream of it is still
conditional.  What changed is the size and shape of what is missing.

**`Strategy/HHBridge` — gaps (1) and (2).**  The repository had two descriptions
of the affine accumulator and never joined them: the word side
(`DeltaSpectrum.accC`, `C`, `gap`) folding `c ↦ 3c + 2^j` along a `List Bool`,
and the orbit side (`AffineExact.affineC`, `oddCount`, `CycleLemma`) reading the
same recursion off `acceleratedOrbit`.  The missing sentence is that they are one
recursion with two sources of parity bits:

* `w x i = acceleratedOrbit i x % 2`, `w_periodic`, `partialSum_eq_oddCount`;
* **`affineC_eq_C : affineC L x = C (word x L)`**;
* `oddCount_word`, `gap_word` — so `gap (word x L) = 2^L − 3^(oddCount x L)`.

**`Strategy/HHMinTime` — gap (3).**  `hhMinTime l n n = hhMin l n l`: the two
constructions of `M_{l,n}` are one sum reindexed along the support of the ceiling
Beatty word.  The endpoint does not induct; the prefix invariant

`hhMin l n j = 3 ^ (n − beattyCount l n j) · hhMinTime l n (beattyCount l n j)`

does, and collapses at `j = l` where the count is `n`.  Note this is only *true*
because of the Round XXXIX ceiling fix — before it the two sides disagreed at 136
of the tested points, and this file could not have existed.

**`Strategy/RotationLaw` + `HHBridge` — gap (4), reduced not closed.**
`HHExtremal` assumes `x` is the orbit *minimum*; `cycle_lemma` picks its own
rotation `r` and concludes about `acceleratedOrbit r x`.  The two never met.

* **`oddCount_rotation_invariant`** — on a cycle, `oddCount` over a full period is
  the same at every rotation.  So the exponent `a`, and the gap `2^L − 3^a`, are
  properties of the *cycle*, not of the point chosen to name it.
* `affine_cycle_eq_rotation`, `gap_mul_le_affineC_rotation` — the affine cycle
  equation holds at every rotation with the same `a`, and if `x` is the minimum
  then `gap · x ≤ affineC L (orbit i x)` for every `i`.  A bound proved at *any*
  rotation bounds the minimum.
* `w_rotate` (no hypotheses), `w_period_mul`, `w_mod`, `w_rotate_mod` — on a cycle
  the word depends only on the index mod `L`.
* `partialSum_rotate`, `oddCount_rotate_eq` — the odd-step count splits at a
  rotation, in the shape `cycle_lemma_time` consumes.
* **`rotation_time_bound`** — hence: on a cycle there is a rotation whose
  odd-step times are dominated by the extremal Beatty times, with all of
  `cycle_lemma_time`'s abstract hypotheses discharged.

What remains is an *indexing* mismatch, and it is now the whole of gap (4):
`rotation_time_bound` bounds a time `t` by the extremal time of the count reached
at `t`, while `dominating_le_hhMinTime` wants the `j`-th one-position bounded by
the `j`-th extremal time.  Producing that function — the `j`-th one-position of
the rotated word, and `times (word y L) 0` as its list — is one lemma, not a
chaining step, and it is not in the repository.

### `Strategy/ExclusionRatio`: the range separates from the length

The product test `3^a·(3c + 2a) < 3c·2^L` is *equivalent*, given `3^a ≤ 2^L`, to
`2a·3^a < 3c·(2^L − 3^a)`.  So `L` is excluded exactly when `c` exceeds

`r(L) = 2a·3^a / (3(2^L − 3^a))`,

**a quantity depending on `L` alone**.  Two consequences, both proved:
`excluded_of_le` (a wider range never loses a length) and, the load-bearing one,
**`excluded_transfer`** — if `r(L) ≤ r(L')`, stated cross-multiplied so no
division is needed, then any range excluding `L'` excludes `L`.  A length can be
killed by a witness at a *different* length.  That is the shape an interval
certificate needs, and it makes interval exclusion a mechanism rather than the
compute optimisation it was dismissed as.

**The frontier is a staircase on the semiconvergents.**  Writing
`2^L/3^a = 1 + d(L)`, we get `r(L) = 2a/(3d(L)) ≈ 0.42 L/d(L)`, so `L` survives
when `a/L` approximates `log₃ 2` unusually well *from the correct side*.
Measured frontiers, exact integer arithmetic:

`485, 1539, 2593, 3647, 4701, 5755, 6809, 7863, 8917, 9971, 11025, 12079, 13133,
14187, 15241, 16295, …, 24727`

— constant step `1054` throughout.  `485/306` and `1054/665` are consecutive
convergents of `log₂ 3`, and `485 + 23·1054 = 24727` is the next convergent, so
these are exactly that block's semiconvergents.  The frontier never lands
anywhere else.

### Two corrections to the repository's own record

`CycleLength2593`'s docstring table gives `102400 → 520` and reads a square-root
law off it.  Both are wrong.  `520` was never a frontier: it is where
`CycleProduct.excludedLength_of_lt` stopped for compute reasons, and that theorem
uses `c = 307200`, not `102400`.  The true frontier at `102400` is **485**,
confirmed by `excludedFast` and by the full `O(L)` scan independently.  With the
row corrected the fitted exponent over fifteen ranges spanning a factor of `240`
is `L ~ c^0.64`, not `c^0.5` — and it is not a power law at all, but the
staircase above.

### A claim of mine, refereed and refuted

I computed that at Barina's verified range `c = 704·2^60` the product bound's
frontier is `L = 114 208 327 604 ≈ 1.14 × 10¹¹`, six orders of magnitude past the
repository's recorded conditional `40 001` and past Eliahou's `17 087 915`.  I
sent it to an adversarial referee before recording it.  **It came back refuted as
a statement about this repository, and I confirmed the refutation myself.**

The idealised arithmetic is right: at `L = 10 439 860 591`, `d = 1.012×10⁻¹¹` and
`r = 4.338×10²⁰ < c`; at `L = 114 208 327 604`, `d = 5.511×10⁻¹²` and
`r = 8.717×10²¹ > c`.  Both check to full precision, and the second `L` is
`q₂₃ + q₂₂` for consecutive convergent denominators of `log₃ 2`.

But those numbers use `⌊L log₃ 2⌋`, and the repository uses `topIndex`, a fixed
rational in error by `1.53×10⁻¹⁹` per unit `L`.  At exactly these two lengths
**`topIndex` undercounts the true floor by one**, `excludedFast`'s first conjunct
`2^L ≤ 3^(topIndex L + 1)` fails, and the repository's actual test excludes
*neither* length — including the one my narrative called excluded.  The claim as
I stated it was about a function the repository does not compute.

This costs no soundness: that conjunct is a self-check, a wrong `topIndex` can
only refuse a length, never falsely exclude one, and no proved theorem moves.  It
costs reach, and the reach is now pinned: **`topIndex` is exact for every
`L < 10 439 860 591`** (brute-forced below `3×10⁶`; past that only one-sided best
approximations can trigger a disagreement, and that `L` is the first).  Every
bound the repository proves, and the conditional sweep at `L ≤ 40 000`, sits far
inside the safe range.  Anything aiming near `10¹⁰` needs an exact `topIndex`
first — an obstacle beyond the raw `10¹¹` checking cost, and one I had not seen.

### Axiom footprint

`lake build Collatz` succeeds, **276 jobs**.  Zero `sorry`.  Zero added axioms.
Every theorem named above: `propext`, `Quot.sound`, some also `Classical.choice`.

**Both halves of the conjecture remain open.**

## Round XLII — Lemma 5 is proved, and it changes no number

### `HHExtremal` is no longer a hypothesis

`Strategy/HHLemmaFive` proves `hhExtremal_holds : HalbeisenHungerbuhler.HHExtremal`.
Axioms: `propext`, `Quot.sound`.  No `sorry`, nothing added.  The `Prop` the
repository carried as an assumption from Round XXV onward is discharged, and
`hh_criterion` / `hh_no_cycle_below` are unconditional.

The four gaps, closed in order:

1. **`HHBridge.affineC_eq_C`** — the word side and the orbit side of the
   accumulator are one recursion.
2. **`HHBridge.oddCount_word`, `gap_word`** — and the two odd-counts agree.
3. **`HHMinTime.hhMinTime_eq_hhMin`** — the two constructions of `M_{l,n}` are one
   sum reindexed along the support of the ceiling Beatty word.  *True only because
   of the Round XXXIX floor/ceiling correction*; before it the two sides disagreed
   at 136 points and this step was false.
4. **`RotationLaw.oddCount_rotation_invariant`** — `oddCount` over a full period is
   rotation-invariant, so the gap `2 ^ L − 3 ^ a` belongs to the *cycle*, not to
   the point, and `gap_mul_le_affineC_rotation` transports a bound at any rotation
   back to the orbit minimum.  Then `HHBridge.T` (the `j`-th one-position, a
   fuelled scan — there is no `Nat.find` here), `rotation_position_bound`, and
   finally `HHLemmaFive.times_word_eq`: the positions `times` reads off the word
   are exactly the one-positions `T`.

### It was checked, not assumed

* Over **4072 words** with `2 ≤ l ≤ 12`: every word has a rotation whose `j`-th
  one-position is `≤ tildeTime l n j`, and `min` over rotations of `C` is at most
  `hhMin`.  Zero violations of either.
* `hhMin l n l` is **exactly** `max_w min_r C(rot_r w)` over all `l ≤ 11` — zero
  slack.  So it is genuinely `M_{l,n}` and the bound is sharp, not a surrogate.
* Tight on the trivial cycle: `gap · x = 1 = hhMin 2 1 2`.
* An adversarial referee attacked vacuity, the identification of `hhMin` with
  `M_{l,n}`, circularity, the correctness of `affineC`, and all five new lemmas
  against real orbits (`x ∈ {1,3,5,7,9,11,27,703,12345}`, `L ≤ 30`).  No
  counterexample, no gap.  It did find four docstrings still narrating the gaps as
  open — false statements by then, since corrected.

### And it buys no new number

This is the part worth stating plainly.  Evaluating the now-unconditional
criterion at the repository's verified range `c = 1 086 464`, at the largest
admissible `n` for each `L`:

`hhMin L n L < (2 ^ L − 3 ^ n) · c` holds for every `L ≤ 6808` and fails first at
exactly `(L, n) = (6809, 4296)`.

That is **precisely** the wall of `RealizableFrontier6809.length_ge_6809`, which
the repository already proves unconditionally by an entirely different route.
The sharp criterion reproduces the existing bound and does not exceed it.  (An
agent reported this as a `2.63×` improvement by comparing against
`CycleLength2593`; that is not the repository's best bound, and the comparison was
wrong.  Verified independently: the criterion holds at `L = 2593, 4701, 6808` and
fails at `6809`.)

**Why**: both methods are stopped by the same Diophantine obstruction.
`6809 = 485 + 6·1054` is a semiconvergent of `log₂ 3` — the same ladder
`ExclusionRatio` found the product-bound frontier on — and there `3 ^ n` sits so
close to `2 ^ L` from below that the gap collapses relative to `hhMin`.
Sharpening the *criterion* cannot move a wall whose position is set by how well
`n/L` approximates `log₃ 2`.  Three independent methods — the product bound, the
realizable-frontier certificate, and now the sharp H–H criterion — all stop at
`(6809, 4296)`.

What the proof does buy is **exchange rate**: the criterion is sharp, so future
increases in the verified range convert into length more efficiently.
Conditionally on Barina's `704 · 2 ^ 60` the criterion survives past
`L = 125 743`, against the `40 001` the repository's conditional sweep records —
but that is a measurement, not a theorem, and certifying it needs an `O(log L)`
evaluation of `hhMin`, which does not exist here.  Reaching the paper's
`102 225 496` needs that same fast evaluation and is out of reach of both `decide`
and direct computation.

### Axiom footprint

`lake build Collatz` succeeds, **277 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**  What closed is a lemma, inside the
cycles half, that the repository had been assuming.

## Round XLIII — seven sparks, six deaths, and the price list

A deliberately creative wave: seven independent agents, each given a short spark
rather than a prescribed method, each told to falsify its own idea and to say
whether it touches the `(6809, 4296)` wall.  Six died.  The round's real result
came from a computation none of them was running.

### The price list

`HHLemmaFive` made the Halbeisen–Hungerbühler criterion unconditional and then
showed it merely reproduces the existing `6809`.  The operational question is
what each further length would *cost*.  The criterion kills `L` when
`hhMin L n L < (2^L − 3^n)·c`, so `L` is killed exactly when

`c > hhMin L n L / (2^L − 3^n)`,

a rational in `L` and `n` alone.  Exact rational evaluation at `n = nmax L` (which
maximises the threshold — checked against *all* admissible `n` for every `L < 60`
and at `L = 485, 1539, 2593`, no exception):

| `L` | verified range needed |
|---|---|
| `485` | `72 059` |
| `1539` | `238 671` |
| `2593` | `420 842` |
| `4701` | `841 478` |
| `5755` | **`1 086 055`** |
| `6809` | **`1 358 718`** |
| `7863` | `1 664 599` |
| `9971` | `2 403 661` |
| `14187` | `4 733 176` |
| `24727` | `206 178 000` |

**The repository's verified range is tuned to the wall.**  `1 086 464` clears the
price of `5755` — `1 086 055` — by `409`, and falls short of `6809`'s price by
exactly `1.2506×`.  The constant was chosen to sit just past a ladder step.

**Proving Lemma 5 did buy something, and this is what.**  The product bound needs
`c = 3 072 000` for `6809` and `12 288 000` for `14187`; the sharp criterion needs
`1 358 718` and `4 733 176` — `2.26×` and `2.60×` cheaper.  The gain is in the
exchange rate, which is invisible at today's `c` and real at any larger one.

**The next step is now priced**: verifying to `1 358 718`, a `1.2506×` extension
of a range this repository has already widened twice, moves the unconditional
cycle-length bound from `6809` to `7863`.  Arithmetic, not insight — but written
down so the cost is known before it is paid.  `Strategy/HHThreshold` holds
`hhKills`, its monotonicity in `c`, the criterion in threshold form, and the first
rung kernel-checked both ways (`485` killed at `72 059`, not at `72 058`).

### A claim checked and withdrawn

One agent proposed that the wall sits where the entropy of the extremal gap
sequences, `log₂ C(a, L−a)`, crosses `log₂ G`.  **There is no crossing.**  Along
the ladder: `295.2` vs `476`, `945.4` vs `1530`, `4199.7` vs `6799` at the wall,
`6152.7` vs `9961` past it — entropy stays below bit length by a near-constant
ratio `≈ 0.62` throughout, with nothing distinguishing `6809`.  The comparison
describes every rung equally and therefore explains no wall.

### The six deaths, each with its cause

* **Orbit geometry** (shoelace area of the lattice staircase `(a_k, b_k)`).  Dies
  on **F1**: the area depends only on the parity word, so every integer realising
  that word gives the same value — an instance of the repository's own
  `NoWindowObstruction`.  Restoring integer-sensitivity collapses it back to the
  log-linear bound and its wall.
* **Nonlocal potential** (excursion peak ratio `M(n)/n` to first return below `n`).
  Unbounded already below `2×10^5` (`Φ(159487) ≈ 53930`), and non-monotone along
  excursion chains in 17–42% of steps with no signed drift.  Inherits the
  unbounded run-length statistic rather than escaping it.
* **Inverse-tree topology.**  Dies at the König trap, correctly identified: the
  finitely-branching tree is the one rooted at `1`, where König gives the vacuous
  branch `1→2→4→…`; a divergent orbit is a single *path*, with no branching for
  König, Nash–Williams or a wqo to bite on.  The right tool there is the
  well-ordering of a minimal counterexample, which the repository already uses.
* **Parity as a code.**  The word-to-minimal-realizer map is a bijection onto
  `[0, 2^k)` that is *not* an isometry — single-bit flips move the realizer by
  `896, 2935, 8192, 4135, 111, …` with no dependence on Hamming distance.  A
  full-rate code with no distance is degenerate; this is the finite-window
  bijection wearing coding-theoretic clothes.
* **Defect cancellation** in `u = n+1`.  The identity is exact and confirmed
  (10 000 starts × 300 steps, zero failures), but `u_j = n_j + 1` is a constant
  shift, so it is an isomorphism, not a reduction: any potential built from `u` is
  `affineC`/`deficit` re-encoded, and inherits the same wall.
* **Integrality via norm forms.**  `G = 2^L − 3^a ≡ 5 (mod 8)` for odd `a` and
  `≡ 7` for even `a`, always, while `u² + 2v² mod 8 ∈ {0,1,2,3,4,6}` — so `G` is
  never a norm from `Z[√−2]`.  True, and **information-free**: it holds identically
  whether or not a cycle exists.  A textbook **F3** death — an order-blind fact
  about `G` alone cannot separate `ℤ` from the ring that has a 13-cycle.

The seventh, a Skolem–Mahler–Lech reduction, is not a known restatement and
clears F1 and F2, but needs the order of `ℤ` smuggled back in separately (F3) and
degrades at exactly the convergent where `2^L/3^a → 1`.  Blocked at the same wall.

### What the wave establishes

Every one of the seven, when pushed, either ignored the integers (F1), ignored the
order (F3), or reduced to the `2^L` versus `3^a` comparison and stopped at
`(6809, 4296)`.  That is now five independent methods stopping at the same pair.
The wall is not an artefact of any technique; it is where the ladder of
semiconvergents of `log₂ 3` puts it.

### Axiom footprint

`lake build Collatz` succeeds, **278 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round XLIV — the price has a closed form, and the ladder can never be paid off

The instruction was to attack the price function itself and find a mechanism
collapsing the whole semiconvergent ladder rather than buying one rung.  The round
found the closed form, reproduced the published bound from it, and then proved the
collapse is impossible by that route.

### The price in closed form

Writing `x = L/a ≈ log₂ 3`, the terms of `hhMin` are
`3^(a−1−j)·2^⌊jx⌋ ≈ 3^(a−1)·(2^x/3)^j·2^(−{jx})`, and `2^x/3 → 1`, so only the
fractional-part factor survives.  `{j log₂ 3}` equidistributes, its average is
`∫₀¹ 2^(−t) dt = 1/(2 ln 2)`, hence `hhMin ≈ 3^a·a/(6 ln 2)` and

**`price(L) ≈ a / (6 ln 2 · δ)`, `δ = 1 − 3^a/2^L`, `1/(6 ln 2) = 0.2404491733…`**

Reproduces every exactly-computed price to within `0.03 %`, and needs no `hhMin`
evaluation — which is what makes the ladder computable past `L = 10^5`, where the
`O(L)` bignum sum stops being feasible.  Derived here twice, independently: once
from the geometric-series argument above and once by a referee, landing on the
same constant.

**Correction to my own first statement of it.**  I recorded `0.2404` as a constant
"to four decimals".  A referee refuted that framing and is right: it is the *limit*
of a slowly converging sequence, measured `0.24060, 0.24042, 0.24039, 0.24045,
0.24045` at `L = 485, 1539, 9971, 125743, 301994`.  The constancy is asymptotic,
not exact.

### The ladder's block structure, and the published bound reproduced

The ladder is **not dense**.  A block based at an odd-index convergent `(P,Q)`
steps by the next convergent `(P′,Q′)`, giving rungs `(P + kP′, Q + kQ′)` for
`k = 0…t` with `t` the next partial quotient, landing exactly on the following
convergent.  Because the partial quotients of `log₂ 3` include `23` and `55`, the
blocks are wildly uneven:

`485…24727` (23 rungs) | `24727, 75235, 125743` | `125743, 301994` |
`301994, 17087915` | `17087915, 102225496, 187363077, 272500658`

**There is no dangerous rung between `301 994` and `17 087 915`** — the ladder
steps over `10^6` and `10^7` entirely.  Paying one rung's price buys everything up
to the *next* rung, however far.

This reproduces Halbeisen–Hungerbühler exactly.  They report `L_max = 102 225 496`
with `m = 2.12 × 10^14`; the closed form gives `price(17 087 915) = 2.124 × 10^14`
— **that is their `m`** — which pays through Eliahou's `17 087 915`, and the next
rung, `17 087 915 + 85 137 581 = 102 225 496`, is therefore the first survivor and
their `L_max`.  Derived here without reference to the paper, landing on both of
its constants.  (I first recorded this as an unresolved `8.4×` discrepancy; it is
not one.  The gap in the ladder is the explanation.)

### The limitative theorem: no finite verification collapses the ladder

On the ladder, continued-fraction theory gives `δ ≈ ln 2 / a_{k+1}`, so

**`price(L_k) ≈ a_k · a_{k+1} / (6 ln 2)`.**

Convergent denominators satisfy `a_{k+1} ≥ a_k + a_{k−1}`, so `a_k → ∞` and the
price diverges — **whatever** the partial quotients of `log₂ 3` turn out to be, an
open Diophantine question this argument does not need.  Therefore:

> **For any fixed verified range `c`, the criterion kills only finitely many
> lengths `L`, and fails on the whole infinite one-sided convergent ladder.**

The escape route was checked and closed: `n = nmax(L)` is genuinely the argmax of
the price over all admissible `n` (verified exhaustively to `L = 4701`), and
smaller `n` only enlarges the denominator, lowering the price — so no other choice
of `n` rescues boundedness.

This is the honest answer to "make the ladder collapse": **it cannot be collapsed
by paying.**  Raising the verified range is a treadmill, not a route.  Excluding
cycles outright requires an argument that is not a threshold in `c` at all.  That
is the real content of the `(6809, 4296)` wall.

### Four sparks, four deaths

* **Sharpen the numerator** — is `hhMin` loose because the extremal Beatty word is
  unrealizable?  **No.**  Explicit witnesses found for every `L` from `3` to `26`
  (e.g. `L=18`: `x = 227195`; `L=21`: `x = 403323`), by forward brute force and by
  reverse-map reconstruction independently.  The minimising word genuinely occurs
  as an orbit's odd-step time list, so the numerator is not loose that way.  Not
  yet tested: realizability as a *closed cycle* rather than an orbit segment,
  which is the stronger and still-open version.
* **A 2-adic × archimedean invariant dominating the price.**  Died on a sharp
  structural point worth keeping: in `u = n+1` the odd run is *exactly*
  `u ↦ 3^r u/2^r` with `r = v₂(u)`, loss-free, verified — and because it is
  loss-free **any invariant built from that recursion is provably equivalent to the
  founding identity** `(2^L − 3^a)x = Σ 3^(a−1−j) 2^(t_j)`, so it inherits the same
  `δ → 0` degeneracy.  There is no leak to build a second, independent inequality
  from.  That explains why this whole line keeps dying.
* **A new object from the dangerous pairs.**  The price generating function is
  Möbius in `k` with a pole at `k* = ε₀/|ε₁|`, and `⌊k*⌋` is exactly the next
  partial quotient.  Real, but it is the mediant-termination fact of the
  Stern–Brocot algorithm in generating-function clothing — and equally true
  whether or not a cycle exists.  Information-free.
* **Barrier inversion.**  The candidate obstruction `v₂(S) = t₀ = 0` collapsed into
  the indexing convention, vacuous before any filter applied.  The one angle left
  unrun is the *ordered* residue condition modulo the small prime factors of
  `G = 2^6809 − 3^4296` (`31² · 191 · 617249 · cofactor`) — the residue *multiset*
  is known unconstrained, the ordered sequence is untested.

### Axiom footprint

`lake build Collatz` succeeds, **278 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

### Addendum: why "stronger than continued fractions" has nothing to grip

The fifth spark asked for machinery beyond ordinary continued fractions to control
`2^L − 3^a`.  All four candidates failed, and the reason for the last one is worth
keeping because it is structural rather than circumstantial.

* **`p`-adic divisibility is information-free.**  For `p ∤ 6`, `p | 2^L − 3^a` iff
  `L·ind(2) ≡ a·ind(3) (mod ord_p)` — a linear congruence on `(L,a)`, satisfied by
  a positive density of all pairs.  Verified directly at the wall:
  `G = 2^6809 − 3^4296` has `31² · 191 · 617249` dividing it exactly (exponents
  `2, 1, 1`), with a `6799`-bit total and `G ≡ 7 (mod 8)` as the parity of `a`
  predicts.  But a genuine cycle's `G` would satisfy whichever congruences it
  happens to satisfy, equally unremarkably.  Divisibility says nothing about the
  *archimedean* size of `G`, which is the only thing the exclusion needs.  Same
  vacuity as the `G ≡ 5, 7 (mod 8)` result of Round XLIII.
* **Ostrowski numeration** in the CF basis of `log₂ 3` is a bijective recoding of
  the continued fraction.  A "characteristic digit pattern" for dangerous `L` *is*
  the one-sided-best-approximation statement, redisplayed.
* **LLL and simultaneous approximation collapse to CF, and here is why.**  `(L,a)`
  is not a free lattice point: it is pinned by the single relation
  `a/L ≈ log₃ 2`.  The problem is **intrinsically one-dimensional** — one real
  number, one linear form.  Lattice-reduction machinery earns its keep when there
  are two or more *independent* forms to control jointly; with one, it reduces to
  the continued fraction it was meant to beat.

That is the general shape of this round's negative results.  The `2^L` versus `3^a`
comparison is a one-dimensional Diophantine problem whose optimal tool is already
the continued fraction, and every richer formalism either recodes it or adds a
condition that holds regardless of whether a cycle exists.  A device that beats the
wall cannot be a better way of comparing `2^L` with `3^a`; it has to be something
that does not reduce to that comparison at all.

## Round XLV — the divergence half, and why one coordinate is never enough

Three heavily constrained tracks against divergence.  All three died, each with an
exact reason, and the reasons agree.  The round's result is the agreement.

### The foundational lemma, formalised

`Strategy/DensitySaturation`, proved, axioms `propext`/`Quot.sound`:

**`orbit_pow_pred : T^i(3^k · 2^m − 1) = 3^(k+i) · 2^(m−i) − 1` for `i ≤ m`.**

One factor of `2` traded for one factor of `3` per step, for as long as the twos
last.  At `k = 0` this is the orbit of `2^j − 1`, whose first `j` iterates are all
odd — `oddCount_allOnes : oddCount (2^j − 1) j = j` — and which then lands on
`3^j − 1`, even (`allOnes_exhausts`).

So a positive integer imitates the `2`-adic integer `−1` for exactly `v₂(n+1)`
steps and no more.  Hence `no_finite_density_obstruction`: for every window length
`j` there is an explicit positive integer whose first `j` steps have odd-step
density **1**, above any threshold, in particular above the critical `log₃ 2` a
divergent orbit must sustain.  **No density test read off a prefix, or a prefix
average, separates anything.**  The density analogue of
`no_finite_window_obstruction`, and sharper: the extreme case is written down.

### Track 1 — carry-bit exhaustion.  Dead, by control.

Capacity `c(n) = v₂(n+1)`; consumption of a run of length `r` is exactly `r`.
Measured creation `r' = v₂(next + 1)` over `10^7` odd `n ≤ 2×10^7`, bucketed by
`r`: mean `r'` is `2.0000` in **every** bucket, `r = 1 … 20`.  Aggregate
consumption `1.9999992` against creation `1.9999965` — indistinguishable.  So the
inequality does not go the required way, and per-bucket its sign depends on `r`.

The decisive part is the control.  Run identically on `expStep n = 3n/2` (even),
`(3n+1)/2` (odd) — which agrees with `T` on odd inputs and **diverges from every
start** — the same statistic gives `1.9999926`, matching bucket by bucket.  A
capacity argument built on `v₂(n+1)` cannot separate `T` from a map that always
diverges, so it can prove nothing about divergence.

### Track 2 — 2-adic repulsion from `−1`.  Refuted numerically.

Claim: growth is always repaid with interest.  **False.**  Over all `99 999`
excursions from odd `n < 200 000` (one full odd run plus the forced even run,
exact rationals): `28.6 %` have net factor `> 1`, none exactly `1`, `71.4 %`
below.  The largest is `492.6`, at `n = 131 071` with `r = 17`, `s = 1`; factors
grow like `(3/2)^r/2` in the common `s = 1` case and `r` is unbounded, so
per-excursion factors are **unbounded above**.  No global per-excursion repulsion
theorem of that shape exists.  Independently reproduced here.

### Track 3 — which infinite words are positive integers.  Falsified, correctly.

The characterisation is exact: a word is a positive integer iff its nested
realisers `x_k ∈ [0, 2^k)` are eventually constant.  Periodic high-density words
all give `B/(2^L − 3^a)`, negative when density exceeds `log₃ 2` — including the
genuine shadow integers `−1` and `−4`.  That is the cycle equation restated.

For **aperiodic** high-density words — the case that matters, measured nested as
it must be, one fixed stream extended to `k = 3200` at densities `0.6309, 0.65,
0.7, 0.8, 0.9` — `x_k/2^k` wanders over the whole of `(0,1)` with no drift toward
either end, and the leading-bit agreement never exceeds about `4` digits.  Nothing
locks in.  **Asymptotic odd density is not by itself an obstruction to landing in
`ℕ`.**  This falsifies the hypothesis using the correct nested measurement, not
the flawed non-nested one flagged earlier.

### What the three deaths agree on: `Strategy/CoordinateMismatch`

* **`odd_clean`** — the odd step is exact in `u = n + 1`: `u ↦ 3u/2`.
* **`even_clean`** — the even step is exact in `n`: `n ↦ n/2`.
* **`even_ceil`** — and in `u` the even step is a *ceiling*, `u ↦ ⌈u/2⌉`.

The growth is clean in one coordinate, the contraction in the other.  Asking for a
single affine shift `v = n + c` that cleans both gives `1 + 2c = 3c` from the odd
branch and `2c = c` from the even one: `c = 1` against `c = 0`.  **`no_common_shift`
is that contradiction.**

So the `+1` is not a nuisance term awaiting a better change of variable — among
affine shifts there provably is none.  And that is exactly why this wave died:
`expStep` shares `T`'s odd-run law in `u` *exactly* (`expStep_eq_on_odd`), and
grows at every step (`expStep_grows`), so every device reading only the
`u`-coordinate odd-run structure — the `u ↦ 3u/2` lockstep, the `v₂(u)` ledger,
carry-capacity accounting — is satisfied by a map that diverges everywhere.

The discriminating fact is the one thing the two maps do not share: **`T`'s even
branch divides `n`, the coordinate in which the growth law is not clean.**  This
sharpens the old requirement "a proof must use that even steps divide" into
something usable: it must use that they divide *the other coordinate*, and pay the
ceiling in between.

### Axiom footprint

`lake build Collatz` succeeds, **280 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round XLVI — the exchange law, and a correction to Round XXXVIII

One approach this round, chosen for the one structural fact the session had
actually proved: `CoordinateMismatch` showed the odd branch is exact in
`u = n + 1` and that no affine shift makes both branches exact.  So: follow the
odd branch in `u`, and ask not what decreases but what is **conserved**.

### The correction

Round XXXVIII recorded, and every round since has repeated, that *the `2`-adic
and `3`-adic pictures never interact, because `3n+1 ≡ 1 (mod 3)` always, so
`v₃(3n+1) = 0` unconditionally*.  That is true, and it is a fact about `n`.

**It is false in the coordinate where the growth law is clean.**  The odd branch
is `u ↦ 3u/2`.  It multiplies by `3` and divides by `2`, so along it

* `v₂(u)` drops by **exactly one**,
* `v₃(u)` rises by **exactly one**,
* and therefore **`Φ = v₂(n+1) + v₃(n+1)` is invariant under every growth step.**

The `+1` that destroys `3`-adic information in `n` is exactly what creates it in
`n + 1`.  Measured: zero exceptions across every growth step of every odd
`n < 300 000`; `Φ` changes at `115 000` of the `150 000` contraction steps in the
same range; `v₃(n+1)` at a growth step is distributed `2/3, 2/9, 2/27, …`.

### `Strategy/ValuationExchange`

Formalised without defining any valuation, by carrying the decomposition instead.

**`exchange_orbit : k ≤ i → T^k(2^i · 3^j · m − 1) = 2^(i−k) · 3^(j+k) · m − 1`**

— the same `m` throughout, `k` factors of `2` traded for `k` factors of `3`, with
the conserved budget visible in the exponents: `(i−k) + (j+k) = i + j`
(`budget_constant`).  `exchange_step` is the single-step form,
`DensitySaturation.orbit_pow_pred` the case `j = 0, m = 1`.

Checked non-vacuous in the kernel: at `i = 4, j = 2, m = 5` the orbit of `719` is
`719, 1079, 1619, 2429, 3644`, and both sides agree at every `k`.

Dynamically: `i = v₂(u)` is Terras' run length, the growth steps *remaining*;
`j = v₃(u)` is the number *banked*.  A growth run is a transfer of `i` units from
the `2`-adic account to the `3`-adic one, halting exactly when the `2`-adic
account empties.  The budget is fixed for the run and moves only at a contraction.

### What it does not do

`Φ` alone proves nothing, and it fails all three filters, for one reason:

* **F1** — `expStep` has the *same* growth branch in `u`, so `Φ` is conserved for
  it too, and `expStep` diverges from every start.
* **F2** — the mirror `3n−1` has the same law in `u = n − 1`.
* **F3** — the law is purely multiplicative; the order of `ℤ` never enters.

That is the ordinary obstruction of this development, in its sharpest form: the
conserved quantity belongs to the growth branch, and every filter model shares
the growth branch.  A device that separates them has to live at the contraction,
which is where `Φ` is unconstrained and where — by `CoordinateMismatch` — the
clean coordinate is `n`, not `u`.

### Axiom footprint

`lake build Collatz` succeeds, **281 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round XLVII — the contraction product, and positivity in one line

Round XLVI ended by locating the target: the growth branch is shared by `T`, by
the mirror `3n−1`, and by `expStep`, so nothing built on it can separate them, and
whatever does must live at the **contraction**.  This round went there.

### The three maps differ only at the contraction

In `u = n + 1`:

| map | growth (`u` even) | contraction (`u` odd) |
|---|---|---|
| `T` | `u ↦ 3u/2` | `u ↦ (u+1)/2` — **ceiling** |
| mirror `3n−1` | `u ↦ 3u/2` | `u ↦ (u−1)/2` — **floor** |
| `expStep` | `u ↦ 3u/2` | `u ↦ (3u−1)/2` |

Identical growth, three different contractions.  That is the whole content, and it
explains every failure of the last several rounds in one table.

### `Strategy/ContractionProduct`

Growth multiplies `u` by `3/2`; contraction multiplies it by `(u+1)/(2u)`.
Telescoping a segment of length `L` with `a` growth steps gives, with both products
over **contraction** steps only:

**`contraction_product : (T^L(n) + 1) · 2^L · Π uᵢ = (n + 1) · 3^a · Π (uᵢ + 1)`**

and on a cycle the outer factors cancel (`cycle_product`):

**`2^L · Π uᵢ = 3^a · Π (uᵢ + 1)`, i.e. `Π (1 + 1/uᵢ) = 2^L / 3^a`.**

Kernel-checked non-vacuous: both sides agree at every segment length `0…5` from
`n = 7, 27, 703`, and the trivial cycle gives `12 = 12`.

### Positivity, exactly located

Every factor of the product is `1 + 1/uᵢ`.  Hence

* all `uᵢ > 0` — a **positive** cycle — every factor `> 1`, so **`2^L > 3^a`**;
* all `uᵢ < 0` — a **negative** cycle — every factor `< 1`, so **`2^L < 3^a`**.

Filter F2/F3 — "a proof must use the order of `ℤ`" — is that one line.  The sign of
`n` *is* the direction of the inequality between `2^L` and `3^a`; nothing else in
the identity knows about order.  Checked against every cycle `T` actually has on
`ℤ`, with the identity holding on all of them and the inequality flipping exactly
with the sign:

| cycle | `L` | `a` | ratio | `2^L > 3^a` |
|---|---|---|---|---|
| `1 → 2 → 1` | `2` | `1` | `1` | `4 > 3` ✓ |
| `−5 → −7 → −10 → −5` | `3` | `2` | `1` | `8 < 9` ✗ |
| `−17` cycle | `11` | `7` | `1` | `2048 < 2187` ✗ |

The cycle `n = −1` is the single exception to the cancelled form, for an honest
reason: there `u = 0`, the fixed point of `u ↦ 3u/2`, so the outer factors cannot
be divided out.

### It does not prove the conjecture, and cannot

Bounding the positive case:
`0 < L log 2 − a log 3 ≤ e · log(1 + 1/(M+1)) < e/(M+1)`, so
`M + 1 < e / (L log 2 − a log 3)` — an upper bound on the cycle minimum.  Excluding
cycles needs that below the verified range for *every* admissible `(L, a)`, and at
the semiconvergents of `log₂ 3` the denominator is arbitrarily small while `e`
grows.  Round XLIV computed the rate: the required range is
`≈ a_k · a_{k+1} / (6 ln 2)`, which diverges.  So this identity — the sharp form of
the product bound, not a weakening — inherits the same ceiling, and **no finite
verified range closes it**.

What the round adds is placement, not power: the one hypothesis every filter calls
indispensable now sits on a single visible factor.

### Axiom footprint

`lake build Collatz` succeeds, **282 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round XLVIII — forward growth and backward branching are one phenomenon

A device, invented from the one genuinely new structure the session produced, and
then measured until it gave up its limits.

### The identification

Two things in this development were built independently and are the same object.

**Forward** (`ValuationExchange`, Round XLVI): the growth branch is exactly
`u ↦ 3u/2` in `u = n + 1`, so `v₃(u)` rises by exactly one per growth step.

**Backward**: a point `m` has preimages `2m` always, and an odd one `(2m−1)/3`
exactly when `3 ∣ 2m − 1`, i.e. `m ≡ 2 (mod 3)`, i.e. **`3 ∣ m + 1`**.

Same condition.  `has_odd_preimage_iff`:

**`(∃ x odd, T x = m) ⟺ (m + 1) % 3 = 0`** for `0 < m`.

So the branching of the inverse tree is governed by precisely the quantity the
forward growth dynamics increments.  With `exchange_orbit` this gives
`growth_run_branches`: **after `k ≥ 1` steps of a growth run every point has an odd
preimage**, since the value is `2^(i−k)·3^(j+k)·m − 1` with `j + k ≥ 1`.  A growth
run of length `r` produces `r` consecutive branching nodes.

The `+1` that makes `v₃(n)` useless is the same `+1` that makes the tree branch.
Forward growth and backward branching are one phenomenon read in two directions.

Verified in the kernel: for `m = 1 … 12`, "`3 ∣ m+1`" and "the odd preimage really
steps to `m`" agree in every case, true exactly at `m = 2, 5, 8, 11`.
Axioms `propext`, `Quot.sound`.

### And then the measurement that bounds it

The obvious hope: this correlation shifts the density of branching nodes away from
the naive `1/3`, changing the tree's growth rate and reviving the inverse-tree
counting route.

**It does not.**  Breadth-first from `1` over `363 020` tree nodes: `121 006`
branch — density `0.33333`, the naive value to five places.

The correlation is real but **local**.  It holds along each growth run and is reset
at every contraction, and the resets wash it out globally.  The counting route,
already dead, stays dead; this does not revive it.

That is the honest shape of the result: an exact structural identification, not a
statistical one, which tells any future forward/backward argument where to look —
the odd preimage exists precisely where the forward dynamics has banked a factor of
three — while closing off the one quantitative use that suggested itself.

### Axiom footprint

`lake build Collatz` succeeds, **283 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round XLIX — the return map, derived from first principles

Not assembled from earlier machinery.  Reduce the map to its irreducible form,
then invert it, and the two halves of the development turn out to be one ladder.

### The reduction

Write `u = n + 1 = 2^a · w`, `w` odd.  The two branches are exactly `u ↦ 3u/2`
(even) and `u ↦ ⌈u/2⌉` (odd), so in the coordinates `(a, w)`:

* growth (`a ≥ 1`): `(a, w) ↦ (a − 1, 3w)` — count `a` down, triple the odd part;
* contraction (`a = 0`): refactor `w + 1`.

Nothing is discarded — that is the whole map.  Collapsing a maximal growth run
gives a **return map on odd values alone**, in closed form:

**`R(u) = 3^(a−1) · w`,  `u + 1 = 2^a · w`, `w` odd.**

`return_map` states it valuation-free: for odd `w`,
**`T^(k+1)(2^(k+1)·w − 2) = 3^k·w − 1`** — one contraction, then the `k` growth
steps it releases, which is `exchange_orbit` at `i = k`, `j = 0`, `m = w`.

### Inverting it

The `R`-preimages of odd `v` are the `u = 2^a·w − 1` with `3^(a−1)·w = v`.  Since
`v` is odd, `w = v/3^(a−1)` is odd whenever integral, so preimages are indexed by
exactly the `a ≥ 1` with `3^(a−1) ∣ v`:

**the number of `R`-preimages of `v` is exactly `v₃(v) + 1`,**

and `preimage_chain` gives their shape: consecutive preimages satisfy
`3·(u′ + 1) = 2·(u + 1)` — a geometric chain of ratio `2/3` in `u`.

Verified exhaustively: the count for every odd `v < 4000`, and both identities for
`a ≤ 13`, odd `w < 400`, with no exceptions.  For `v = 3^k` the chain in `u` is
`[2·3^k, 4·3^(k−1), …, 2^(k+1)]`; at `v = 81` that is `162, 108, 72, 48, 32`.
Kernel-checked: `30, 46, 70, 106, 160` all reach `80`.

### The unification

**That chain is `ValuationExchange`'s ladder run backwards.**  Forward growth
trades one `2` for one `3` and conserves `v₂(u) + v₃(u)`.  The inverse tree's
preimage chain trades a `3` back for a `2`, along the same conserved level.  The
branching multiplicity at `v` is `v₃(v) + 1` because that is how many threes are
available to trade back: **the tree is wide exactly where the forward dynamics has
banked.**

Round XLVIII saw the two-fold case of this for `T` (an odd preimage exists iff
`3 ∣ m+1`).  The return map sees the entire chain at once, with multiplicity, and
explains why the multiplicity is a *valuation* rather than a coin flip.

### What it does not do

It does not bound anything.  Mean branching is `E[v₃ + 1] = 3/2`; the return map
contracts by `3^(a−1)/2^a` with `E[a] = 2`, mean factor `3/4` — the classical
heuristic recovered, not improved.  Round XLVIII already measured that the
branching correlation is local, reset at every contraction, and washes out
globally at density `0.33333`.  Nothing here changes that.

### Axiom footprint

`lake build Collatz` succeeds, **284 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round L — Collatz is a base swap perturbed by one

Pushing the Round XLIX reduction to its end point.

### The form

Put `U = n + 2`, even exactly at a contraction, and write `U = 2^a · w` with `w`
odd.  Then the whole map — one contraction plus the growth run it releases — is

**`U ↦ 3^(a−1) · w + 1`.**

Take the `2`-part, replace it by a `3`-part one power smaller, add one.  Verified
faithful for every even `n < 60 000` with no exceptions; `swap_form` derives it in
Lean from `ReturnMap.return_map`.

**So Collatz is the base-swap operator `2^a ↦ 3^(a−1)` perturbed by `+1`.**  The
swap alone is a monoid map and trivial.  The `+1` is the entire problem, and its
role is now exactly visible: `S(U)` is always *odd*, so the swap destroys all
`2`-content, and `+1` is what regenerates it and returns the state to the domain.

### Period one, completely classified

`S(U) + 1 = U` reads `w · (2^a − 3^(a−1)) = 1`, so `w = 1` and
`2^a − 3^(a−1) = 1`.  Since `2^a < 3^(a−1)` for every `a ≥ 3`
(`two_pow_lt_three_pow`, a two-line induction), only `a = 1, 2` survive:

**`fixed_point_iff` — the only fixed points are `U = 2` and `U = 4`,**

that is `n = 0` and the trivial cycle `n = 2`.  A family of exponential Diophantine
equations collapses to an induction.

### The difficulty, located and bounded at `w = 1`

Everything now sits in one quantity: `v₂(3^k · m + 1)` — how much `2`-content
adding one regenerates from an odd number whose `3`-part the swap has just made.
That is a genuine `2`-adic × `3`-adic interaction, in the coordinate where one
exists.

At `m = 1` it is bounded outright.  `3^k % 8 ∈ {1, 3}` (`three_pow_mod_eight`),
hence

**`not_eight_dvd_three_pow_succ` — `8 ∤ 3^k + 1` for every `k`,**

so `v₂(3^k + 1) ≤ 2` always: from `U = 2^a` the next state has `a′ ≤ 2`, where
`3^(a′−1) < 2^(a′)`, so it contracts.  The pure powers of two can never launch a
growth run.

For general `m` the bound fails and the structure reappears as a congruence.
Measured: `v₂(3^k·m + 1) ≥ j` holds exactly on a residue class of `k` modulo
`2^(j−2)` — at `j = 4`, `m = 5` gives `k ≡ 1 (mod 4)`, `m = 7` gives `k ≡ 2
(mod 4)`, `m = 11` is empty.  **Deep regeneration requires the `3`-exponent to lie
in an exponentially thin class.**

### What it does not do

It classifies period one, not period `L`.  The same computation at period `L` puts
`2^E − 3^(E−L)` in the denominator, positive only when
`E/L < log 3 / log(3/2) = 2.7095…`, so `E ≤ ⌊2.7095·L⌋` — finite for each `L`, but
with `C(E−1, L−1)` valuation words to check, and the standing bound already forces
`E ≥ 6809`.  The small-`L` checks this makes available are therefore subsumed.

The regeneration question is not answered.  It is put in its sharpest form:
**how large can `v₂(3^k·m + 1)` be along an actual orbit?**  Every filter model
shares the swap; none shares the way `+1` regenerates.  That is where a separating
argument has to live.

### Axiom footprint

`lake build Collatz` succeeds, **285 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LI — the discrete-logarithm coordinate

One approach, aimed at the eleven-symbol question Round L left: *how large can
`v₂(3^k·m + 1)` be along an orbit?*  Change coordinates on it.

### The coordinate

`3` generates the cyclic part of `(ℤ/2^j)*`, which has index `2`, and `−1` is not
a power of `3` — powers of `3` are `1, 3` mod `8`.  So **every odd `w` is uniquely
`ε · 3^t`**, `ε ∈ {±1}`, `t ∈ ℤ₂`, with

`ε(w) = +1 ⟺ w ≡ 1, 3 (mod 8)`,  `ε(w) = −1 ⟺ w ≡ 5, 7 (mod 8)`.

In this coordinate the swap `w ↦ 3^(a−1)·w` of Round L is the **translation
`t ↦ t + (a−1)`**.  All the `3`-multiplication becomes addition.

### The law

With `s = t + a − 1`, lifting the exponent gives the regeneration exactly:

| `ε(w)` | `s` odd | `s` even |
|---|---|---|
| `+1` | `2` | `1` |
| `−1` | `1` | `2 + v₂(s)` |

Verified against exact arithmetic on `4000` random `(w, a)`, `w < 2^20`, `a ≤ 13`,
using a genuine `2`-adic discrete log to `2^64`: **4000 agree, 0 disagree.**  The
supporting identities, checked for `s < 3000`: `v₂(3^s − 1) = 1` (odd `s`),
`2 + v₂(s)` (even `s`); `v₂(3^s + 1) = 2` (odd `s`), `1` (even `s`).

**So the `+1`-regeneration question becomes `v₂` of a linear form in the
logarithm.**  The valuation sequence of an orbit is generated by
`a′ = 2 + v₂(t + a − 1)` with `t` translating by `a − 1` each step.  What the
original coordinates hide, this one displays as the divisibility of a running
linear expression.

(My first attempt at this law was wrong — I wrote `2 + v₂(s)` for the whole `ε=−1`
branch and the test returned `2240` agree against `760` disagree, every failure
having `s` odd.  The parity split is what LTE actually gives.)

### Formalised

The half needing no logarithm is the half that bites:

* `three_pow_two_mul`, `three_pow_mod_eight_even/odd` — `3^s ≡ 1` or `3 (mod 8)` by
  the parity of `s`, which is exactly the statement `−1 ∉ ⟨3⟩`.
* **`growth_blocked`** — if `w ≡ 1` or `3 (mod 8)` then `8 ∤ 3^k·w + 1`, for every
  `k`.  Regeneration is capped at two units.
* **`contracts_of_odd_part`** — so a state `U = 2^a·w` with `w ≡ 1, 3 (mod 8)` has
  next valuation `≤ 2`, and `swap_contracts_below_three` gives `3^(a′−1) < 2^(a′)`
  there.

**Half of all odd parts cannot launch a growth run.**  Growth requires `ε = −1`.
Kernel-checked: `w = 1, 3, 9, 11` never reach `0 mod 8`; `w = 5, 7, 13, 15` do.
Round L's `not_eight_dvd_three_pow_succ` is the case `w = 1`.

### What is not proved

The `ε = −1` branch, which is now where all the difficulty sits.  There the depth
is `2 + v₂(s)`, so a long growth run demands `s = t + a − 1` divisible by a high
power of `2` — an exponentially thin condition on the running logarithm.  Whether
an orbit can keep meeting it *is* the conjecture.  Nothing here bounds `v₂(s)`, and
the recursion is self-referential: `a` depends on `t` through the very valuation
being asked about.

The `2`-adic logarithm is not formalised — it needs the structure of `(ℤ/2^j)*`,
absent from this Mathlib-free development.  The congruences are what survives
without it.

### Axiom footprint

`lake build Collatz` succeeds, **286 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LII — the limitation, assessed; and the device it calls for

Round LI ended by saying the recursion is self-referential.  This round finds out
what that actually costs, and builds the tool matched to the answer.

### Everything collapses onto one function

Chasing what the log-coordinate `t` becomes after a step: the new odd part is
`3^s − 1` defactored, so the whole dynamics is governed by

**`Λ(s) = dlog₃(oddpart(3^s − 1))`.**

That one function is the conjecture.  So: is `Λ` structured?

### Four measurements, with a `2`-adic discrete log to `2^44`

* **Exactly multiplicatively self-similar.**  `3^(2s) − 1 = (3^s − 1)(3^s + 1)` and
  `dlog` is additive, so **`Λ(2s) = Λ(s) + Ψ(s)`**, `Ψ(s) = dlog₃(oddpart(3^s+1))`.
  Verified for all `s < 60`, no exceptions.
* **Additively opaque.**  `Λ(s+1) − Λ(s)` takes `24` distinct values in `24`
  consecutive samples.  No pattern.
* **Not `2`-adically continuous.**  `Λ mod 2^4` is determined by `s mod 2^k` for no
  `k ≤ 15`, and the Mahler coefficients do not decay — valuations
  `0, 2, 6, 0, 1, 0, 3, 0, 1, 2, 3, …`, no growth.  By Mahler's theorem that rules
  out continuity, hence **every `p`-adic analytic method at once**.
* **But Lipschitz on each stratum.**  Restricted to `{s : v₂(s) = j}`, `Λ mod 2^n`
  *is* determined by `s mod 2^(n+j+c)` — measured `c = 1` at `j = 0`, `c = 2` at
  `j = 1, 2`, across `n = 4, 6, 8`.

### The assessment

**The discontinuity is caused by the defactoring.**  `3^s − 1` must be divided by
`2^(2+v₂(s))`, an exponent that jumps with `v₂(s)`, and division by `2^k` is not
continuous in `k`.  So the step that makes `Λ` immune to analysis is *the even
branch dividing* — filter F1, recurring one level up, in the log coordinate.

And then the barrier, in one sentence:

> `Λ` is regular exactly on the strata of the `v₂`-filtration, and the recursion
> `a′ = 2 + v₂(s)` moves the orbit **between** strata at every step.  The dynamics
> is transverse to the stratification on which the object is regular.

That is why the multiplicative self-similarity cannot be iterated — the dynamics is
additive in `s` — and why the stratum-wise regularity cannot be composed —
consecutive steps lie in different strata.  Two exact structures, neither usable,
for the same reason.

### `Strategy/LiftingLaw`

The arithmetic engine underneath, formalised:

* `three_pow_succ_even` / `three_pow_succ_odd` — `3^k + 1` is `2·odd` for even `k`,
  `4·odd` for odd `k`.
* `three_pow_sub_one_odd` — `3^q − 1 = 2·odd` for odd `q`.
* **`three_pow_sub_one_factor`** — for odd `q` and `j ≥ 1`,
  `3^(2^j·q) − 1 = 2^(j+2)·odd`.

That is lifting the exponent at `p = 2` without a valuation function:
`v₂(3^s − 1) = 2 + v₂(s)` for even `s`, `1` for odd `s`.  The induction is the
factorisation `3^(2m) − 1 = (3^m−1)(3^m+1)` plus the mod-`8` congruences of
Round LI.  This single law produces the depth formula `a′ = 2 + v₂(s)`, the
stratification, *and* the discontinuity.

Kernel-checked sharp: `3^(2^j·q) − 1` is divisible by `2^(j+2)` and not by
`2^(j+3)`, at `(j,q) = (1,1), (2,1), (3,1), (1,3), (2,5), (4,7)`.

### Devices tried and their verdicts

* **Mahler expansion** (the canonical basis for functions on `ℤ₂`) — *refuted*:
  coefficients do not decay, so `Λ` is not continuous and has no Mahler series.
* **Stratified `2`-adic analysis** — *works, but does not compose*: `Λ` is Lipschitz
  on each `v₂`-stratum with an explicit, measured modulus, and the dynamics leaves
  the stratum immediately.
* **The multiplicative functional equation** — *exact, but not iterable*: it relates
  `Λ(2s)` to `Λ(s)`, while the dynamics moves `s` additively.

### Axiom footprint

`lake build Collatz` succeeds, **287 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LIII — the tower converges, on the axis the dynamics does not use

Targeting the recurrence Round LII named.

### The recurrence, exactly

* **Level 0** — branches `n` and `n + 1`; `no_common_shift` says no affine shift
  serves both.
* **Level 1** — in the logarithm the branches are `3^s − 1` and `3^s + 1`.
  **The same `±1` defect, reproduced around a new object by the log transform.**

The obstruction is self-similar.  But level 1 has what level 0 lacks: its branches
satisfy an exact identity, since `3^(2s) − 1 = (3^s−1)(3^s+1)` and `dlog` is
additive —

**`Λ(2s) = Λ(s) + Ψ(s)`.**

A renormalization equation.  Does it converge?

### It does, at an exact rate

`three_pow_succ_factor` — for odd `q`, `j ≥ 1`,
**`3^(2^j·q) + 1 = 2·(2^(j+1)·A + 1)`** with the *same* odd `A` from
`three_pow_sub_one_factor`.  A one-line corollary — add `2` to the lifting law —
but it is the engine.  It gives `oddpart(3^(2^j q)+1) = 1 + 2^(j+1)A`, and since
`3^t ≡ 1 + 2^(v₂(t)+2)` to the next power, that element's logarithm has `v₂`
exactly `j − 1`.  Hence

**`v₂(Ψ(2^k·s)) = k − 1` for every `k ≥ 1`, independently of `s`.**

Measured for odd `s ≤ 25`, `k ≤ 7`: no exceptions.  So the increments tend to zero
`2`-adically at an explicit rate, and

**`Λ_∞(s) = lim_k Λ(2^k·s) = Λ(s) + Σ_{k≥0} Ψ(2^k·s)` exists.**

Observed: at `s = 1` the values settle from below, agreeing to `17 (mod 64)` from
`k = 7`.  `branches_share_factor` records that one factorisation supplies both
branches — the relation level 0 does not have.

### The assessment

A genuine new object with an exact rate, and **it does not help**, for the reason
Round LII identified: it lives on the transverse axis.

The tower runs in the direction `s ↦ 2s`.  The Collatz recursion moves `s`
*additively*, by `a − 1`.  A tower converging under doubling says nothing about a
trajectory that translates — and the translation direction was measured
structureless: `Λ(s+1) − Λ(s)` gives `24` distinct values in `24` samples.

So the position is sharp rather than vague.  There are now **two exact structures**
on `Λ` — multiplicative self-similarity with a convergent tower, and stratum-wise
Lipschitz regularity — and the dynamics is transverse to **both**.  One statement,
not two failures, and the same statement at level 0 and level 1.  Whatever settles
Collatz must move along the additive direction, where every measurement so far
shows nothing.

### Axiom footprint

`lake build Collatz` succeeds, **288 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LIV — the contraction harvest: device dead, differing term extracted

Built to specification: a `V` changing only on contraction steps, not a rewrite of
`affineC`, tested against all three filter maps before being believed.  The test
killed it.  The term at which the maps differ survives, and is proved.

### The device

All three maps share growth `u ↦ 3u/2` and differ only at the contraction —
`⌈u/2⌉` for `T`, `⌊u/2⌋` for the mirror `3n−1`, `(3u−1)/2` for `expStep`.  So

`V_C(n) = Σ` over the first `C` contractions of the `2`-adic content that map's
contraction harvests: `v₂(n+2)`, `v₂(n−2)`, `v₂(3n+2)` respectively.

Constant on growth by construction; a sum of *valuations*, not a weighted sum of
powers of two, so not `affineC` in disguise.

### Dead, by its own test

Every odd `n < 50 000`, first `10` contractions:

* **Marginals identical** — all three give `0.500, 0.250, 0.125, 0.0625, 0.031,
  0.015`, geometric `(1/2)` to four decimals.
* **Joint law identical** — consecutive pairs agree to three decimals and match the
  independent product: `P(1,1) = 0.24975, 0.25098, 0.24973` against `0.25`.

`V` has the same law under a map with the wrong sign and under a map that diverges
from every start.  Summing over an orbit averages the difference away.

### The exact differing term

The maps do differ pointwise, exactly.  For even `n = 2m`:

**`T` harvests `1 + v₂(m+1)`; the mirror harvests `1 + v₂(m−1)`.**

Verified for all even `n < 20 000`.  So the difference between Collatz and its
mirror, at the one place they differ at all, is `v₂(m+1)` against `v₂(m−1)` — **the
same `±1` defect, one level further down.**  The recurrence, a third time.

Which branch is shallow is decided by `m` mod `4`, exactly (`harvest_split`,
`harvest_exclusive`):

* `m` even — both `m ± 1` odd, both harvests `1`: **the maps agree**;
* `m ≡ 1 (mod 4)` — `m+1 ≡ 2 (mod 4)`, `4 ∣ m−1`: `T` shallow, mirror deep;
* `m ≡ 3 (mod 4)` — `4 ∣ m+1`, `m−1 ≡ 2 (mod 4)`: `T` deep, mirror shallow.

### Why this is worth more than the device

The trichotomy *explains* the statistical agreement.  The cases `m ≡ 1` and
`m ≡ 3` occur equally often and **exchange the roles of the two maps**, so every
symmetric functional of the harvest — marginal, joint law, sum — is blind to the
sign of the defect.

**A separator must be antisymmetric in `m mod 4`.**  That rules out `V` and every
symmetric statistic built from the harvest at once, which is a stronger conclusion
than the single failure, and it is a testable condition for the next candidate.

### Axiom footprint

`lake build Collatz` succeeds, **289 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LV — a relation that survives the `n ↦ n + 2^M` test

Built to specification: mention both `v₂(n+1)` and the archimedean size of `n` in
one relation, at a contraction, and pass the test that killed the previous devices.

### The test

`n` and `n + 2^M` share their first `M` parity bits
(`parityVector_mod_pow_two`).  So every function of the parity word alone, and
every function of `u = n+1` modulo a high power of two, is blind to the difference.
That is what makes a device `2`-adic only, and dead.

### The relation that passes

**`perturb_orbit` — `T^j(n + 2^M) = T^j(n) + 3^(a_j)·2^(M−j)` for `j ≤ M`**, with
`a_j = oddCount n j`.  Proved by induction, no appeal to `affineC`: for `j < M` the
offset is even, so the two orbits keep the *same parity at every step* — which is
why the words agree — and the offset is halved on an even step, tripled on an odd
one (`step_shift_even`, `step_shift_odd`).

Cleared of division, `perturb_scaled`:

**`2^j · T^j(n + 2^M) = 2^j · T^j(n) + 2^M · 3^(a_j)`.**

The `2`-adic datum `a_j` — identical for the two starting points — and the
archimedean `2^M`, in one exact identity.  **It is not invariant under
`n ↦ n + 2^M`**: the sides differ by exactly `2^M·3^(a_j)`, never zero.  The device
sees precisely what the parity word cannot.

Kernel-checked at `n = 27`, `M = 8`: the parity words of `27` and `283` agree at
every `j ≤ 5`, while the orbit values differ by `256, 384, 576, 288, 432, 648` —
exactly `3^(a_j)·2^(8−j)`.

The consequence: the scaled deficit `D_j(n) = 2^j(n − T^j(n))` satisfies
`D_j(n+2^M) − D_j(n) = 2^M(2^j − 3^(a_j))`, verified for `M ≤ 12`, `n < 400`,
`j ≤ M`.  **The `2`-adic data fixes the sign of the shift — the heavy/light
dichotomy `2^j` against `3^(a_j)` — and the size fixes its magnitude.**

### The target shape

`v₂(n+1) = 1` is exactly `n ≡ 1 (mod 4)`; by Terras the odd run has length one, so
a growth step is followed immediately by a contraction, and the pair composes:

**`drop_of_v2_one` — `n ≡ 1 (mod 4) → 4·T²(n) = 3n + 1`,**

hence `T²(n) < n` for every `n > 1`, with `n − T²(n) = (n−1)/4`.  The drop is
**proportional to `n`, not bounded** — that proportionality is the archimedean
content.  A shallow run does not merely fail to grow; it loses a fixed *fraction*
of the size.  Verified for every odd `n < 40 000` with `v₂(n+1) = 1`, no exceptions,
and kernel-checked at `n = 5, 9, 13, 17, 21, 25`.

### What it does not do

It does not iterate.  `drop_of_v2_one` fires only on `n ≡ 1 (mod 4)` — half of odd
`n`; the rest have longer runs and can grow, and `no_uniform_block` already proves
no bounded block descends for every `n`.  And `perturb_orbit` relates two starts
with the same word; it says nothing about a single orbit whose word is not given.

What is new: the first relation in this development in which the `2`-adic and
archimedean data appear together and neither can be eliminated — the sign from one,
the magnitude from the other.

### Axiom footprint

`lake build Collatz` succeeds, **290 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LVI — the banked three and the next harvest are independent, provably

A local, non-density coupling was sought: along one forward orbit, does the next
contraction's harvest correlate with the `v₃` the last growth run banked?

### A correction to the question

At the end of a growth run of length `r = v₂(n+1)` every factor of two is spent, so
`T^r(n) + 1 = 3^r·w` is **odd** and `v₂(T^r(n)+1) = 0` identically — checked for
every odd `n < 200 000`.  The live quantity, the one that sets the next run length,
is the harvest `v₂(T^r(n) + 2) = v₂(3^r·w + 1)`.  That is what was tabulated.

### The exact contingency table

`A = v₃(n+1)` against `B = v₂(3^r·w + 1)`, all odd `n < 2^20`, `524 288` samples:

| `A \ B` | `1` | `2` | `3` | `4` | `P(A)` |
|---|---|---|---|---|---|
| `0` | `0.33333` | `0.16667` | `0.08333` | `0.04167` | `0.66667` |
| `1` | `0.11111` | `0.05555` | `0.02778` | `0.01389` | `0.22222` |
| `2` | `0.03704` | `0.01852` | `0.00926` | `0.00463` | `0.07407` |
| `3` | `0.01235` | `0.00617` | `0.00309` | `0.00154` | `0.02469` |
| `P(B)` | `0.50000` | `0.25000` | `0.12500` | `0.06250` | |

Marginals exactly geometric, `P(A=a) = (2/3)·3^(−a)` and `P(B=b) = 2^(−b)`, and
every cell is their product: maximum relative deviation `0.00266`, `χ² = 0.01` on
`16` cells.

**The table factors.  The coupling is local and dead.**

### Why it must factor — and this is the part worth keeping

Not an accident of sampling.  With `n + 1 = 2^r·w`, `w` odd:

* `A = v₃(w)` is a function of `w` modulo a power of **three**;
* `B` is, by `LogCoordinate`, a function of `r` and `w` modulo a power of **two** —
  the discrete logarithm and the sign `ε(w)`, which is `w mod 8`.

Powers of two and three are coprime, so by CRT every combination of `w mod 2^j` and
`w mod 3^k` occurs equally often.  **No orbit structure can correlate them, because
there is no arithmetic through which one could constrain the other.**
`CouplingDead.two_pow_dvd_three_pow_iff` is that coprimality in usable form: a power
of two divides a power of three only when it is `1`.

### Consequence

The banked `v₃` cannot force a drop, and no refinement of this pairing will — the
obstruction is not a weak correlation but an *arithmetically absent* one.  A local
coupling must pair quantities living at the **same prime**.  That is exactly why
`SizePerturbation` (Round LV) survives where this dies: there the two coordinates
are `2`-adic and archimedean, not `2`-adic and `3`-adic.

### Axiom footprint

`lake build Collatz` succeeds, **291 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LVII — heights cannot see the ghosts, and why, exactly

Asked: is there an archimedean height, house, or house-of-conjugates inequality
that `n_σ = C(σ)/(2^E − 3^L) ∈ ℕ` would violate for expanding words?

**No.  The mechanism is named below and the route is closed.**

### The house branch closes in one line

`n_σ` is a **rational** number — degree `1` over `ℚ`, with **no nontrivial Galois
conjugates**.  So `house(n_σ) = |n_σ|`, and every conjugate inequality is an
identity.  Lehmer, Dobrowolski, Schinzel–Zassenhaus, Bogomolov–Zhang all need
degree `≥ 2`, or bound height away from zero for non-torsion points of bounded
degree; at degree `1` each is vacuous or saturated.  There is nothing for conjugate
geometry to act on.

### The height branch, and the exact gcd mechanism

With `G = |2^E − 3^L|`, the naive floor is `H(n_σ) ≥ G`.  After reduction,
`H(n_σ) = max(|C|, G)/gcd(C, G)`, so the floor survives only while the gcd is
small.  It is not:

> **`n_σ ∈ ℤ  ⟺  gcd(C, G) = G`.**

Verified exactly over all `131 070` words with `L ≤ 16`, no exceptions
(`integrality_iff_max_gcd`).

**This is fatal in the sharpest possible way.**  The hypothesis one wants to
refute — that the ghost is an integer — *is precisely the case of maximal gcd
collapse*, where the denominator cancels completely and the floor `G` vanishes.  A
height inequality with a floor at `G` is vacuous exactly on the set it must
exclude.  The bound is not weak; **integrality is the definition of its failure.**

Measured, exhaustive by length: `9.5 %` of words at `L = 10` and `11.7 %` at
`L = 16` already have `H < G`, and the largest cancellation at `L = 16` is
`gcd = 42 981 185`, absorbing essentially all of `G`.

The extremal ghost makes it concrete: the all-ones word has `C = −G` for **every**
`L` — `(C, G) = (1,1), (5,5), (19,19), (65,65), (211,211), (665,665), (2059,2059),
(6305,6305)` — so the gcd is maximal at every length and `n_σ = −1` exactly.  A
genuine ghost, saturating the collapse at every scale, at height `0`.

### What survives

Nothing on this route.  The positive-integer ghosts at `L ≤ 16` are exactly
`(L,a) = (2,1), (4,2), (6,3), (8,4)` with `n ∈ {1,2}` — the trivial cycle and its
repetitions, as it must be.  No height statement separates them from the negative
ghost `−1`: both are degree-`1` points whose denominators have cancelled.

`reduced_denominator_one` records the endpoint: in the integral case the reduced
denominator is `1`.

**Naming the mechanism and stopping, as instructed:** *integrality is maximal gcd
collapse, and maximal gcd collapse is exactly where every archimedean height floor
becomes vacuous.*

### Axiom footprint

`lake build Collatz` succeeds, **292 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LVIII — the max-side product bound, the missing half of the sandwich

### Selection, against the four sources

* **Hercher 2023, Lemma 9** — already formalised (`HercherMerge.merge`), with
  Remark 10 as `unbounded_descends`.  Not a gap.
* **Halbeisen–Hungerbühler 1997** — Lemma 5 was the gap and is now proved
  (`HHLemmaFive.hhExtremal_holds`).  Not a gap.
* **collatz-lab.org** — `BakerSeparation` is stated there as a *conjecture de
  travail*, an undemonstrated strengthening of Rhin/Wu/Salikhov carried as an
  axiom: formalising it means **adding an axiom**, forbidden here.  Its `δ8` note is
  an *obstruction* result — no Baker + CF + Khinchin derivation gives a uniform
  `F(k) < 2^71` — so it closes a route rather than moving a bound.  Neither
  qualifies.
* **The cycle-ratio theorem** (T. I. Martiny, *New Lower Bound on Cycle Length for
  the 3n+1 Problem*, Univ. of Pittsburgh, 9 Apr 2015, slide 9): for a cycle `Ω` with
  odd part `Ω₁`,
  `log₂(3 + M⁻¹) < |Ω|/|Ω₁| ≤ log₂(3 + m⁻¹)`, `M = max Ω`, `m = min Ω`.
  **Its lower half is the gap.**

Clearing denominators with `L = |Ω|`, `a = |Ω₁|`:

`(3M+1)^a ≤ 2^L · M^a`  and  `2^L · m^a ≤ (3m+1)^a`.

The right inequality *is* `CycleProduct.product_invariant` at a cycle — the source
of every `CycleLength` result here.  The left one, governed by the cycle
**maximum**, was absent.

### `Strategy/ProductMax`

**`product_invariant_max` — `(3M+1)^(a_k)·x ≤ 2^k·M^(a_k)·T^k(x)`** whenever
`T^i(x) ≤ M` for all `i`.  Dual to `product_invariant`: that one bounds the orbit
above from a *lower* bound on its values, this bounds it below from an *upper*
bound.  The step is one line: at an odd `y ≤ M`, `(3M+1)·y ≤ M·(3y+1)`, since
`3My + y ≤ 3My + M`.

**`cycle_max_bound` — `(3M+1)^a ≤ 2^L · M^a`** on a cycle, after cancelling `x`.

Verified: no violation over `155 961` pairs `(x,k)`, `x < 4000`, `k ≤ 39`, strict in
`151 972`.  Kernel-checked on the trivial cycle `{1,2}`: the sandwich is `7 ≤ 8` and
`4 ≤ 4`, the min side exactly tight.

### Why it can move a bound

Every existing exclusion uses only the cycle *minimum*, through the verified range.
This supplies the complementary constraint from the *maximum*, so the admissible
`(L,a)` region is cut from both sides: `log₂(3 + 1/M) < L/a ≤ log₂(3 + 1/m)`.  From
below the development previously had only `L/a > log₂ 3`; since
`log₂(3 + 1/M) > log₂ 3` strictly, this is a genuine strengthening, by an amount
governed by the orbit maximum — which `HercherMerge.orbitMax` already supplies.

It does not by itself raise `6809`: converting it to a number needs an upper bound
on `M` for a hypothetical cycle, which the development lacks.  Recorded in sharp
form, ready for that input.

### Axiom footprint

`lake build Collatz` succeeds, **293 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LIX — the pair `(n, n+1)`, and why no potential can live on it

### The step, corrected

As proposed the two second components were exchanged.  Growth (`x` odd) is the
clean one in `y = u`; contraction (`x` even) is the clean one in `x`.  So

* `x` even:  `(x, y) ↦ (x/2, (y+1)/2)` — the ceiling, in `y`;
* `x` odd:   `(x, y) ↦ ((3x+1)/2, 3y/2)` — the exact tripling, in `y`.

The version with these swapped fails on **every** input: `n = 2` gives `(1,4)`
against the wanted `(1,2)`; `n = 3` gives `(5,2)` against `(5,6)`.  `19 999`
failures out of `19 999`.  With the components in the right slots, none.

`PairStep.pairStep` is the corrected map, `pair_preserves_gap` the check
(`pairStep (x, x+1) = (T x, T x + 1)`), and `pair_orbit` its iterate.
Kernel-checked at `n = 2, 3, 7, 27`.

### The kill test fires by construction

The proposal's own criterion: *if `V(x, x+1)` is secretly `f(x)`, dead.*  It is —
and unavoidably.

The locus `{(x, x+1) : x ∈ ℕ}` is the **graph of a function**.  The second slot is
determined by the first, so the pair carries exactly what `x` carries and not one
bit more.  `pair_potential_is_unary`: for *any* `V : ℕ → ℕ → α` there is an `f` with
`V x (x+1) = f x` — namely `f = fun x => V x (x+1)`.  It depends on **no axioms at
all**.

**So no potential on the pair locus can escape the test, however it is built.**  The
construction cannot fail to be unary; the gap-`1` constraint is what makes it so.
This is a stronger verdict than a failed candidate: it rules out the whole class in
advance, and cheaply.

### What the pair formalism *is* good for

Not a potential — a typing discipline.  Its content is in the step rule, recording
which coordinate is exact at each letter, and that content is already
`CoordinateMismatch`: `odd_clean`, `even_clean`, and `no_common_shift` (no affine
`v = n + c` makes both branches exact, the odd branch forcing `c = 1` and the even
`c = 0`).

The pair carries both coordinates so neither must be chosen; `no_common_shift` is
the theorem that they cannot be merged.  The pair does not add information — it
**displays** the obstruction.  Worth stating, and not a route to a Lyapunov
function.

### Axiom footprint

`lake build Collatz` succeeds, **294 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LX — banked threes against spent twos: the identity is exact and vacuous

Proposal: after a maximal run of length `r = v₂(n+1)`, let
`κ(n) = v₂(n′+1) − v₃(n′+1)` with `n′ = T^r(n)`, and hope for `κ ≤ −1`.

**The dream lemma is true.  It is also vacuous, and both halves are now proved.**

### The exact identity

With `n + 1 = 2^r·w`, `w` odd, `exchange_orbit` gives `n′ + 1 = 3^r·w`
(`run_end_value`).  Since `w` and `3^r` are both odd, that product is odd
(`run_end_odd`), so

**`v₂(n′+1) = 0` identically** — all `524 288` odd `n < 2^20`, no exception.

The run spends *every* two; that is what ends it.  Hence

**`κ(n) = 0 − (r + v₃(w)) = −Φ(n)` exactly,**

with `Φ = v₂(n+1) + v₃(n+1)` the conserved budget of `ValuationExchange`.  So
`κ ≤ −1` holds always — but only because it reads `−Φ ≤ −1`, i.e. `Φ ≥ 1`, which is
Terras' statement that the run is nonempty.  **`κ` never sees the contraction.**  It
is the budget with a minus sign, and `budget_constant` already says the budget does
not move.  The measured histogram of `κ` is exactly the geometric profile of `Φ`,
reflected — as the identity forces.

### The corrected surplus, and the kill test

The intended quantity is the *harvest* `v₂(n′+2) = v₂(3^r·w + 1)`, the `2`-content
the contraction actually pulls in.  Put `κ* = v₂(n′+2) − v₃(n′+1)`.  Over all odd
`n < 2^20`:

* **mean `κ* = −0.49999`** — exactly `−1/2`, since `E[harvest] = 2` and
  `E[Φ] = 2 + 1/2 = 5/2`;
* **`P(κ* > 0) = 0.26667`**, about `4/15`;
* **maximum `+19`**, with the harvest's geometric tail.

The mean is genuinely favourable — negative, not zero.  But the **positive tail is
unbounded**, inherited from the harvest, which Round LI showed equals `2 + v₂(t+r)`
and is unbounded.

So by the proposal's own kill test, precisely: `κ*` is a **drift, not a descent
function**.  A negative mean with an unbounded positive tail is an average
statement, and averages do not transfer here — `no_uniform_block` proves no bounded
block descends for every `n`, and `2^j − 1` realises arbitrarily long growth.  `κ*`
cannot be pointwise negative, because the harvest alone exceeds any bound.

### Proved

`run_end_value`, `run_end_odd`, `kappa_zero_two_part`: the `2`-part is empty at the
end of a run, which forces `κ = −Φ`.  Kernel-checked at `(r,w) = (1,1), (2,3),
(3,5), (4,7)`: the end-of-run `u` values `3, 27, 135, 567` are all odd.

Nothing is claimed for `κ*`; its positive tail is unbounded and no pointwise
statement is available.

### Axiom footprint

`lake build Collatz` succeeds, **295 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXI — the sign flip is rigid; the logarithm jump is a coin flip

Approach 4 of three.  One real theorem, and its Lyapunov hope refuted by its own
kill test.

### The rigid part, proved

`w(s) = oddpart(3^s − 1)`; for odd `s`, LTE gives `v₂(3^s − 1) = 1`, so
`w(s) = (3^s − 1)/2`.  Then, with no hypothesis at all,

**`three_pow_add_two`: `3^(s+2) − 1 = 9(3^s − 1) + 8`,  hence `w(s+2) = 9·w(s) + 4`.**

Modulo `8` that is an involution: `9w + 4 ≡ w + 4`, sending `1 ↦ 5`, `5 ↦ 1`,
`3 ↦ 7`, `7 ↦ 3`.  Since `LogCoordinate` puts `ε = +1` exactly on `{1,3}`, the sign
**flips at every two-step, always** (`w_sign_flips`).

Re-verified independently here for all odd `s < 4000`: recurrence exact, sign flips
in every case.  Kernel-checked: `w mod 8` runs `1, 5, 1, 5, 1, 5` on
`s = 1,3,5,7,9,11`, with `w = 1, 13, 121, 1093, 9841, 88573` — a perfect two-cycle.

(Those values are exactly the family named in approach 3's kill test, so the two
approaches meet here.)

### The part that would have to decrease, refuted

The hope: the jump `t′ − t` in the discrete logarithm carries a **pointwise** sign,
so the logarithm cannot run uphill forever.  Measured with a genuine `2`-adic
discrete log (Pohlig–Hellman in `⟨3⟩ ⊂ (ℤ/2^N)^×`, order `2^(N−2)`, self-checked
against direct exponentiation), `2000` consecutive odd `s` at `N = 24`:

* sign flips in **all 2000** cases — the algebra confirmed numerically;
* `t′ − t` **positive 1019, negative 981** — a coin flip;
* ten windows of `200` each split near `50/50` (`104/96`, `99/101`, `108/92`,
  `100/100`, …) — no drift, no run of one sign;
* the cumulative sum wanders (`1.53M, 3.08M, 1.68M, 0.52M, 0.16M, 2.71M, 3.50M,
  3.61M, 1.50M, 1.39M`) — a random walk, not a trend.

**Verdict: `t′ − t` has no pointwise sign, so this is not a Lyapunov function.**  A
mean-near-zero, sign-unpatterned quantity is a drift, and drifts do not transfer
here — `no_uniform_block` proves no bounded block descends for every `n`, and
`2^j − 1` realises arbitrarily long growth.

### What the round actually establishes

The rigid part of the structure is the **sign of `ε`**; the part that would have to
decrease is the **logarithm `t`**, and that is exactly the part with no pattern.
The involution is real and worth having formalised, but it constrains the coset,
not the magnitude — and the magnitude is what a descent argument needs.

### Axiom footprint

`lake build Collatz` succeeds, **296 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXII — the orbit semigroup buys nothing

Approach 3 of three.  The kill test fires, and the decisive half is formalised.

### A measurement error worth recording

A capped breadth-first search over the semigroup generated from `1` by `w ↦ 3w`
and `w ↦ oddpart(w+1)` reported that `oddpart(3^s − 1)` was **absent** for `s ≥ 9`,
which would have been a genuine constraint.  That was an artefact.  The search
truncates exactly the paths that rise via `w ↦ 3w` and return via
`w ↦ oddpart(w+1)`, and `9841` is only `14` bits — far too small to be genuinely
unreachable.

Computing the **true closure** below a bound instead reverses the reading
completely.

### The measurement

* **Density `0.5091` among odd numbers below `2^22`** — about half of them, not a
  thin set.
* **All sixteen odd residues mod `32`** occur: no congruence obstruction at any
  level tested.
* `max ρ` on the closure against all odd `w` of matched bit length: `13/13`,
  `18/18`, `16/15`, `17/17` — **no gap**.  The closure attains the same deep
  valuations as the unrestricted set.
* The `oddpart(3^s − 1)` family is present throughout the range where the closure
  is complete; the few apparent absences move as the bound moves, which is the
  signature of a truncated path rather than a real one.

### The kill test, formalised

`LogCoordinate.growth_blocked` permits deep `2`-valuation only for
`w ≡ 5, 7 (mod 8)`.  Both classes are reached, in three and four steps:

`1 → 3 → 9 → 5` (as `9 + 1 = 2·5`) and `1 → 3 → 9 → 27 → 7` (as `27 + 1 = 4·7`).

`Strategy/OrbitSemigroup` gives `Semi` as an inductive predicate — the second
generator in decomposition form (`w + 1 = 2^k·v`, `v` odd), so no `oddpart`
function is needed — together with `semi_five`, `semi_seven`,
`semi_meets_both_deep_classes`, and `semi_three_pow`.  **All four depend on no
axioms whatever.**

**Verdict: the restriction buys nothing.**  The semigroup meets every class in
which deep valuation can occur, by short explicit derivations, and attains the same
maximal `ρ`.  Route closed.

### Axiom footprint

`lake build Collatz` succeeds, **297 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXIII — one witness certifies a whole interval

Approach 5 of three.  The two remaining agents died on a session rate limit, so
this and Round LXII were done directly.

### The interval form

`ExclusionRatio.excluded_transfer` (Round XLIII) already proves a length can be
excluded by a witness at a *different* length: `wt L · dev W ≤ wt W · dev L` —
cross-multiplied `r(L) ≤ r(W)` — transfers exclusion.  `IntervalCertificate`
packages it as a sweep needs it: fix one witness `W` excluded at `c`, and **every**
`L` with `r(L) ≤ r(W)` follows with no further computation.  `witness_trans` makes
it transitive.

### What it buys, measured

At the repository's kernel-proved `c = 1 086 464`:

* product-bound frontier `L = 2593`;
* argmax of `r` over `[1, 2592]` is `L = 1539`, `r = 661 176 < c`, so the witness is
  itself excluded;
* **all `2592` lengths satisfy `r(L) ≤ r(1539)`.**

A `CycleLength2593`-style sweep — `2592` separate `excludedFast` evaluations —
collapses to **one**.

Conditionally on Barina's `c = 704·2^60 ≈ 8.12 × 10^20`:

* argmax of `r` over `[1, 10^5]` is `L = 75 235` (`a = 47 468`), `r ≈ 2.90 × 10^9`,
  far below `c`;
* direct sweep: `~10^5` `decide` calls on numerals up to `~10^5` bits;
* **via transfer: one `decide` at `L = 75 235`, `~75 235`-bit numerals** — and this
  repository already discharges `decide` at `~40 000` bits (`barina_sweep`) and at
  `6809` bits.

So **transfer makes the Barina-conditional `L ≥ 10^5` kernel-checkable**, where a
direct sweep is defeated by runtime rather than by mathematics.  `topIndex` is exact
below `10 439 860 591`, so `75 235` is arithmetically sound.

### A correction worth recording

My first pass took the argmax of `r` over `[1, 6808]`, got `L = 5755` with
`r = 3.01 × 10^6`, and nearly reported one witness covering the repo's whole
unconditional range.  That is wrong: `3.01 × 10^6 > 1 086 464`, so `5755` is **not**
excluded by the product bound at that range.  The repo's unconditional `6809` comes
from `RealizableFrontier6809`, a different certificate — not from the product bound
at `1 086 464`, whose frontier is `2593`.  The two prices had been conflated.

### Kill test, answered honestly

The witness is always the top rung of the semiconvergent staircase below the
target, and the reachable range is still exactly the frontier priced by
`a_k·a_{k+1}/(6 ln 2)`.  **This is an optimisation, not new mathematics** — it does
not move the frontier by one length, and Round XLIV's proof that no finite range
collapses the ladder stands untouched.

It is formalised because the kill test's own second clause is met: it converts an
infeasible sweep into a feasible one at Barina scale.

### Axiom footprint

`lake build Collatz` succeeds, **298 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

### Round LXIII, addendum — the Barina premise confirmed exactly

Round LXIII's Barina figures rested on the Round XLIV asymptotic.  A direct scan
with exact `2^L` and `3^a` bignums has since confirmed the premise outright:

* at `c = 704·2^60` there is **no product-bound frontier below `200 000`** — every
  length under `2 × 10^5` is excluded, so the witness `L = 75 235` sits inside the
  excluded region with a factor of nearly three in hand;
* the same scan reproduces the proved-range line exactly: at `c = 1 086 464`,
  frontier `2593`, argmax `1539`, `r = 661 176 < c`, all `2592` lengths covered.

So the interval-certificate claim no longer depends on an asymptotic estimate at
any point.  The kill-test verdict is unchanged: still an optimisation, not new
mathematics.

## Round LXIV — approaches 6, 7, 8: three kill tests, three fires

All three carried their own kill test.  All three fired.  One exact congruence
survives and is proved; the rest is recorded so the elimination is not repeated.

### 6 — the opening template.  Congruence exact, kill test fires.

For odd `n` with `n + 1 = 2^r·w`, `w` odd, `exchange_orbit` gives
`T^r(n) = 3^r·w − 1`, even because `3^r·w` is odd (`run_lands_even`).  The
template's demand — *exactly one even step after the first run* — is then one
congruence:

**`one_even_step_iff` : the step after the run is odd `⟺ 3^r·w ≡ 3 (mod 4)`.**

Verified for every odd `n < 200 000`, no exception, and kernel-checked at
`r = 1…7`, where the `iff` alternates exactly with the parity of `r`.

But the template never empties.  Measured survival over `B` blocks:
`0.49999, 0.25001, 0.12496, 0.06249, 0.03122` — **exactly `2^(−B)`**.  Each block
costs precisely one bit, so the template is satisfiable at positive density for
every `B` and dies at no depth.

And the kill test fires outright.  `killtest_family`: for `w = 1` the congruence is
`3^r ≡ 3 (mod 4)`, which holds **exactly when `r` is odd** — so `n = 2^r − 1` fits
the template for every odd `r`, while `T^r(n) = 3^r − 1 > n`.  The saturating family
sits inside the template at every odd scale.  The template recovers Terras, no more.

### 7 — a third modulus.  Dead, by its own kill test.

Odd elements of never-dropping windows, `n < 10^6`, longest prefix `41`.  Residues
mod `5` occur at `0.2004, 0.1996, 0.1998, 0.2005, 0.1997` — flat.  All fifteen
residues mod `15` occur.  And **every pair of mod-`5` classes co-occurs inside a
single window**, so there is no pair-exclusion, not merely no singleton.

The contrast is the content: on the same data mod `3` *is* structured —
`0.032, 0.262, 0.706` — while mod `5` is uniform.  **Local modular avoidance really
does stop at `3`.**  Route closed.

### 8 — the inverse chain.  Premise refuted.

**All `30 468`** never-dropping windows contain two points on the same inverse
chain — `100 %`.  Not a near miss: the chain `u, (2/3)u, (4/9)u, …` **is** the
growth ladder of `ValuationExchange` read backwards (`ReturnMap`, Round XLIX), so a
growth run rides one chain by construction.  Asking an orbit not to revisit a chain
is asking it not to grow.

The `3`-adic toll is real but already accounted: mean `v₃(u)` along never-dropping
windows is `1.7675` against `0.5` for random integers — precisely because growth
banks `+1` of `v₃` per step, which is the exchange law.

Kill test: **zero** windows contain a repeated value, so "cannot visit a chain
twice" reduces to injectivity on a never-dropper — that is, to distinctness, which
the repository already has.

### Axiom footprint

`lake build Collatz` succeeds, **299 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXV — the constraint set is over-determined; the two-step monomial is not

### Part 1: the constraints force a candidate, and it dies twice

Living at the contraction *and* having to differ on `T` versus `3n−1` forces the
`u`-coordinate ceiling/floor — in `n` the two maps share the even branch `n ↦ n/2`
**exactly**, so any statistic there is identical by construction.  At even `n = 2m`,
`T` harvests `v₂(m+1)` and the mirror `v₂(m−1)`, so the unique antisymmetric harvest
statistic is

`χ(n) = v₂(m+1) − v₂(m−1)`  —  same prime on both sides, never `v₂` with `v₃`.

Measured: antisymmetric in `m mod 4` exactly as required (`m ≡ 1` gives `χ < 0`,
`m ≡ 3` gives `χ > 0`, `m` even gives `0`), and it separates `T` from the mirror on
`50 %` of even `n`.  **But it fails two kill criteria at once:**

* **invariant under `n ↦ n + 2^M`** — identical for `M = 16, 20, 24` on every sample
  (`9998/9998`);
* **mean-zero with symmetric tails** — mean `0.000025`, `P(χ>0) = 0.25`, range
  `±16`.

And the first failure is structural, not incidental: **any statistic built from
valuations at the contraction is invariant under `n ↦ n + 2^M`**, because `v₂(m±1)`
is determined by `m mod 2^k`.  The constraint set — *live at the contraction*, *be a
valuation statistic at one prime*, *and see the archimedean size* — is
over-determined.  That is the named obstruction.

### Part 2: `Δ`, and what actually survives

`Δ(n) = (n − T²(n))·σ(n)` restricted to `v₂(n+1) = 1`.  But `v₂(n+1) = 1` **is**
`n ≡ 1 (mod 4)`, so `σ ≡ +1` on the evaluation set: the sign factor is inert, and
`Δ` is neither odd nor even in `m mod 4` because only one class is ever visited.

With `n = 4k+1`, over all such `n < 2^20`, `Δ` is exactly linear in `k`, no
exceptions — and **the three histograms differ**:

| map | `Δ` | slope |
|---|---|---|
| `T` | `k` | `+1` |
| mirror `3n−1` | `−5k` | `−5` |
| `expStep` | `−5k − 2` | `−5` |

Equivalently, as exact two-step laws on `n ≡ 1 (mod 4)`, zero violations over all
such `n < 300 000`:

* `T`: **`4·T²(n) = 3n + 1`**  (Round LV)
* mirror: **`4·M²(n) = 9n − 5`**  (`mirror_two_step`)
* `expStep`: **`4·E²(n) = 9n + 3`**  (`exp_two_step`)

**The exact differing monomial is the coefficient of `n`: `3` for `T`, `9` for both
others.**  On this class Collatz contracts by `3/4` while both filter models expand
by `9/4`.  `two_step_separates` proves `T²(n)` lies strictly below both for every
`n > 1` in the class; kernel-checked at `n = 5, 9, 13, 17, 21`, where `T²` gives
`4, 7, 10, 13, 16` against the mirror's `10, 19, 28, 37, 46`.

This is F1/F2 made quantitative **at the contraction**: `v₂(n+1) = 1` is exactly
where Collatz's two-step contracts and both models expand, by a factor of three in
the leading coefficient.

### The kill test, answered

`Δ` on never-dropping prefixes is positive and unbounded — `120 486` samples,
positive in all, maximum `1 433 531 479`.  But positive means *descent*, and the
value is exactly `(n−1)/4`: Round LV's `drop_of_v2_one` restated.  So `Δ` itself is
not formalised, as instructed — only the differing monomial is.  `Δ` also fires on
only half of odd `n`, and `no_uniform_block` already rules out any bounded block
descending for every `n`.

### Axiom footprint

`lake build Collatz` succeeds, **300 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXVI — the `t′−t` route closes; a log-free contraction criterion survives

### The kill test does not apply

`n = 2^j − 1` has `w = oddpart(n+1) = 1`, hence `ε = +1` — checked at
`j = 3, 5, 8, 12, 20`.  **It is not on the `ε = −1` branch at all.**  By
`LogCoordinate.growth_blocked` the `ε = +1` branch regenerates at most `2`, so that
family cannot sustain deep growth and cannot be the counterexample the kill test
guarded against.  The guard was aimed at the wrong family.

### The table factors, so the `t′−t` route closes

Over all odd `s < 2^16` on the `ε = −1` branch, the table of
`(v₂(s), sign(t′−t), a mod 4)` has marginals

* `v₂(s)`: `0.5, 0.25, 0.125, 0.125`
* `sign(t′−t)`: `−1 ↦ 0.4954`, `+1 ↦ 0.5046`
* `a mod 4`: `0.0667, 0.5334, 0.2666, 0.1333`

and the largest relative deviation from the product measure is `0.1089`, on a cell
with `75` counts against `67.6` expected — inside Poisson noise (`√75 ≈ 8.7`).
**There is no non-product cell to formalise**, and `sign(t′−t)` is a coin flip,
confirming Round LXI independently.

### What survived, and it is stronger than what was asked

The pointwise statement exists, but it concerns the *harvest*, not `t′−t`, and it
needs **no discrete logarithm**:

**`harvest_one_iff` — regeneration is exactly `1` ⟺ `3^(a−1)·w ≡ 1 (mod 4)`.**
Zero violations over `150 000` odd `n`.

In the logarithm chart this is the union of the two shallow cases (`ε=+1, s` even
and `ε=−1, s` odd); stated this way it is arithmetic mod `4`.  And harvest `1`
forces contraction:

**`shallow_then_contract` — if `3^(a−1)·w ≡ 1 (mod 4)` then the next block is `2v`
with `v` odd, and the step after sends `2v ↦ v+1 < 2v`.**
Zero violations over `50 002` samples.

Since `3^(a−1)·w` is odd it is `1` or `3` mod `4` (`criterion_dichotomy`), so the
criterion fires on **about half of all blocks** — pointwise, by a congruence, with
no average, no drift, and no logarithm.  That is the shape the mission demanded,
reached from the other side.

### What it does not do

Conditional, not global.  The complementary class `3^(a−1)·w ≡ 3 (mod 4)` is exactly
where regeneration can be deep, and nothing here bounds it.
`no_uniform_block` already proves no bounded block descends for every `n`, so a
criterion firing on a fixed congruence class cannot close the argument alone.  What
it adds is an explicit, checkable, log-free half.

### Axiom footprint

`lake build Collatz` succeeds, **301 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXVII — the shallow chain: exact, geometric, unchainable

### A correction to my own reading

The target shape `T²(n) ≤ n − n/4` is not merely true — with `Nat` division it is an
**equality**: for `n ≡ 1 (mod 4)`, **`T²(n) = n − ⌊n/4⌋`**, zero violations over every
such `n < 300 000`.  I first judged the stated form false by reasoning with real
division, where `(n−1)/4 < n/4`.  With `⌊·⌋` they agree exactly: `n = 4k+1` gives
`⌊n/4⌋ = k` and `T²(n) = 3k+1 = n − k`.  The mission's shape was right and mine was
wrong.

The companion holds too: `4w′ ≤ 3n + 5`, i.e. `w′ < (3/4)n + 2`, no violations.

### Both kill tests fire, as predicted

* `n = 2^j − 1` evades the hypothesis for every `j ≥ 2`, since `v₂(n+1) = j ≠ 1` —
  all 23 checked.
* Chaining needs the hypothesis to persist, which no bounded block supplies.

### The chain, exactly

**`shallow_chain` — if `T^(2i)(n) ≡ 1 (mod 4)` for all `i < k`, then
`4^k · (T^(2k)(n) − 1) = 3^k · (n − 1)`.**

Zero violations over `66 686` tested stages, chains as long as `k = 25` occurring.
So `T^(2k)(n) − 1 = (3/4)^k (n − 1)` exactly — pure geometric decay to the fixed
point `1`.  Kernel-checked at `n = 5, 13, 17, 53, 213`, where `4(T²(n) − 1)` and
`3(n−1)` agree at `12, 36, 48, 156, 636`.

### The remainder: the fraction of shallow runs

On never-dropping windows of length `≤ 40` below `2^20` — `106 496` windows:

* overall fraction with `v₂(x+1) = 1`: **`0.38735`**, against `0.5` unrestricted;
* **decreasing with window length**: `0.41146, 0.39245, 0.38354, 0.38050, 0.34274`
  across lengths `8–15, 16–23, 24–31, 32–39, 40–47`.

Never-droppers are systematically short of shallow runs, increasingly so.  **But no
pointwise bound below `1/2` is available** — the per-window maximum is `0.625`.  So
the honest provable statement is the extreme case only (`not_all_shallow`): a
never-dropper **cannot be all-shallow**, since `k` shallow stages force decay by
`(3/4)^k`.

Why it stops there: consecutive shallow stages occur with probability
`0.75, 0.1875, 0.0469, 0.0117, …`, i.e. `≈ (3/4)·4^(−(k−1))`.  The chain is exact but
its **length is geometric**, and persisting requires `n ≡ 1 (mod 4)` afresh at every
stage — exactly the uniform block `no_uniform_block` refutes.

### Axiom footprint

`lake build Collatz` succeeds, **302 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXVIII — the Eliahou form at Barina scale, and the kill test that fires

### The form, with current continued-fraction data

Eliahou's constants `301 994`, `17 087 915`, `85 137 581` are convergent numerators
of `log₂ 3`, at indices `13, 15, 16` — confirmed by recomputing the expansion:

`… 485, 1054, 24727, 50508, 125743, 176251, 301994, 16785921, 17087915, 85137581,
272500658, 357638239, 630138897, 9809721694, 10439860591 …`

At the Barina floor `c = 704·2^60 ≈ 8.117 × 10^20`, the product bound leaves exactly
the one-sided best approximations above its frontier.  The surviving lengths begin

`114 208 327 604`,  `217 976 794 617`,

and the first is `103 768 467 013 + 10 439 860 591` — the **sum of two consecutive
convergent numerators**, a semiconvergent.  So the Eliahou-type form at this scale is
`p = αa + βb + γc` with `α, β, γ` the convergents near indices `21–23`, `b ≥ 1`,
`ac = 0`, rather than the `13, 15, 16` of 1993.

### The kill test fires

**The form is implied by what the repository already has** — precisely the stated
kill condition.

`ExclusionRatio.excluded_iff_gap` (Round XLIII) proved `L` is excluded exactly when
`c` exceeds `r(L) = wt L / (3·dev L)`, a function of `L` alone, and Rounds XLIII–XLIV
established that the records of `r` — hence the survivors — are exactly the one-sided
best approximations of `log₃ 2`, the semiconvergent ladder `P + kP′`.  **That ladder
is the Eliahou-shape set.**

So semigroup membership restates `product_invariant`'s ratio form.  **No new theorem
is claimed; the kernel closes no length beyond `RealizableFrontier6809`.**

### What was formalised, and only that

`Strategy/PeriodLadder`, the packaged arithmetic implication and nothing more:

* `period_not_excluded` — a cycle whose every element is `≥ c` cannot have an
  excluded period (contrapositive of `no_cycle_of_excludedLength`);
* `period_not_excludedFast` — the same through the fast test;
* `period_ratio_ge` — in `wt`/`dev` coordinates, an admissible period satisfies
  `3·c·dev L ≤ wt L`, i.e. `r(L) ≥ c`.

Since the `r`-records are the one-sided best approximations, that last is exactly
"the period lies on the ladder" — the content of "min-cycle-element `≥ 2^K` ⇒ `p`
belongs to the semigroup", one rewrite from what was already proved.

### Axiom footprint

`lake build Collatz` succeeds, **303 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXIX — the two certificates cost the same, and the 7863 recipe is exact

### A correction to my own framing

I said `HHThreshold`'s price `1 358 718` for `L = 6809` was "the cheapest route past
6809".  Wrong on both halves.  **`6809` is already free**: the `Bcap`
realizable-frontier certificate reaches it at `c ≥ 1 086 055`, and the repo's proved
range is `1 086 464`.  And the number `1 358 718` buys **`7863`**, not "past 6809".

### The two price tables are the same table

Comparing `HHThreshold`'s price-to-kill against `RealizableFrontier6809`'s own
staircase — these are *independent* constructions, the sharp Halbeisen–Hungerbühler
criterion and the `Bcap` frontier certificate:

| kill `L` costs (HH) | certificate: `c` at least → frontier |
|---|---|
| `2593` → `420 842` | `420 842` → `L ≥ 3647` |
| `3647` → `620 859` | `620 859` → `L ≥ 4701` |
| `4701` → `841 478` | `841 478` → `L ≥ 5755` |
| `5755` → `1 086 055` | `1 086 055` → `L ≥ 6809` |
| `6809` → `1 358 718` | `1 358 718` → `L ≥ 7863` |

**Identical at every riser, offset by exactly one rung** — killing `L` costs precisely
the range the certificate needs to push the frontier past `L`.  Five rows, no
exceptions.

That upgrades Round LXII.  There the finding was that independent methods *stop at the
same place*; here they also **cost the same to move**.  Both are reading the same
Diophantine object — the records of `G(i) = Bcap i /(2^(fexp i + 1) − 3^i)` and of
`r(L) = hhMin/(2^L − 3^a)` are the same convergents of `log₂ 3`.

### The `7863` recipe, and the blocker resolved

`RealizableFrontier6809`'s table gives the requirement exactly: index `A = 4961`,
range `c ≥ 1 358 718`, needing `cert 4961 … = true` and `pow_gap_4961 : 2^7862 < 3^4961`.

The verified range must go from `1 086 464` (block `1061`) to `≥ 1 358 718`
(block `1327`) — `266` more blocks, about six `checkRange` chunks, `~21`-bit numerals,
a few minutes of kernel time.

**The open question was the fuel, and it is now closed.**  The sieve runs
`dropsWithin fuel (2^10·m + r)` at `fuel = 200`.  Scanning every `n` in
`[1 086 464, 1 358 848)`:

* **maximum steps-to-drop is `224`**, at `n = 1 126 015`, block `m = 1099`;
* and that is the **only** residue in the whole range exceeding `200` — exactly one.

So `fuel = 200` is **not** sufficient and the extension cannot be done at the current
setting; raising it to `224` (or `256`) suffices, and only a single residue forces the
raise.  The repo's own docstring had flagged `m = 1099` as "safely past the endpoint" —
true for the `1 086 464` endpoint, false for the `1 358 848` one.

### Status

No unconditional improvement is claimed.  `length_ge_6809` stands as the strongest
unconditional bound.  What this round produces is an exact, executable recipe for
`7863` — raise the fuel past `224`, extend `266` blocks, then `cert 4961` — together
with the finding that the two independent certificates are priced identically.

*Later: the recipe was executed.*  `Search.VerifiedRung7863` extends the sweep and
`Strategy.Frontier7863.length_ge_7863` is now unconditional; a second rung followed
(`VerifiedRung8917`, `Frontier8917.length_ge_8917`), so `8917` is the strongest
unconditional cycle bound.  Two things were added beyond the recipe.  First,
`Search.FuelMonotone.dropsWithin_mono`: the recipe says to raise the fuel, but
monotonicity means the `1061` blocks already proved at `200` can be *read* at `224`
with no recomputation, so an extension costs only its new blocks.  Second, the
certificates were decoupled from the ranges — `Strategy.PreCertified` banks six rungs
out to frontier `13133`, and `Strategy.FrontierParametric.length_ge_of_cert` states the
frontier theorem once over `(c, A, F)`, so a future range extension is an
instantiation rather than a proof.  Measured cost confirms why that split matters:
the block sweeps run `261 s`, every banked certificate together `6 s`.

### Axiom footprint

`lake build Collatz` succeeds, **303 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

### Round LXIX, addendum — divergence track: record-depth rigidity, refuted

The divergence track proposed **record-depth rigidity**: a *record* is an odd orbit
value exceeding all previous ones; a divergent orbit has infinitely many; the claim
was that every record must be **deep**, `v₂(r+1) ≥ 2`.  The motivation was sound —
`ShallowChain.two_step_exact` makes a shallow record drop by exactly `(r−1)/4`, a
per-visit identity rather than an average — and it nominally clears all three filters
(`v₂` uses F1, `drop_of_v2_one` is specific to `3n+1` so F2, "record" needs an order
so F3).

**Refuted by the first nontrivial start.**  Under the accelerated map,
`3 → 5 → 8 → 4 → 2 → 1`, records `3, 5, 8`; the record `5` has `v₂(6) = 1` — shallow.
(The agent's write-up gave the unaccelerated orbit `3 → 10 → 5 → …`; the conclusion is
the same either way.)

And the reason it fails is structural, not accidental.  Over odd `n < 120 000` there
are `163 146` odd records, of which `82 379` are shallow — **fraction `0.50494`**,
matching Terras' base rate `P(v₂ = 1) = 1/2` exactly.  **Records are an unbiased
sample of the `2`-adic depth law, not a special subsequence.**  So any device
constraining the depth of the record subsequence is the already-dead statistical drift
statement one level removed, and the `50/50` split must not be reported as progress.

Filter verdict: it dies to an exact counterexample rather than to F1/F2/F3 — the
sharpest kind of death, since no repair is available.

### Round LXIX, addendum 2 — the max side is inert, correcting Round LVIII

Round LVIII proved `ProductMax.cycle_max_bound` and claimed it "cuts the admissible
`(L,a)` region from two sides rather than one".  **The theorem is right; that
inference was wrong.**

Clear both inequalities with `θ = 1/(2^(L/a) − 3)`:

* min side `2^L·m^a ≤ (3m+1)^a` ⟺ **`m ≤ θ`**;
* max side `(3M+1)^a ≤ 2^L·M^a` ⟺ **`M ≥ θ`**.

**The same `θ`.**  The pair therefore says only `m ≤ θ ≤ M` — and the max side is a
*lower* bound on the maximum.  Exclusion needs an **upper** bound to contradict; a
cycle with a large maximum is not absurd.  So the max side **cannot contribute to
excluding any length**.  Checked at `(L,a) = (2,1), (485,306), (1539,971),
(2593,1636), (6809,4296)`, where `θ = 1, 99 781, 330 749, 583 287, 1.883 × 10^6`.

What makes the min side work is the *external* input `m ≥ c` from a verified range,
converting `m ≤ θ` into `c ≤ θ`.  No external upper bound on `M` exists, and the only
provable one is the chain bound `2^(a−1)(M+1) ≤ 3^a(m+1)`, from `2(n_{i+1}+1) ≤
3(n_i+1)` per step.  It misses the required threshold by `54`, `171`, `288` and over
`750` orders of magnitude at those pairs, the gap growing with `a`.  It is consistent
with the trivial cycle (`M ≤ 5` against `M = 2`) — not wrong, just hopelessly weak.

The second candidate, the exact identity `M+1 = 3^r·(w+1)/2^r` for the maximal run
ending at `M`, is genuine but circular: `w` is an unconstrained cycle element with
only `m ≤ w ≤ M` known, so `w ≤ M` reproduces the chain bound and `w ≥ m` gives
another lower bound on `M`.

**Verdict: the sandwich cannot close.**  `ProductMax`'s docstring has been corrected
in place; the theorem stands as a completion of the statement, not as a lever.

## Round LXX — the contraction boundary is `a ≤ 2`, sharpening Round LXVI

The shallow-vs-deep track returned a decisive negative on its own target and, in
passing, a correction to Round LXVI worth more than the target was.

### The count inequality does not exist

The sought envelope `#deep ≥ f(#shallow)` on never-dropping windows is not a
function: windows with `s = 8` exist at `d = 2`, while `s = 20` forces `d ≥ 21`.
The reason is exact — cancelling one deep block needs contracting blocks in number
proportional to *that block's own depth `a`*, since each contributes only a fixed
factor near `1/2` or `3/4`, and `a` is unbounded.  Both mandated kill tests fire:
the compensation cannot be expressed by any uniform block
(`DensitySaturation.no_uniform_block`), and the per-block log-factor has an
unbounded tail, so no drift argument survives.

### The correction: the boundary is `a ≤ 2`

`HarvestOne.shallow_then_contract` (Round LXVI) proved contraction when the
regeneration is exactly `1`.  **That is a strict special case.**  The exact factor is

`U′/U = 3^(a−1)/2^a + 1/(2^a·w)`,

governed by `a` alone up to the vanishing term:

| `a` | ratio | |
|---|---|---|
| `1` | `1/2 + 1/(2w)` | contracts |
| `2` | `3/4 + 1/(4w)` | **contracts** |
| `≥ 3` | `> (3/2)^(a−1)/2` | grows, unboundedly in `a` |

**Contraction holds exactly when `a ≤ 2`**, for `w > 1` — zero violations over
`15 992` pairs.  So the mod-`4` shallow/deep split does **not** align with the
growth/contraction split: inside the "deep" class, `a = 2` also contracts, and it is
about `42 %` of that class.

Coverage over odd `n < 300 000`: harvest `= 1` fires on `0.5000` of blocks; harvest
`≤ 2` on **`0.7500`**.  Half the domain becomes three quarters.

`Strategy/BlockContract` proves it: `block_contracts_of_le_two`
(`3^(a−1)·w + 1 < 2^a·w` for `w > 1`, `1 ≤ a ≤ 2`), `block_grows_of_three_le`, and
`residue_forces_contraction` tying it to `LogCoordinate.growth_blocked` — so whenever
the odd part is `1` or `3` mod `8`, the following block is forced down, now by the
sharp criterion rather than half of it.  Kernel-checked at `(a,w) = (1,3), (1,101),
(2,3), (2,101), (3,3)`, the last growing as predicted.

### Why it stops there

`a ≥ 3` grows with **no bound on the factor**: on `U = 2^j` the first block's ratio is
`2.56, 19.2, 146, 1108, 8417, 63917` at `j = 5, 10, 15, 20, 25, 30`.  One deep block
needs compensation proportional to its own unbounded depth — `no_uniform_block` again,
and the exact reason the count inequality cannot exist.

### Axiom footprint

`lake build Collatz` succeeds, **304 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXXI — the two certificates are literally the same integer

Round LXIX found the sharp Halbeisen–Hungerbühler criterion and the `Bcap`
realizable-frontier certificate charging identical prices at every riser, and called
it a coincidence.  **It is not a coincidence.  The numerators are the same integer.**

### The identity, verified independently

With `L = fexp a + 1`:

**`hhMin L a L = Bcap a`**

at every rung the two ladders use — `a = 306, 971, 1636, 2301, 2966, 3631, 4296` —
digit for digit, up to a **`2053`-digit** number at `a = 4296`.  Not proportional, not
rounding-close: **equal**.  At `a = 306` both are the same `148`-digit integer, and
dividing by `2^485 − 3^306` returns the tables' `72 059`.

Re-derived here from the repo's own definitions (`beattyRem/beattyBit/beattyCount/hhMin`
in `HalbeisenHungerbuhler`, `fexp/Bcap` in `RealizableBound`), not taken on report.

**It is not universal.**  It fails at `a = 2, 12, 53, 665` — the bare even-indexed
convergents, which are not rungs.  (`665` is the ladder's *step*, never a rung.)

### Why

Both quantities have the same shape.  Writing `pos i` for the position of the
`(i+1)`-th `1` in the ceiling-Beatty word of shape `(L,a)`: at a one-position
`j = pos i` the count is `i+1`, so `hhMin`'s term is `2^(pos i)·3^(a−1−i)`; and
`Bcap`'s recursion unfolds to `Σ_{i<a} 3^(a−1−i)·2^(fexp i)`.

**Both are `Σ_{i<a} 3^(a−1−i)·2^(e i)`** — with `e = pos` for one, `e = fexp` for the
other.  They coincide exactly when `pos i = fexp i` for `i < a`, which is verified true
at the rungs and false at `53` and `665`.

That is a continued-fraction fact about `log₂ 3`: the Beatty word's one-positions track
`⌊i·log₂ 3⌋` along the one-sided semiconvergent chain the ladder walks, and not off it.
So there is **no all-`a` theorem** — the statement is false for generic `a` — and no
induction on `a` alone can prove it.

### `Strategy/PriceIdentity`

The part that is a theorem rather than a computation:

* `Bsum` — the common shape as a cocycle recursion;
* **`Bcap_eq_Bsum`** — `Bcap` *is* `Bsum fexp`; depends on **no axioms at all**;
* **`Bsum_congr`** — exponent sequences agreeing below `a` give equal sums;
* `numerators_agree` — hence, given `pos = fexp` below `a`, the numerators coincide.

Kernel-checked: `Bcap` and `Bsum fexp` agree at `a = 0…7` (`0, 1, 5, 23, 85, 319, 1085,
3767`).

The remaining bridge `hhMin L a L = Bsum pos a` is the one-position reindexing of
`HHLemmaFive.times_word_eq`; it is carried as a **hypothesis**, not an axiom, and each
rung's `pos = fexp` check is a finite `decide` in the style of this repo's own `cert`
certificates.

### What it means

Two constructions from different papers — H–H's minimum over admissible words, and the
`Bcap` realizable-frontier bound — are computing **one object**.  That explains Round
LXII's finding that independent methods stop at the same wall, and Round LXIX's that
they cost the same to move: there was only ever one certificate, wearing two notations.

### Axiom footprint

`lake build Collatz` succeeds, **305 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXXII — the affine cocycle, and the block-depth threshold

Two tracks, both landing.  One separates Collatz from its divergent twin
structurally for the first time; the other corrects a direction I got wrong.

### Collatz is affine; `expStep` is multiplicative

Since `w = U/2^a`, the block map `U = 2^a·w ↦ 3^(a−1)·w + 1` is

**`U′ = λ_a·U + 1`,  `λ_a = 3^(a−1)/2^a = (1/3)(3/2)^a`.**

An **affine cocycle**: multiplier chosen by `v₂(U)`, plus a *constant* translation.
The `+1` is not a rounding artefact — it is the translation part.

And the divergent twin fails it not by a margin but by **degeneracy**:

**`expStep_block` : `expStep^a (2^a·w) = 3^a·w`, exactly** — no violations over `5187`
pairs, `a ≤ 13`, and now proved by induction in Lean.

| | multiplier | translation |
|---|---|---|
| Collatz | `3^(a−1)/2^a` | **`+1`** |
| `expStep` | `3^a/2^a` | `0` |

Kernel-checked at `(a,w) = (1,3), (2,5), (3,7), (4,9)`: `expStep` gives
`9, 45, 189, 729`, Collatz gives `4, 16, 64, 244`.  **The `+1` is exactly what the
twin lacks.**  That is filter F1 — "a proof must use that even steps divide" — made
exact at block level, and the first statement here separating the two maps
*structurally* rather than numerically.

Measured, on the additive part `A_N` (satisfying `A_{k+1} = λ_{a_k}A_k + 1`): it is
**not** bounded absolutely — it reached `18 802`, and one block with `a = 25` lifts it
from `1` to `8417`.  But `A_N < U_N` always, and the *ratio* is `10^(−7)`–`10^(−12)` on
growth windows, order one only near the fixed points `U ∈ {2,4}`.  So the translation
is a boundary effect during growth.  A measurement, not a theorem.

### The block-depth threshold, and my error

A window grows only if `3^(S−N) > 2^S` (`S = Σa_i`), i.e. **mean block depth above
`log 3/log(3/2) = 2.709511…`**, against an unconstrained mean of `2`.

Measured over every even `U₀ < 2^19`: **`65 537` never-dropping windows, exactly `2`
violations** — and both are the fixed points `U₀ = 2` and `U₀ = 4`, where `w = 1` makes
the `+1` cancel the swap forever.  The mean tightens onto the threshold **from above**:

| min length | mean `S/N` | windows |
|---|---|---|
| `N ≥ 1` | `3.1112` | `65 537` |
| `N ≥ 10` | `2.7653` | `3 442` |
| `N ≥ 20` | `2.7412` | `620` |
| `N ≥ 30` | `2.7308` | `130` |

**My task specification had the implication backwards.**  I asked for *"if
`3^(S−N) ≤ 2^S` then the window does not grow"*.  The chain inequality bounds `U_N`
from **below**, so it can force growth and never forbid it — and `U₀ = 2, 4` are exactly
the counterexamples to the literal converse.

Proved (`Strategy/DepthThreshold`): `block_step_exact` (the `+2^a` is precisely the
swap's shortfall), `block_step_ge`, `chain`
(`(∏3^(a_i−1))·U₀ ≤ (∏2^(a_i))·U_N`, no division, no logs), **`forced_growth`** (above
the threshold growth is forced), and **`depth_capped_of_no_growth`** (a non-growing
window has `3^(S−N) ≤ 2^S`).

This constrains the **depth multiset of a given window**.  It is not a descent theorem:
`no_uniform_block` stands untouched.

*Later:* the `2^j − 1` family no longer stands untouched.  `Strategy.MersenneDescent`
checks that it descends within `12j` for `2 ≤ j ≤ 200`, so it is not the obstruction
it was taken for; and `Strategy.RunLengthAny.no_tail_at_any_run_length` settles the
run-length question outright — no tail depending only on `r(n) = v₂(n+1)` works at any
`j ≥ 2`, while `j = 1` forces `σ = 2`.  The mean of `(σ − j)/j` over that family drifts
to `2.81` by `j ≈ 400`, matching the random-walk descent rate
`2·log(3/2)/log(4/3) = 2.8188` rather than the block-depth threshold `2.7095` above —
the two constants are close but unrelated.

### Axiom footprint

`lake build Collatz` succeeds, **337 jobs**.  Zero `sorry`.  Zero added axioms.

**Both halves of the conjecture remain open.**

# Round LXXIII — the frontier ladder executed, and what the run length controls

Two lines this round.  The first executes a recipe the repository had already
written down; the second answers a question it had posed and left open.

## 1. The cycle frontier: `6809 → 8917`

Round LXIX derived an exact recipe for `7863` — index `A = 4961`, range
`c ≥ 1 358 718`, `266` more blocks, fuel past `224` — and explicitly claimed no
improvement.  It is now executed, and one rung further.

* `Search.FuelMonotone` — `dropsWithin_mono`, `checkBlock_mono`,
  `checkRange_mono`.  The recipe says to raise the fuel; monotonicity means the
  `1061` blocks already proved at `200` are *read* at `224` with no
  recomputation, so an extension costs only its new blocks.  `VerifiedExtended`
  had noted this plumbing was not required at its own endpoint; crossing block
  `1099` requires it.
* `Search.VerifiedRung7863` (`266` blocks, range `1 358 848`) and
  `Search.VerifiedRung8917` (`299` more, range `1 665 024`).  The second needs
  no fuel change: the worst drop in `[1 358 848, 1 665 024)` is `214`, below the
  `224` already forced.  **Drop times are not monotone in the range**, so the
  fuel must be measured per range, never extrapolated.
* `Strategy.Frontier7863.length_ge_7863` and
  `Strategy.Frontier8917.length_ge_8917`.  The latter is the strongest
  unconditional cycle bound here.

**The certificates were decoupled from the ranges**, which is the reusable part.
`Strategy.PreCertified` banks six rungs out to frontier `13133` at their exact
least thresholds; `Strategy.FrontierParametric.length_ge_of_cert` states the
frontier theorem once over `(c, A, F)`, with `length_ge_6809_again` recovering
the old bound by instantiation as both a subsumption check and a non-vacuity
witness.  `Strategy.CertMonotone` shows a certificate survives any *larger*
range — including `bank_mono` for the unpacked form, which settles the caveat
recorded in the parametricity audit above.

Measured cost explains why the split matters: the block sweeps run `261 s`, every
banked certificate together `6 s`.  **Ranges are the whole expense; certificates
are free.**  Climbing stopped at `8917` by choice — each further rung is
mechanical and buys a fixed `+1054` for a linearly growing sweep — and none of it
touches Round XLIV's conclusion that the range needed per rung diverges.

`scripts/audit_ladder.py` re-checks the whole ladder outside Lean: reach, exact
riser, frontier optimality, and that the rungs lie on the semiconvergent
staircase `306 + 665k` of `log₂ 3`.

## 2. What the initial run length controls

`PROGRAM_STATUS` asked whether `n > T^(r(n) + s(n))(n)` for explicit `s`, with
`r(n) = v₂(n+1)`, and proposed `n = 2^j − 1` as the first test.  Answered, and
the obstruction is not where the question expected it.

* **Not in that family.**  `Strategy.MersenneDescent` checks it descends within
  `12j` for `2 ≤ j ≤ 200`; `σ/j` peaks at `11.2` on the small case `j = 5` and
  stays under `4.34` past `j = 30`.
* **No tail depending only on `r` works, at any `j ≥ 2`.**
  `Strategy.RunLengthUnbounded.no_tail_at_run_length_two`, then
  `Strategy.RunLengthAny.no_tail_at_any_run_length`.  For `n = 8a+3`,
  `T³(n) = 9a+4`, so choosing `9a+5 = 2^k` lands the orbit exactly on `2^k − 1`
  and `ScaleLadder.climb` carries it to `3^k − 1`.  The first member is `27`.
  Generalizing needs `3^j ∣ 2^(2·3^(j−1)m) − 1` — lifting the exponent at
  `p = 3`, which the repository lacked (`LiftExponent` covers `p = 2` only) and
  is now `Strategy.LiftExponentThree.two_pow_three_pow`.
* **`j = 1` is a genuine exception**, not an artefact: the construction needs
  `n < 2^k − 1`, which reduces exactly to `2^(j+1) < 3^j`, true precisely for
  `j ≥ 2`.  And at `j = 1`, `σ = 2` always
  (`Structure.CycleMinClass.two_step_descent`).
* **But `r` does bound descent from below, everywhere.**
  `Strategy.MersenneLower.sigma_gt_run_half`: `σ(n) > r + r/2` for every odd `n`,
  no parity assumption; sharpened at `12 ∣ r` to `σ(n) > (19/12)·r` by the
  convergent `19/12` of `log₂ 3`.  That is within `0.1 %` of `log₂ 3`, the
  ceiling no argument of this shape can pass — the run lifts by exactly
  `(3/2)^r` and a Terras step halves at best.

So `r(n)` bounds the descent time from **below** but not from **above**, which is
the precise sense in which the question's shape was the wrong one: it asked for
an upper bound in terms of `r`, and `r` only ever supplies lower ones.

## Corrections

* `Strategy.CycleVerified.cycle_length_ge_2966` is **superseded** and retained
  only as a cross-check.  It reaches odd-budget `2966` where
  `RealizableFrontier6809` already reached `4296` at the same verified range —
  the product bound `2^K·N^L ≤ (3N+1)^L` at `N = 1 086 464` yields what that
  file's Beatty certificate yields at `c = 620 859`.  Its value is corroboration:
  it lands on the riser indices `2966` and `3631` from a completely different
  inequality.
* A measured mean of `(σ − j)/j ≈ 2.718` over the `2^j − 1` family is **not** the
  block-depth threshold `log 3/log(3/2) = 2.7095` of Round LXXII.  It drifts to
  `2.81` by `j ≈ 400`, matching the random-walk rate `2·log(3/2)/log(4/3) =
  2.8188`.  Two close constants, unrelated.

## Axiom footprint

`lake build Collatz` succeeds, **338 jobs**.  Zero `sorry`.  Zero added axioms.
The block sweeps and every banked certificate depend on no axioms at all.

**Both halves of the conjecture remain open.**  The cycle half is bounded, not
excluded, and Round XLIV's divergence of the per-rung range requirement caps this
method regardless of effort; the divergence half is untouched by this round.

### Round LXXIII, addendum — what the run length bounds, and the convergents again

Written after the main entry; these results came later in the same round.

**The run length bounds descent from below, everywhere.**
`Strategy.MersenneLower.sigma_gt_run_half`: for every odd `n`, no iterate falls
below `n` within `r + r/2` steps, where `r = v₂(n+1)` — no parity assumption.  The
mechanism is one inequality: the opening run lifts `n` by exactly `(3/2)^r`, and a
Terras step halves at best, so `run_no_drop_pow` needs only `2^(t+r) ≤ 3^r`.

That hypothesis makes the constant a question about rational approximation, and
the convergents of `log₂ 3` from below give the instances — they alternate:

| convergent | `2^p ≤ 3^q` | ratio to `log₂ 3` |
|---|---|---|
| `19/12` | yes | `0.998972` |
| `65/41` | no | — |
| `84/53` | yes | `0.999964` |
| `485/306` | no | — |
| `1054/665` | yes | `0.99999994` |

`sigma_gt_1054_665` comes within `6·10⁻⁸` of `log₂ 3`, which is the ceiling no
argument of this shape can pass.  **Its denominator `665` is the spacing of the
frontier ladder's risers** (`306 + 665k`) — two unrelated arguments, the same
continued fraction.

**The `2^j − 1` family is sandwiched.**  `MersenneDescent` gives `σ ≤ 12j` for
`2 ≤ j ≤ 200` (a finite check); `MersenneLower.mersenne_sigma_gt` gives
`σ > 3j/2` for every even `j`, from `8^m ≤ 9^m`.  Linear growth, both sides.

**Heaviness now follows from never-dropping.**  The repository had fifteen
`*_of_heavy` consumers and no producer from a never-dropper;
`Frontier8917.heavy_of_neverDrops` supplies one at the extended range, and with
it `heavy_window_5625` (against `2592`) and `odd_steps_5625` — a counterexample's
minimum takes more than `3541` odd steps in its first `5625`.  The density is
unchanged at `17/27`; the window is what doubled.

**The counterexample profile is restated** at the new constants in
`Strategy.ProfileSharp`: `≥ 1 664 599`, heavy for `5625` steps, cycle length
`≥ 8917`.  No clause is added or removed.

**A lower bound on the total stopping time**, which the development lacked:
`TotalStoppingLower.total_stopping_exact`, `2^k = 3^(oddCount n k)·n + affineC k n`
when the orbit reaches `1` in `k` steps.  Exact, not an inequality.  Measured, the
residual over `3^q` stays below `n`, so `k − q·log₂ 3 ∈ [log₂ n, log₂ n + 1)`;
that last part is measured and **not** proved — it does not follow from the
identity, since the trailing even steps change neither `q` nor the accumulator.

### Axiom footprint

`lake build Collatz` succeeds from a clean tree, **340 jobs**.  Zero `sorry`.
Zero added axioms.

**Both halves of the conjecture remain open.**

## Round LXXIV, iteration 1 — the residual has no composition law

**Candidate.** Induct on a block decomposition of the word to force `δ ≥ 2`.
The motivation is that `(C, G)` composes *exactly* under concatenation, by a
single two-dimensional cocycle (`PhantomMediant.C_append`, `gap_append`):
`C(uv) = 3^a(v)·C(u) + 2^|u|·C(v)` and the same for `G`.  If the residual
inherited any composition rule from that cocycle, block control would compose.

**Membership audit** (all four `CLOSURE.md` tests passed, so it was admissible):
no orbit lower bound is invoked — no orbit appears at all; it does not reduce to
the factors of `∏(1 + 1/(3x_t))`; it consumes no prefix of an infinite path; and
it is *not* `d`-free, since `δ` is precisely the `d`-separating residual.

**Refuted by its own arithmetic** — `Strategy.ResidualComposition`.
`delta_no_composition_law`: there is **no** `F` with
`δ(uv) = F(δu, δv, |u|, a(u), |v|, a(v))`, for any `F` whatsoever.  Witness, all
of length ≤ 6:

| word | `L` | `a` | `C` | `G` | `gcd` | `δ` |
|---|---|---|---|---|---|---|
| `u  = [0,1]`          | 2 | 1 | 2  | 1  | 1  | 1  |
| `v  = [0,0,0,1]`      | 4 | 1 | 8  | 13 | 1  | 13 |
| `v' = [0,0,1,0]`      | 4 | 1 | 4  | 13 | 1  | 13 |
| `uv  = [0,1,0,0,0,1]` | 6 | 2 | 38 | 55 | 1  | **55** |
| `uv' = [0,1,0,0,1,0]` | 6 | 2 | 22 | 55 | 11 | **5**  |

The right factors agree in every one of `(δ, L, a, G)` — the cocycle's entire
input — and the concatenations agree in `(L, a, G)` and differ in `δ` elevenfold.
`C` is the only thing that separates them, which is the point: the residual reads
`C` against `G` multiplicatively, and multiplicative information is exactly what
a bilinear cocycle does not transport.  So the cocycle **does not descend to the
residual**, and no block induction of any composition rule can force `δ ≥ 2`.

`delta_created`: `δ(u) = δ(v) = 1` with `δ(uv) = 7`.  `delta_destroyed`:
`δ = 5` on both halves with `δ(uv) = 1`.  The residual is created out of nothing
and destroyed by concatenation.

**Stated weakness, exactly.**  `delta_destroyed`'s concatenation is `(01)^4`, a
member of the rigid `δ = 1` family that `PhantomMediant` already characterised
(for `L ≤ 22`: the all-even word and the two rotations of `(10)^(L/2)`, nothing
else).  So the *destruction* direction is exhibited only on that family, and a
composition law restricted to words with no trivial factor is **not** refuted.
`delta_no_composition_law` does not share the weakness — `concats_nontrivial`
checks `δ ≠ 1` on both of its concatenations — and it is the theorem the kill
rests on.

**What this closes.**  The block-induction route to `δ ≥ 2`, for every
composition rule.  It does not touch the counting route, which `DeltaSpectrum`
had already identified as the same route as the equidistribution of `C mod G`.

`lake build Collatz` succeeds, **341 jobs**; `scripts/check_integrity.sh` passes.
Zero `sorry`, zero added axioms.

*Housekeeping, same iteration.*  `Collatz/ProgramA`–`ProgramG.lean` — untracked
drafts written against `Mathlib` and carrying six `sorry`s — were turning the
integrity gate red while being imported by nothing.  They are moved verbatim to
`Sketches/`, outside the scanned tree; nothing is deleted, and the gate is green.

## Round LXXIV, iteration 2 — track C: the quantifier swap has no content

**Candidate.** Isolation.  The infinite admissible valuation words form an
inverse limit — a Cantor set of `2`-adic integers — and one asks that no positive
integer sit at a divergent point of it.  This is the premise of the quarantined
`Sketches/ProgramE`, and it is the natural track-C target because it is a
statement about the *limit*, not about any prefix, so `exists_realizer` does not
settle it.

**Membership audit.**  Passes three tests outright: no orbit lower bound is
invoked, it does not reduce to the factors of `∏(1 + 1/(3x_t))`, and it consumes
no finite prefix.  The `d`-free test is where it wobbles — the `2`-adic
conjugacy is `d`-free — but it does not die there either, since the statement is
about `3x+1`'s integer points specifically.

**Killed by circularity** (`CLOSURE.md` diagnostic 5, track-C form), and the kill
is a theorem rather than an observation — `Strategy.WordInjective`.

The only thing separating track C from prefix reachability is the quantifier
swap `∀L ∃n` → `∃n ∀L`.  **That swap has no content, because the `n` is
unique.**  `word_injective`: two odd positive integers whose odd-map valuation
sequences agree at every index are equal.  So an integer realizing every prefix
of an infinite word is not a new object to be excluded; it *is* the integer whose
word that is, and asking whether a divergent word has an integer realizer is
asking whether some integer diverges — the divergence half verbatim.

`word_injective_bounded` sharpens it and is the form that matters: agreement on
the first `n' + 1` valuations already forces `n = n'`.  The modulus is explicit
and linear, so no limit is involved at all — the `∃n ∀L` statement is decided by
a **bounded** prefix.  That is the strongest form of the kill: track C's escape
from prefix-consuming arguments is illusory, because the object it quantifies
over is pinned by a prefix of length `n' + 1`.

**The proof**, three inputs, all already here.  `traj_affine_exact` gives
`2^{K_L}·A = 3^L·n + S` and `2^{K_L}·B = 3^L·n' + S` with the *same* `K_L` and
`S` — both are functions of the word alone — so `3^L·(n' − n) = 2^{K_L}·(B − A)`;
`AccumulatorCap.dvd_cancel_three_pow` strips the `3^L` since `2^{K_L}` is not
divisible by `3`; `Ksum_ge` gives `K_L ≥ L`, and at `L = n' + 1` the modulus
exceeds the difference.

**Scope, stated exactly.**  This closes the *coordinate change*: passing to the
inverse limit and asking for isolation buys nothing.  It does **not** close every
limit-object argument — one that used a genuine property of the limit (a measure,
a dimension, a transcendence input) is untouched by injectivity.  What is refuted
is the specific hope that `∃n ∀L` is a weaker target than divergence.

`lake build Collatz` succeeds, **343 jobs**; `scripts/check_integrity.sh` passes.
Zero `sorry`, zero added axioms (`propext`, `Quot.sound` only).

## Round LXXIV, iteration 3 — track B: the counting drift cannot reach zero

**Candidate.**  A **counting drift**: a drift inequality on the number of
surviving residue classes rather than on orbit values.  Let `S_j` be the set of
residues mod `2^j` whose first `j` steps never drop, and seek an inequality
driving `|S_j|` down.  This is the right shape for track B — it is not a
pointwise or block Lyapunov function, and not an excursion-peak potential, since
it is a potential on a *set* and not on any trajectory.

**Membership audit.**  It rests on no orbit lower bound and does not reduce to
the factors of `∏(1 + 1/(3x_t))`.  It is not prefix-consuming in the fatal sense
either — it is a statement about *all* residues at level `j`, not about
continuing one path.  It is however **`d`-free**, which is the first kill: the
survivor classes are the same for every `3x+d`, so Round X's divergence-half
filter applies and `expStep` — heavy at every scale, every orbit divergent —
refutes any mechanism of this shape.

**The second kill is constructive, and it is the useful one.**
`ValuationDensity.Enum_pos` / `two_pow_le_Enum`: `E_ℓ ≥ 2^(−ℓ) > 0` at **every**
length.  The witness is explicit — the all-ones valuation vector is admissible at
every `ℓ` because `2^ℓ ≤ 3^ℓ` always, so `dpRow ℓ ℓ = 1` and the DP's `K = ℓ`
term alone contributes `2^ℓ` to `Enum ℓ`.  The bound is tight at `ℓ = 1`
(`Enum 1 = 2 = 2^1`), confirming it is exactly the all-ones term.

So a counting drift can deliver density `→ 0` — which is Terras's theorem, known
since 1976 — but **never emptiness**, and density zero does not exclude a
divergent orbit.  The survivor set is nonempty at every level, forever.

**What this closes.**  Any argument whose conclusion is "the surviving set
eventually empties".  It does *not* close arguments about the *rate* at which
density decays, which is Class 2 (the counting class) and closed separately by
the unconditional L¹ barrier.

**Connection worth recording.**  This kill is a corollary of the DP built for the
work-plan's item 12 — the same object that computes `E_ℓ = 1/2, 3/8, 1/4, …`
proves it never reaches `0`.  A construction built to measure a density turned
out to refute the hypothesis class that density belonged to, which is the
cheapest kind of kill available.

`lake build Collatz` succeeds, **343 jobs**; `scripts/check_integrity.sh` passes.
Zero `sorry`, zero added axioms.

## Round LXXIV, iteration 4 — reversal is not a symmetry of the residual

**Candidate.**  `G = 2^|w| − 3^a(w)` depends only on length and odd count, so it
is manifestly **reversal-invariant**.  If `gcd(C, G)` were too, `δ` would carry a
nontrivial involution on words, the `δ = 1` words would come in pairs, and a
fixed-point or parity argument would open on the residual.

**Membership audit.**  Passed all four tests: no orbit lower bound (no orbit
appears), no reduction to the factors of `∏(1 + 1/(3x_t))`, no prefix consumed,
and not `d`-free — `δ` is the `d`-separating residual.  Admissible, so it was
formalized rather than dismissed.

**Refuted by computation** — `Strategy.ResidualReversal`.  At length 12,
`w = 111100110100` is heavy at every proper prefix with `gcd(C, G) = 1` and
`δ = 1909`; its reversal has `gcd = 23` and `δ = 83`, against the **same**
`G = 1909`.  Measured scope: over every word of length `≤ 14` with `G > 0` the
gcd is preserved in 5875 cases and **broken in 548**; restricting to words heavy
at every proper prefix does not rescue it — 7 of 142 break, and the witness above
is the smallest heavy one.  Reversal is a genuine involution
(`reverse_involutive`), so this is an involution failing to descend, not a defect
of the map.

**The near-miss, and why it is empty.**  Over the same range *every* `δ = 1` word
reverses to a `δ = 1` word — 24 of 24 — which looks exactly like the sought
structure.  It is not.  The census returns 14 all-even words and 14 of the form
`(10)^k` or `(01)^k`, and nothing else: precisely the family `PhantomMediant`
already characterised as the *only* `δ = 1` words up to length 22.  That set is
reversal-closed because reversing `(10)^k` gives `(01)^k`.  So the closure is the
rigidity result restated, and by the Class 3 test it carries no information — a
symmetry of a set whose elements are already listed tells you nothing.

**What this closes.**  Any argument pairing words by reversal to constrain `δ`.
It leaves rotation untouched, which was closed separately and for a different
reason (the walk is closed, so max and min are rotation-invariant).

**Worth recording as method.**  The candidate was killed by the *second* check,
not the first.  The first check found the near-miss on `δ = 1` and looked like a
discovery; identifying the 24 words is what turned it into a restatement of a
known theorem.  A symmetry observed on a set should always be tested against a
census of that set before it is believed.

`lake build Collatz` succeeds, **344 jobs**; `scripts/check_integrity.sh` passes.
Zero `sorry`, zero added axioms.

## Round LXXIV, iteration 5 — the divergence-half filter cannot be narrowed

**Candidate.**  Not a new attack but the open task `CLOSURE.md` records against
its own Round X filter: `expStep` differs from `T` on a whole branch, whereas
`3x+d` differs in one constant, so the divergence-half filter is coarser than the
cycle filter.  *Narrowing it is the natural next task.*  The natural attempt is an
interpolating family that keeps the halving branch on a thin set:

    f_c(x) = x/2  when 2^c ∣ x,  else 3x/2 (even) or (3x+1)/2 (odd)

which is Terras at `c = 1` and `expStep` in the limit.

**Refuted, and the refutation generalises past the family** —
`Strategy.FilterWidth`.

The filter works only because `expStep` has a *one-line* divergence proof: every
step strictly increases.  A witness whose divergence were conjectural would
refute nothing.  So a usable witness must satisfy `x < g x` for all `x ≥ 1` — a
**no-contraction witness**.

`increasing_ne_halving`: such a witness has `g x ≠ x/2` at **every** even
`x ≥ 2`.  It cannot agree with the Collatz even branch anywhere — not on a sparse
set, not at a single point.  So `expStep`'s whole-branch difference is **forced**,
not an artefact of the choice, and the filter's coarseness is not reducible by
picking a better map of this kind.

The measurement confirms it where the attempt actually breaks: over the first
`20000` starts the number whose orbit dips below its own start is `12677` at
`c = 2`, `6149` at `c = 3`, `3045` at `c = 4`.  Every `c ≥ 2` contracts somewhere,
so `x < f_c x` fails and divergence — if true at all — stops being provable by
the means that made `expStep` useful.  Admitting halving on any set of positive
density reintroduces dips, which is `increasing_ne_halving` appearing numerically.

**Scope, stated exactly.**  Settled: the filter cannot be narrowed by weakening
the even branch, and "differs on a whole branch" is the minimum distance a
no-contraction witness can achieve.  **Not** settled: whether an entirely
different style of witness — divergent for a reason other than pointwise increase
— could do better.  Nothing here rules that out, and the theorems are about
no-contraction witnesses only, which is the class every known witness belongs to.

**Why this is worth an iteration.**  A filter is infrastructure for killing
candidates; knowing it cannot be sharpened is as useful as sharpening it, because
it stops future rounds from spending cycles on the interpolation idea.  The
`CLOSURE.md` entry has been amended so the open task now reads as answered rather
than pending.

`lake build Collatz` succeeds, **345 jobs**; `scripts/check_integrity.sh` passes.
Zero `sorry`, zero added axioms.

## Round LXXV, iteration 1 — one more rung, and a proof that the ladder ends

Two pieces, one of each kind the brief asks for: a number moved, and a route
closed.

### The number

`Strategy.PreCertified` banked `cert_6291` and `pow_gap_6291` against the
threshold `2 010 160` and had been waiting for a range.  `Search.VerifiedRung9971`
supplies it: the `338` blocks `1626 … 1963`, sweeping `[1 665 024, 2 011 136)`,
all at fuel `224`.  A direct scan puts the worst drop time in the new interval at
`222` (`n = 1 689 023`), so the fuel did not have to move — the second extension
in a row where it did not, while the range grew by a factor of `1.85`.  The `224`
record still belongs to `n = 1 126 015`, well inside the first million; the worst
drop time is not tracking the range.

`Strategy.Frontier9971.length_ge_9971` follows by the usual one-line
instantiation of `FrontierParametric.length_ge_of_cert`:

```
length_ge_9971 : 0 < n → AccIsCycleOf n L → ¬ ReachesOne n → 9971 ≤ L
```

Unconditional, `[propext, Classical.choice, Quot.sound]`.  The heavy window
widens with the certificate's reach: `heavy_window_6290` gives `2 ^ j ≤ 3 ^ a(j)`
for every `j ≤ 6290`, and `odd_steps_6290` reads `3960 < oddCount m 6290` off it
at the same `17/27` from `RunAlgebra.heavy_even_bound`.

This is the **last** banked rung the development's range reaches.  `11025`,
`12079`, `13133` need `2 403 661`, `2 855 820`, `3 380 808` and stay conditional.

### The route closed

Round XLIV asserted that no finite verified range excludes all cycle lengths,
supporting it with a *measurement*: the range needed to kill the `k`-th rung
grows like `a_k · a_{k+1} / (6 ln 2)`.  A measured growth rate is not a theorem,
and the assertion is load-bearing — it is the reason this ladder is a finite
resource rather than a programme.  `Strategy.RouteCap` proves it.

```
reach_lt_six_mul  : Bcap a + 3 ^ a * c < 2 * 2 ^ fexp a * c → a < 6 * c
cert_reach_le     : (∀ i < A, Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c) → A ≤ 6 * c
frontier_le_of_route : … → 2 ^ (F − 1) < 3 ^ A → F ≤ fexp (6 * c) + 1
route_misses_a_length : ∀ c, ∃ F₀, ∀ A F, cert … → gap … → F < F₀
```

Two collisions between `Bcap` and `fexp`, and nothing else:

* `2 ^ fexp a ≤ 3 ^ a` (`fexp_le`) weakens the certificate's right-hand side
  from `2 · 2 ^ fexp a · c` to `2 · 3 ^ a · c`, so the condition already forces
  `Bcap a < 3 ^ a · c`;
* `3 ^ i < 2 · 2 ^ fexp i` (`lt_fexp`) says each of the `a` summands of
  `Bcap a = Σ_{i<a} 3 ^ (a−1−i) · 2 ^ (fexp i)` exceeds `3 ^ a / 6`, giving
  `a · 3 ^ a ≤ 6 · Bcap a` (`six_Bcap_ge`, by induction on the `Bcap` recursion).

Together `a · 3 ^ a ≤ 6 · Bcap a < 6 · 3 ^ a · c`, and cancelling `3 ^ a` gives
`a < 6c`.  No positivity hypothesis on `c` is needed; at `c = 0` the certificate
condition is unsatisfiable and the reach is `0`.

**What is proved and what is not.**  Proved: the route's frontier is bounded by a
function of the range alone, so *every* finite verification leaves cycle lengths
untouched.  Not proved: the rate.  `a < 6c` allows `A < 12 060 960` at this
repository's range against an actual `6291`, a factor of `1917`.  The slack is
exactly the crude step `2 ^ fexp a ≤ 3 ^ a`, which throws away how closely
`3 ^ a` approaches `2 ^ (fexp a + 1)` from below.  Recovering the measured
quadratic law needs an effective irrationality measure for `log₂ 3` — Baker
territory, and outside this development's no-Mathlib, no-external-theorem budget.
The honest split is: **finiteness is elementary, the rate is Diophantine.**

**Why this is worth the iteration.**  The repository's most valuable artefacts
are the ones that stop future rounds spending cycles, and until now the reason
not to keep climbing the ladder was a table of measurements.  It is now a
theorem with an explicit `F₀`, which means the acceptance criterion (P1) can be
stated exactly: the certificate route can reach frontier `F` only for
`F ≤ fexp (6c) + 1`, and `CollatzConjecture` needs all `F`.  Any future proposal
of the form "verify further, then re-instantiate" is refuted by citation.

**Killed-approach log.**  Two candidates were checked against the repository
before `RouteCap` was chosen and both were already covered: (i) the mod-`3`
filter — `S(n) mod 3` is exactly the parity of the preceding valuation, so the
mod-`3` orbit carries no information beyond the valuation word, which
`GapBarriers.exists_realizer` shows is arbitrary; this is already
`Structure.CycleModThree.accStep_mod_three_of_odd` and `BcapSharp.leaf_vacuous`.
(ii) A `3`-adic Lyapunov quantity on orbit points — vacuous for the same reason,
since every point after one odd step is coprime to `3`, so `v₃` is identically
`0` along the orbit.  Neither is new; recording them keeps the next round from
re-deriving them.

`lake build Collatz` succeeds, **348 jobs**; `scripts/check_integrity.sh` passes,
now also guarding `Frontier9971.length_ge_9971`,
`Search.reachesOne_of_lt_2011136` and `RouteCap.route_misses_a_length`.
Zero `sorry`, zero added axioms.

### Next session — three tasks, one primary

1. **Primary.**  Sharpen `reach_lt_six_mul` from `a < 6c` toward the measured
   law without importing Baker.  The tractable half is the *lower* bound on
   `2 · 2 ^ fexp a − 3 ^ a` along the `306 + 665k` staircase, where
   `Strategy.PosLadder` already derives the semiconvergent structure of
   `log₂ 3`; a rung-restricted `a² < K · c` would be strictly stronger than
   anything currently proved and needs no external theorem.
2. Extend the range to `2 403 661` and unlock `length_ge_11025`.  Purely
   mechanical — `338` blocks bought `1054` of frontier here, and the next riser
   needs `384` more blocks — but by task 1 it buys one rung, not a programme.
3. Audit which of the fifteen `*_of_heavy` consumers actually improve at window
   `6290` rather than `5625`; the window widened but nothing downstream was
   re-derived at the new reach.
