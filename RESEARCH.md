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
neither a magnitude estimate nor a congruence class.  It excludes every one-run
cycle with `a ≤ 200000`, uses **no verified range**, and is Baker-free.  Its
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
