# Formalized: the odd-map gap audit

Module: `Collatz/Strategy/GapBarriers.lean` (namespace `Collatz.GapBarriers`).
Lean 4.33.0-rc1, no Mathlib, no `sorry`, no project `axiom`, no `native_decide`.

**Audit.**  All 197 theorems across `GapBarriers`, `OddClock` and `Paradoxical`
were checked with `#print axioms`: 125 depend on `[propext, Quot.sound]`, 18 on
`[propext, Classical.choice, Quot.sound]`, 10 on `[propext]`, and 44 on **no
axioms at all**.  No `sorryAx` appears anywhere.  (Five `private` lemmas are not
addressable from outside their modules and are excluded.)

The map here is the **odd-to-odd** accelerated map `T(n) = (3n+1)/2^{v₂(3n+1)}`,
*not* the Terras halving map `acceleratedStep` used elsewhere in the repo.
A step is a relation, `OddStep n k m := 1 ≤ k ∧ m % 2 = 1 ∧ 2^k * m = 3n+1`,
so no 2-adic valuation function is ever defined; existence and uniqueness are
proved (`oddStep_exists`, `oddStep_unique`).

## Proved

| Note | Lean |
|---|---|
| Lemma 2.2 — `v₂(3n+1)=1 ⟺ n≡3 (4)` | `oddStep_k_one_iff` |
| Lemma 2.2 — `v₂(3n+1)≥2 ⟺ n≡1 (4)` | `oddStep_two_le_iff` |
| Lemma 3.1 — a valuation-1 step always ascends | `lt_of_k_one` |
| Lemma 3.2 — `T(n)<n ⟺ 3n+1 < 2^k·n` | `oddStep_lt_iff` |
| Lemma 3.2 — for `n ≥ 3`, `T(n)<n ⟺ k ≥ 2` | `oddStep_lt_iff_two_le` |
| exact affine identity `2^{K_L}n_L = 3^L n_0 + b`, `b ≥ 1` | `traj_affine` |
| exact product estimate `2^{K_L}N^L n_L ≤ (3N+1)^L n_0` | `traj_product` |
| G9 — cycles satisfy `3^L < 2^{K_L}` | `cycle_three_pow_lt` |
| G9 — cycle squeeze `2^{K_L}N^L ≤ (3N+1)^L` | `cycle_min_bound` |
| G11 — non-descending stretch: same bound | `noDescent_product_bound` |
| Thm 5.4 — the only 1-cycle is `n=1, k=2` | `cycle_length_one` |
| Lemma 5.3 — a run of `L` ones forces `2^L ∣ n₀+1` | `ones_two_pow_dvd`, `ones_run_le` |
| Thm 4.1 / G1 — the ascent family, `2^{L+1}-1 → 2·3^L-1` | `ascChain_*`, `excursion_unbounded` |
| G7 / Gap 5 — coefficient stopping time unbounded | `coefficient_stopping_time_unbounded` |
| G8 / Gap 6 — no `φ` with `B n^e ≤ φ(n)^d ≤ A n^e` descends | `no_power_descent` |
| exact accumulator `Sacc`, `2^{K_L}n_L = 3^L n_0 + S` | `traj_affine_exact` |
| `S ≥ 3^L − 2^L` (subtraction-free) | `Sacc_lower` |
| small cycles force `2^K/3^L` away from 1 | `cycle_delta_lower`, `traj_delta_lower` |
| **every** cycle has mean valuation `≤ 2`: `2^{K_L} ≤ 4^L`, `K_L ≤ 2L` | `cycle_two_pow_le`, `cycle_Ksum_le` |
| a cycle with least element `≥ 3` satisfies `2^{K_L}·3^L ≤ 10^L` | `cycle_two_pow_le_of_three_le` |
| the admissible-`K` window criterion | `admissibleK`, `hasAdmissibleK`, `no_cycle_of_no_admissibleK` |
| a cycle through `1` is all `1`s | `traj_one_of_start_one` |
| only 1-cycle is `n=1,k=2`; only 2-cycle, 3-cycle trivial | `cycle_length_one/two/three` |
| no 4-cycle (window criterion alone) | `cycle_length_four_trivial` |
| composition enumerator and its completeness | `cycleScan`, `cycleScan_complete` |
| **no nontrivial cycle with at most ten odd steps** | `no_short_cycle` |
| the circuit equation `(2^K − 3^L)·n₀ = 3^L − 2^L` | `Sacc_ones_prefix`, `circuit_equation` |
| **no nontrivial circuit with at most 100 odd steps** | `no_circuit_below_101` |
| the circuit band `3^L < 2^K < (4/3)·3^L`, holding at most one `K` per length | `circuit_band`, `circuit_band_unique` |
| `Sacc` under one big valuation; **no such cycle at length ≤ 12** (two local minima) | `Sacc_oneBig`, `no_oneBig_below_13` |
| no cycle has *every* non-final valuation `≥ 2` beyond length 3 | `no_all_big_pattern` |
| the pattern checks are **not vacuous** — divisibility does fire, `n₀ ≥ 3` rejects it | `circuit_check_nonvacuous`, `oneBig_check_nonvacuous` |
| Lemma 2.3 — `v₂(3n+1)=k ⟺ 3n+1 ≡ 2^k (mod 2^{k+1})` | `oddStep_iff_mod` |
| Lemma 2.3 — explicit residue `n ≡ r_k (mod 2^{k+1})` | `rk`, `oddStep_iff_rk`, `rk_table` |
| Lemma 2.4 — the valuation prefix is a function of `n mod 2^{K+1}` | `traj_congr`, `valuations_determined` |
| Lemma 2.4, realization — **every** valuation vector occurs | `exists_realizer`, `parity_vector_correspondence` |
| the all-ones class `n ≡ −1 (mod 2^{L+1})` is realized in full | `ascT`, `ones_run_of_class` |
| bridge: one odd step = `k` Terras steps | `oddStep_acceleratedOrbit`, `traj_acceleratedOrbit` |
| one odd step = exactly one tripling; counters match | `oddCount_add`, `oddStep_oddCount`, `traj_oddCount` (in `OddClock.lean`) |
| Remark 5.1 — the two clocks give the same paradoxical set | `paradoxical_iff_oddClock` |
| Gap 8 — count of valuation-`≥2` steps is capped | `bigCount_bound`, `bigCount_bound_three`, `bigCount_ten` |
| Gap 6 — no `c(n mod 2^M)·n` descends, any `M`, any `c` | `no_local_descent` |
| integer mean-value bound `(a+1)^{L+1} ≤ a^{L+1} + (L+1)(a+1)^L` | `pow_succ_le` |
| the shared arithmetic core, with a lower bound supplied | `min_upper_of_squeeze_gen`, `min_upper_of_squeeze` |
| a cycle's least element obeys `3^L·N ≤ (L+1)·10^L` | `cycle_min_upper` |
| the same bound for paradoxical pairs (Corollary 4.4, `Nat` form) | `OddClock.paradoxical_min_upper` |
| *(conditional on the cited Barina range `704·2^60`)* a nontrivial cycle has ≥ 42 odd steps | `cycle_length_ge_42` |
| the same from the repository's **own kernel-proved** range `1 086 464` — ≥ 12 odd steps | `cycle_length_ge_12_of_verified` |
| **≥ 12 odd steps, unconditionally** — hypothesis discharged from `verified_1086464` | `CycleVerified.cycle_length_ge_12` |
| ≥ 2966 odd steps, unconditionally — the admissible-exponent window at the verified scale *(superseded; cross-check only)* | `CycleVerified.cycle_length_ge_2966` |
| ≥ 6809 accelerated steps (odd budget 4296), unconditionally — pre-existing | `RealizableFrontier6809.length_ge_6809` |
| ≥ 7863 accelerated steps (odd budget 4961), unconditionally | `Frontier7863.length_ge_7863` |
| **≥ 8917 accelerated steps (odd budget 5626)** — the strongest *unconditional* cycle bound in the repository | `Frontier8917.length_ge_8917` |
| a cycle's Terras orbit is periodic; a cycle above `2` never reaches `1` | `cycle_accOrbit_period`, `not_accReachesOne_of_cycle` |
| **the `41.5%` valuation-one bound, unconditional for cycles** (`0.415037` vs the asymptotic `0.4150375`) | `cycle_bigCount_bound` |
| in a cycle of the minimum length `12`, at least five valuations are exactly `1` | `cycle_twelve_bigCount` |
| Terras `σ ≥ κ` on the odd clock | `traj_no_drop_of_coeff_le`, `no_drop_before_coeff` |
| **Terras Conjecture 2.9 machine-checked for odd `2 ≤ n ≤ 999`** | `cst_below_1000`, `cstUpTo_999` |
| `κ ≤ σ` on the odd clock, unconditional; both halves side by side | `oddCoeffStoppingTime_le`, `cst_two_sided` |
| bounded least-witness search with a spec; computed `σ`, `κ` | `firstSuch`, `sigmaOdd_spec`, `kappaOdd_spec` |
| predecessors: exist iff `2^k·m ≡ 1 (mod 3)`; parity of `k` forced by `m mod 3` | `exists_pred_iff`, `pred_valuation_parity` |
| multiples of three are leaves of the backward tree | `no_pred_of_three_dvd` |
| the backward tree branches infinitely at every other odd node | `exists_pred_large` |
| the image of the odd map is exactly the odd `m` with `3 ∤ m` | `exists_pred_iff_image` |
| the predecessors of `1` are the base-4 repunits `1, 5, 21, 85, …` | `predOne`, `oddStep_predOne` |
| a **computable** odd map, and constructive trajectories | `oddT`, `oddK`, `oddStep_oddT`, `exists_traj` |
| any non-rising stretch has already made the coefficient exceed | `coeff_gt_of_no_rise` |

`Collatz/Strategy/CoefficientStopping.lean` treats the same map with the
bookkeeping sequences supplied as hypotheses rather than defined; the module
docstring of `GapBarriers` carries the correspondence table
(`orbit_identity ↔ traj_affine_exact`, `cycle_coeff_gt ↔ cycle_three_pow_lt`,
`no_drop_of_coeff_le ↔ traj_no_drop_of_coeff_le`).  Neither module imports the
other.

The strongest cycle-length bound in the repository is **not** any of these.  When
this was written it was the pre-existing `RealizableFrontier6809.length_ge_6809`,
which at the same verified range `1 086 464` gives an odd-step budget of `4296`
against the `2966` here; it has since been superseded by
`Frontier8917.length_ge_8917`.

A stronger bound exists but is **conditional**:
`VerifiedRange.cycle_length_ge_40001_of_barina` assumes `BarinaVerified` and
gives `40 001`.  Its constant is where the sweep was stopped, not a frontier, so
it would move further with more computation.

`cycle_length_ge_2966` is retained as an independent cross-check, and is
documented as such.  Its mechanism is the classical Diophantine squeeze, kept
exact in `Nat`: `cycle_three_pow_lt` and `cycle_min_bound` together confine the
halving total to `3^L < 2^K ≤ (3 + 1/N)^L`, a window of multiplicative width
`(1 + 1/(3N))^L`.  At `N ≥ 1086464` the per-step slack is `3.068·10⁻⁷`, so the
window admits a power of two only for exceptional `L`, and `windowScanFast_verified`
checks in the kernel that none does below 2966.  Every inequality is an exact
`Nat` comparison and the scan depends on no axioms.

The value of keeping it is corroboration, not strength.  The scan reaches its
first admissible lengths at `2966` and `3631` — precisely the riser indices in
`RealizableFrontier6809`'s staircase table — from a completely different
inequality, with no Beatty ceiling and no certificate.  Two independent routes
land on the same staircase of convergents of `log₂ 3`.  Quantitatively the gap is
exact: the product bound `2^K·N^L ≤ (3N+1)^L` used here at `N = 1086464` yields
what that file's certificate already yields at `c = 620859`, so the weaker
inequality wastes the whole range above `620859`.

### The next rung, taken

`Frontier7863.length_ge_7863` and `Frontier8917.length_ge_8917` improve the
repository's headline cycle bound from `6809` to `7863` and then `8917`,
unconditionally and with no new mathematics.  It is an
instantiation of `length_ge_of_cert` at `(c, A, F) = (1 358 718, 4961, 7863)`,
and it is short because the other two inputs were banked in advance: the
certificate `PreCertified.cert_4961` and the gap `pow_gap_4961` were proved
before any verified range supported them.

The one new ingredient is the range.  `Search.VerifiedRung7863` sweeps `266`
further blocks to `1 358 848`, the first multiple of `1024` past the riser
`G(4296) = 1 358 717`.  That sweep needs fuel `224` rather than `200` — a direct
scan of `[1 086 464, 1 358 718)` puts the worst drop time at `224`, reached at
`n = 1 126 015` — and the earlier `1061` blocks are carried up to the new fuel
without recomputation by `Search.FuelMonotone.dropsWithin_mono`.  That
monotonicity is the piece `VerifiedExtended` had been able to do without, and
could not be avoided once the sweep crossed block `1099`.

The second rung repeats the pattern at `1 665 024`, past `G(4961) = 1 664 598`,
and needs no fuel change: the worst drop time in `[1 358 848, 1 665 024)` is
`214`, below the `224` already forced by the previous range.  Drop times are not
monotone in the range, so the fuel must be measured per range rather than
extrapolated.

Climbing stops here by choice rather than obstruction.  Each further rung is
mechanical and buys a fixed `+1054` for a linearly growing kernel cost;
`PreCertified` has certificates banked to `A = 8286` (frontier `13133`) whenever
the ranges are wanted.  The improvement recorded here came from the
infrastructure — banking certificates ahead of the range, stating the frontier
theorem once, and fuel monotonicity — rather than from the climbing.

### The frontier theorem, stated once

`Strategy.FrontierParametric.length_ge_of_cert` states the cycle-length frontier
over `(c, A, F)`, separating its three inputs: the certificate reaching `A`, the
gap `2 ^ (F−1) < 3 ^ A`, and the verified range `c`.  Only the last needs
verified computation; the first two are banked in `PreCertified`.
`length_ge_6809_again` recovers the existing headline bound by instantiation,
which both checks that the general form subsumes the hand-written one and
witnesses that the conditional shape is inhabitable rather than vacuous.

The banked rungs then appear as honest conditional statements
(`length_ge_7863_of_verified` and friends): *if* the verified range reaches the
threshold, the frontier follows.  Extending the range is now the single missing
ingredient — the certificate, the gap and the plumbing are all in place.

### The ladder, banked ahead of the range

`Strategy.PreCertified` records the certificate and the exponent gap for the next
six rungs — reaches `4961` through `8286`, frontiers `7863` through `13133`, at
the exact least ranges `1 358 718` through `3 380 808`.  These are kernel
computations that do not depend on the verified range, so they can be done now
and redeemed later: the day a range extension lands, the corresponding frontier
follows with no further certificate work, and by `CertMonotone.cert_mono_c` a
range merely at least as large as the threshold suffices.

The rungs are `306 + 665k`, the one-sided semiconvergent staircase of `log₂ 3`
that `Strategy.PosLadder` derives independently of any of this.  The reach moves
only on that staircase and never between rungs, which is why the ladder has
risers and no slope.

No cycle bound beyond `6809` is claimed.  Each banked rung needs `VerifiedBelow c`
for its threshold, which this development does not have.

### The verified range is the binding constraint, not the method

The certificate `RealizableBound.cert` is parametric in the verified range `c`,
and `CertMonotone.cert_mono_c` proves it is monotone in it: raising `c` never
invalidates a certificate already proved.  (`cert_barina_4296` is the immediate
corollary — the 4296-index certificate transfers to Barina's range with no
recomputation.)  So the frontier ladder only ever moves upward, and past work is
never invalidated by a range extension.

What that ladder would give at Barina's `704·2^60` is worth stating, **as a
numerical estimate and not as a theorem**.  Reproducing the published staircase
exactly (`307200→1636`, `620859→2966`, `1086055→4296`, `1358718→4961`) and then
continuing it by best-approximation theory for `log₂ 3` gives a reach of about
`7.2·10^10` odd steps, i.e. a frontier near `1.14·10^11` accelerated steps.

Two reasons this is an estimate.  It approximates the accumulated quantity
`Bcap i / 3^i` by its mean `0.24045·i` rather than bounding its fluctuation, and
it assumes the first failing index is a semiconvergent denominator of `log₂ 3` —
true by best-approximation theory, but not proved here.  It is also
unformalizable as it stands: `cert` would need evaluating at some `7·10^10`
indices on integers of roughly `3.4·10^10` digits, which is beyond the kernel and
beyond any scan.  An independent check from the window scan of
`CycleVerified` puts the same quantity at `~4·10^10`, the same order.

The honest summary is that this method's reach is set by the verified range, and
that closing the remaining distance is a computation nobody can run, not a proof
anybody is missing.

`no_short_cycle` remains of independent interest: it is unconditional and self-contained — no
verified numerical range is assumed and no Diophantine-approximation input is
used.  The mechanism is that `3^L < 2^{K_L} ≤ (10/3)^L` leaves a window of width
only `0.152·L`, so at most one or two total valuations `K` are possible per
length, and the compositions of each are then checked exhaustively by kernel
evaluation.  (`L = 11` is still out of reach; the check does not finish in two
minutes.)

`no_power_descent` is the strongest of the barrier results: with `d=e=1` it rules out every
`φ(n) = c(n mod 2^M)·n`; with `d=2, e=1` it rules out `√n`; with arbitrary `e/d`
it rules out every rational power, locally reweighted or not.

## Not formalized (and why)

* **G2/G3** (the exponent `ψ(s) = 3^s/(2^{s+1}-1)`, `s* = 0.438`, rate `0.9465`)
  — needs real exponents.
* **G10** (the continued-fraction step from `cycle_min_bound` to
  `ℓ ≥ 6 586 818 670`) — needs `log 2`, `log 3` and best-approximation theory.
  The *algebraic input* to it, which is the whole `Nat` content, is
  `cycle_three_pow_lt` + `cycle_min_bound`.
* **G5** (`⋂E_ℓ ∋ −1` in `ℤ₂`) — needs `ℤ₂`.

## Not claimed

Nothing here proves or assumes Collatz, the absence of divergent orbits, or the
absence of nontrivial cycles. `no_power_descent`, `coefficient_stopping_time_unbounded`
and `excursion_unbounded` are **barrier** results: they say named methods cannot
work, not that the conjecture is false.


---

## State of play

Where this leaves the two statements the audit set out to test.

**Statement B (no nontrivial cycle) — not proved, but the finite results moved.**
The cycle-length frontier went from `6809` to `8917` accelerated steps
(`Frontier8917.length_ge_8917`), unconditionally and with no new mathematics: the
gain came from banking certificates ahead of the verified range, stating the
frontier theorem once over `(c, A, F)`, and proving fuel monotonicity so an
extended sweep need not re-verify the blocks already done.  Measured build cost
shows why that decomposition matters — the block sweeps cost `261s` and every
certificate in `PreCertified`, covering six rungs out to frontier `13133`, costs
`6s`.  Ranges are the whole expense; certificates are free.

This does not approach a proof.  `PROGRAM_STATUS` records that the range needed
to kill the `k`-th rung grows like `a_k·a_{k+1}/(6 ln 2)`, which diverges, so no
finite verified range excludes all cycle lengths; an independent estimate here
puts the reach at Barina's `704·2^60` at only about `7·10^10` odd steps.  Two
rungs change none of that.

**Statement A (no divergent orbit) — untouched by this work.**  Nothing here
bears on divergence.

So the conclusion of the audit is unchanged: this line of attack is incomplete,
and the incompleteness is structural rather than a matter of more computation.
