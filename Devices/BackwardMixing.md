# One node's children hit every class mod `3^k` exactly once

*Round LXXVIII.  Companion to `Devices/StochasticTree.md`.  Lean:
`Strategy/BackwardMixing.lean`; measurements: `scripts/backward_cover.py`,
`scripts/phase_word.py`, `scripts/syracuse_lift.py`, `scripts/syracuse_test.py`.*

**Novelty tag: NEW (structural).**  In one sentence: *the inverse Syracuse
tree is exactly 3-adically equidistributed at every node and every level — the
`i`-th child's class modulo `3^k` runs over `ℤ/3^k` bijectively and
`3^k`-periodically in `i` — so the 3-adic imbalance that costs
Krasikov–Lagarias its exponent is a truncation effect, not a structural one,
and it is measured here to cost only a polynomial factor in scale.*

Searched.  Repository: the injectivity half is the *open* Lean statement of the
Round LXXVI gap list (`RESEARCH.md` §E, "backward mixing"), and the exact order
of `4` modulo `3^(k+1)` is the Round LXXVI next-round item 3;
`TreeBranching.phase` and `ClassChild.child_mod_pow` are the `k = 1, 2` shadows
of it.  Literature: K–L 2003 and Applegate–Lagarias 1995 use the class
transition `r ↦ (2^v r − 1)/3` but state no per-period bijection; the fact that
`4` generates the index-`2` subgroup of `(ℤ/3^(k+1))ˣ` is classical, its use as
an exact equidistribution statement for the inverse tree is not recorded here
or, as far as this session could check, there.

## 1. The theorem (kernel-checked)

`Strategy/BackwardMixing.backward_mixing`, axioms `propext, Quot.sound`:

> For every odd `a` prime to `3` and every `k`, the map
> `i ↦ child a (v₀ a + 2i) mod 3^k` is a **bijection** of `{0,…,3^k−1}` onto
> `ℤ/3^k`, and it is `3^k`-periodic in `i`.

Removing the `3^(k−1)` classes divisible by `3`: the *fertile* children of any
node, listed by increasing valuation, hit each of the `2·3^(k−1)` fertile
classes modulo `3^k` **exactly once per period of `2·3^(k−1)` fertile
children**.

*Proof, in one line.*  The admissible valuations are `v₀ a + 2i`, so the
multiples are the geometric progression `4^i · base a`; `4` generates
`{u : u ≡ 1 (mod 3)}`, the index-`2` subgroup of `(ℤ/3^(k+1))ˣ`, of order
exactly `3^k`; and `s ↦ (s−1)/3` carries that subgroup bijectively onto
`ℤ/3^k` (`ClassChild.child_mod_pow`).

Supporting lemmas, all from the core `Nat` API: `four_pow_three_pow` (the sharp
lift `4^(3^j) = 3^(j+1)c + 1` with `c ≡ 1 mod 3`, from the repository's
`cube_three`), `one_add_pow` (`(A+1)^e = eA + A²w + 1`), `cancel_three_pow`
(a factor prime to `3` cancels from a power of `3`), `four_pow_ne_one`
(**the exact order of `4` modulo `3^(k+1)` is `3^k`** — the Round LXXVI item),
and `inj_on_range_surj`, a from-scratch pigeonhole.

## 1b. The same theorem in one line: `4c + 1` is a full cycle

`BackwardMixing.child_succ`: the next admissible child is `4c + 1` — the
classical "`n` and `4n+1` have the same Syracuse successor" — so a node's
children *are* the forward orbit of the affine map `τ c = 4c + 1`, and the
theorem reads

> **`BackwardMixing.tau_cycle`: `τ c = 4c + 1` acts on `ℤ/3^k` as a single
> `3^k`-cycle, from any starting point.**

(Because `3·τ^i(c) + 1 = 4^i·(3c + 1)` and `3x + 1` modulo `3^(k+1)` sees `x`
only modulo `3^k`.)  This is the memorable form: the inverse Syracuse tree
branches by iterating `4c+1`, and that map is a `3^k`-cycle at every level.

## 2. The `k = 2` face: a universal word

`phase n ∈ {0,1,2}` (`TreeBranching`) is the slot residue mod `3` whose child
is infertile.  The `9` classes mod `9` split as `3` infertile plus `2` per
phase, so the bijection at `k = 2` says the phase sequence of the children over
`9` consecutive slots is always a **rotation of one universal word**

    W  =  2  0  X  1  1  X  0  2  X                    (X = infertile)

with the rotation determined by `n mod 27`; all `9` rotations occur, two
fertile classes mod `27` each (`scripts/phase_word.py`).  In particular every
node's `9`-slot phase word has counts `(2,2,2)`: **per period the inverse tree
is exactly phase-balanced.**  `W` is a palindromic necklace — its reverse is
its rotation by `8` — with the infertile letters at `i ≡ 2 (mod 3)` and the
fertile pairs `(2,0), (1,1), (0,2)` in the three blocks.

So the hypothesis `Equi` of `Strategy/TreeBalance9` (mod-`9` balance of the
tree of `1`, the object G8) is *not* a statement about which phases the tree
produces — over a period it produces each exactly twice, always.  It is a
statement about how the geometric slot weights `2^(−v)`, which put `3/4` of
the mass on the first slot, truncate the rotations.

## 3. Why the period is not the end of the story

One generation costs a full period: valuation `2·3^k`, scale `4^(3^k)`.
Exponential in the modulus, so useless directly.  The **subtree** does
exponentially better, and this is where the `1/k` law of
`Devices/StochasticTree.md` comes from.  `scripts/backward_cover.py`,
best-first search over the actual descendants of a root `a`:

| quantity | one generation | subtree (measured) |
|---|---|---|
| total valuation to cover `ℤ/3^k` | `2·3^k` | `≈ 5k` |
| scale `X/a` to cover `ℤ/3^k` | `4^(3^k)` | `Θ(M log M)`, `M = 3^k` |

Covering scales, `log_M(X/a)`, for roots `1`, `1234567`, `10^11−23` at
`k = 6,7,8,9`: `1.31, 1.30, 1.31, 1.28` · `1.37, 1.27, 1.27, 1.19` · `1.43, 1.45,
1.40, 1.30`; and `X/(a·M·log M) = 0.16 … 4.05`, bounded, no trend.
`M log M` is exactly the coupon-collector scale for a set of counting exponent
`1` equidistributed modulo `M`: **the tree's 3-adic covering is as fast as a
density-one set would manage.**  The obstruction is in the multiplicities, not
in the support.

## 3b. Per-root balance: the computable shadow of G8

`Equi` is about the tree of `1`, which below `10^9` is every integer, so it
cannot be tested.  The subtree of one large root **is** a genuine thin
inverse-closed set — the root `10^11 − 23` has only `1.9·10^6` descendants
below `10^18` — and its balance is exactly the per-root statement
`Devices/StochasticTree.md` §5 sketch 3 asked for.  `scripts/tree_perroot.py`
enumerates the descendants of `a` below `a·Y` and reports, for each modulus,
`min/max` of the class counts against their mean and
`χ := max |count − mean| / √mean`.

At `Y = 10^7` (`k = 1,2,3,4`, i.e. moduli `3, 9, 27, 81`):

| root | descendants | `χ` | worst relative deviation |
|---|---|---|---|
| `1` | `1 979 312` | `0.06, 0.22, 0.21, 0.68` | `0.36 %` |
| `25` | `1 693 382` | `0.29, 1.06, 2.08, 2.93` | `1.7 %` |
| `1234567` | `4 019 372` | `0.14, 0.43, 2.29, 2.31` | `0.85 %` |
| `10^11 − 23` | `1 937 402` | `0.06, 0.60, 1.33, 2.01` | `1.1 %` |

`χ` stays `O(1)` — never above `3.5` — across `Y = 10^2 … 10^7`, five orders of
magnitude and four moduli.  That is the signature of exact equidistribution
with `√N` fluctuation, not of a residual bias.  In particular the mod-`9`
deviations are `≤ 0.2 %` at `Y = 10^7` against the `3 %` that `Equi` allows
(`Equi` asks each class mod `9` to carry `≥ 1/3 − 1/100` of its class mod `3`).

Honest scope: this is the *per-root* statement, not `Equi`, which is a claim
about `T ∩ [1,X]` as a union over all roots; and the roots tested are small
against `X`.  But it is the first evidence in this repository about the
3-adic behaviour of thin inverse-closed sets, and it says the min-over-lifts
adversary of Krasikov–Lagarias is not realised by any root tested.

## 4. What this kills

The Perron vector of the lift-averaged K–L system at exponent `1`
(`StochasticTree` Theorem A) is now identified explicitly.  Let

    μ_n := law of  Σ_{m=1}^{n} 3^(m−1) 2^(−(a_1+⋯+a_m))  mod 3^n,
    a_i iid with P(a = j) = 2^(−j) —

Tao's Syracuse random variable `Syrac(ℤ/3^n)` (Forum Math Pi 10 (2022), §1.3).
It obeys `μ_(k+1)(r) = Σ_v 2^(−v) μ_k(childClass k v r)`, i.e. `A_1 μ = μ`
exactly, and it projects consistently, `Σ_lifts μ_n = μ_(n−1)`
(`scripts/syracuse_lift.py`, projection error `≤ 1.4·10^(−18)` to `n = 12`).
So **the K–L weights at exponent `1` are the Syracuse random variable**, and
the natural route "prove Tao-style equidistribution of `Syrac(ℤ/3^n)`, get
K–L exponent `→ 1`" is available in principle.  Measured, it is dead:

| `n` | 2 | 4 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|---|
| `β_n` = 3·min lift share | .2857 | .3585 | .3721 | .3770 | .3792 | .3798 |
| `γ_n` = 3·max lift share | 1.5714 | 1.5342 | 1.5223 | 1.5150 | 1.5137 | 1.5131 |
| mean lift oscillation | 1.286 | .921 | .703 | .567 | .472 | .400 |

`β_n` is nondecreasing and `γ_n` nonincreasing — immediate, since the lift
shares at level `n` are convex combinations of reflected level-`(n−1)` shares
— and they converge to `≈ 0.3798` and `≈ 1.5131`, **not to `1`**.  So
`Syrac(ℤ/3^n)` is *not* lift-equidistributed in `L^∞`; only the mean
oscillation decays, and only like `n^(−0.65)`.  Used as a K–L test vector
(`scripts/syracuse_test.py`) `μ` certifies

    rho_k(1) ≥ β_(k+1) ≥ 0.2857   (level-uniform, unconditional)

and exponent `α ≈ 0.077` at best, falling to `0` by level `7` — against the
true `ρ_k(1) = 0.875` and `α_k = 0.80` at the same level.  **The `1/k` law is
therefore not the equidistribution of the Syracuse random variable**; the
min-system reaches criticality by reweighting away from `μ` onto the classes
where the lift shares are good.  Killed: the `L^∞` route.

One number is explained, though: `γ_∞ ≈ 1.5131` against the max-relaxation
ghost's measured growth `1.50` at every level (`StochasticTree` §4) — the
ghost's constant is the worst lift share of the Syracuse law.

## 4b. The 2-adic mirror: anti-mixing (kernel-checked)

The 3-adic statement is as strong as it could be; the 2-adic one is as weak as
it could be, and for the same reason `3·child + 1 = 2^v · a`.  Modulo `2^M` the
right side vanishes as soon as `v ≥ M`, so

> `BackwardMixing.deep_child_congr`: for **any** two nodes `n, m` and any
> admissible valuations `v, w ≥ M`, `child n v ≡ child m w (mod 2^M)`.

Every child taken at valuation `≥ M`, from every node at once, sits in the one
class solving `3c ≡ −1 (mod 2^M)` — `1, 1, 5, 5, 21, 21, 85, 85, …` for
`M = 1…8`.  So a node's children occupy at most `⌈(M − v₀)/2⌉ + 1` classes
modulo `2^M`, against **all** `3^k` classes modulo `3^k`.

That asymmetry is the reason G1 (mixing modulo `2^M`) is a different kind of
problem from backward mixing modulo `3^k`: mod `3` the spread is per-node and
immediate, mod `2` it can only come from depth.  It also says the two "local
blindness" phenomena of `Strategy/LocalBlindness` have different mechanisms at
the two primes, which that theorem's uniform statement does not distinguish.

## 5. Where the wall is, stated exactly

Within one generation the tree is diagonalised by the *multiplicative*
characters of `(ℤ/3^(k+1))ˣ`: the per-period bijection of §1 is character
orthogonality applied to `4^i · base a`, and for a multiplicative `χ` the
weighted slot sum `Σ_i q^i χ(4^i · base a) = χ(base a) Σ_i (qχ(4))^i` factors,
its root-dependence a single scalar.  Across generations the child map
`u ↦ (u−1)/3` is affine, not multiplicative, so the factorisation dies at
depth `2`.  **The interference of the multiplicative structure at `2` and `3`
with the additive `+1` is the whole of the residual obstruction**, and it is
the same object as the ternary-digit questions of Lagarias 2009.

## 6. Where this leaves G6 and G8

* G6: unchanged as a scalar (`0.852` computer-verified, `7/10` kernel-checked).
  Its mechanism is now fully described: exact per-node equidistribution,
  truncated by the geometric slot weights, recovered by the subtree at
  polynomial scale cost `M^(≈1.3)`.
* G8 (`Equi`): sharpened twice.  It is *not* about which classes the tree
  produces (§2), and it is *not* implied by any `L^∞` statement about the
  Syracuse random variable (§4).  What remains is a statement about
  multiplicities under the geometric weights, i.e. about the affine map
  `u ↦ (u−1)/3` composed with multiplication by `2^v` — §5.
* The measurement of §3 is the first *unconditional* quantitative evidence
  about the tree of `1`'s own 3-adic behaviour above the verified range that
  is not a restatement of the conjecture: it is a covering statement, and
  covering is strictly weaker than balance.
