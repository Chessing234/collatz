# Device: the dyadic corona pairing

Agent 3 — 2-adic / real hybrid geometry.

Not a residue-class list.  Not a translate clock `v₂(n+5)` or `v₂(11n+19)`.
Not a frozen window of length `L`.  The scale is a function of real size.

No Collatz claim is made.  Heavy coronas expand (27, 31, Mersenne prefixes).
The pinch below kills only the strongly light ones.

---

## Exact definition

At every positive integer there are two simultaneous objects: the archimedean
size `|n|` and the 2-adic point `n ∈ ℤ₂`.  Pair them at a **dynamic** scale

    κ(n)  :=  ⌊log₂ n⌋

selected by the real magnitude, not prescribed in advance.  The hybrid state is

    S(n)  =  ( n ,  n mod 2^{κ(n)} )  ∈  ℕ  ×  ℤ/2^{κ(n)}ℤ.

Write `mantissa(n) := n mod 2^{κ(n)}`.  Because `n` lies in the dyadic annulus
`[2^{κ(n)}, 2^{κ(n)+1})`, the high part at this scale is identically the unit:

    n  =  2^{κ(n)}  +  mantissa(n),     highPart_{κ(n)}(n)  =  1.

That is the geometry: real size *is* the 2-adic precision, and the remaining
2-adic coordinate is a proper residue at that precision — a different modulus
for every dyadic annulus.  A list of classes modulo a frozen `2^L` cannot
express this, because `L` here moves with `|n|`.

A companion scale, still a function of `|n|`, is the midscale pinch window

    π(n)  :=  ⌊κ(n)/2⌋.

The **strongly light** predicate at a window of length `k` is

    StronglyLight(n, k)  :⇔  2 · 3^{oddCount(n,k)}  ≤  2^k.

The factor `2` is not a fudge: it is the exact matching of `affineC < 2^k·3^a`
against the corona lower bound `n ≥ 2^k`.

Lean: `Collatz.Strategy.DeviceHybrid`.

---

## The two arrows

The accelerated map `T` is `n/2` on evens and `(3n+1)/2` on odds.

**1. Real expansion forces 2-adic localisation.**
After `κ(n)` steps the corona identity is

    T^{κ(n)}(n)  =  3^a  +  T^{κ(n)}(mantissa(n)),

`a = oddCount(n, κ(n))`, which is a function of the mantissa alone
(`stronglyLight_of_mantissa`).  Non-drop `T^{κ(n)}(n) ≥ n` rewrites as

    2^{κ(n)} + mantissa(n)  ≤  3^a + T^{κ(n)}(mantissa(n))

(`expansion_localizes`).  A real lower bound has become a lower bound on the
odd-density of a 2-adic window whose length was chosen by `|n|`.

**2. That localisation forces future real contraction — when it is strong.**
If the window is strongly light, the same identity yields

    T^{κ(n)}(n)  <  n

(`light_corona_drops`).  Proof: `affine_exact` plus `affineC_lt` give
`C < 2^κ·3^a`, strong lightness gives `3^a ≤ 2^κ − 3^a`, and the corona
supplies `n ≥ 2^κ`, so `C < n·(2^κ − 3^a)`.

This is the even branch `x ↦ x/2` being consumed.  It is not a valuation of a
fixed translate, and it is not a statement about a frozen modulus.

The midscale form `light_pinch_drops` is the same pinch at `π(n)`, where the
high part is at least `2^{π(n)}` rather than `1`.

---

## What this knows about a single orbit that the parity word does not

Terras: a word of length `k` *is* a residue class modulo `2^k`, realised by
some `r < 2^k`.  On that fibre the magnitude is free (`ScaleFibre.fibre_affine`:
rank one, `E(w)/n`).

At the corona the fibre is **not free**.  The window length is `κ(n)`, so the
Terras representative would have to satisfy `r < 2^{κ(n)} ≤ n`.  The integer
under study is the *unique* lift of its mantissa into the next dyadic annulus.
You cannot vary the starting integer independently of the word length: they are
locked by `|n|`.

Three concrete data the free word does not carry:

1. **Which modulus is being read.**  `κ(n)` is not a letter of the word.
2. **The unit high part.**  `highPart_{κ(n)}(n) = 1` is an archimedean fact.
   At a frozen `L` the high part is the free coordinate `HighPart` already
   analysed; here it is frozen to `1` by the choice of scale.
3. **The jump of scales along one orbit.**  After `κ(n)` steps the landing
   `3^a + T^κ(mantissa)` has a *new* corona scale `κ(T^{κ(n)}(n))`.  The
   hybrid state maps coronas to coronas.  A single parity word of unspecified
   length has no such jump.

`WindowCollapse` says consecutive frozen windows are one longer word.  That
collapse assumes the window length is chosen independently of magnitude.  It
does not apply to `κ(n)`.

---

## What this knows about `3n+1` that `expStep` does not

`expStep` agrees with `T` on odds and replaces the even branch by `3x/2`.  Its
affine law saturates `a = j` at every window (`ScaleRecord.expOrbit_affine`).

* Saturation is incompatible with strong lightness at a positive scale
  (`saturated_not_strongly_light`).  `expStep` never meets the hypothesis of
  `light_corona_drops`.
* At the same dynamic window, `expStep` **grows**: for every `n ≥ 2`,
  `n < expOrbit(κ(n), n)` (`expStep_fails_corona_drop`).  Checked on all
  `n ∈ [2, 200]`; the proof is `expOrbit_ge` plus `κ(n) ≥ 1`.

So the pinch is not a theorem of affine law + heaviness + positivity.  It uses
the contracting even branch that `expStep` deletes.  A divergence-half
mechanism that `expStep` satisfies cannot be this pinch.

---

## Tests

### Collatz (`d = 1`)

Strongly light coronas in `n = 2..200`: **109** of them, **0** drop failures.
Examples: `2, 4, 8, 10, 12, 13, 16, 20`.  These are numbers whose low
`κ(n)` bits are sparse in odd steps.

Heavy coronas that grow, as they must: `3, 7, 9, 11, 14, 15, 23, 25, 27, 31`.
The Mersenne prefix `31 = 2^5−1` is the extreme: `a = κ = 4`, saturation, no
pinch.  This is the open side of the device, not a counterexample to the
theorem.

### `3x+5`

The small cycle `{5, 10}`: at the never-dropper `5`, the corona is **not**
strongly light (`k=2, a=1, 2·3=6 ≰ 4`), and `T^2(5)=5` does not drop.  At `10`
the corona *is* light and drops to `5` — toward the cycle minimum, not off the
cycle.

The length-27 cycle through `187`: the unique never-dropper on the cycle is
the minimum `187` itself, whose corona is heavy (`k=7, a=6, T^7(187)=1091>187`).
Other cycle points can be strongly light and drop toward `187`.  That is
allowed: the pinch is a statement about one window of one value, not a
Lyapunov function on a cycle.

Empirically, every strongly light corona for `3x+5` on `n = 2..4000` drops
(2731 lights, 0 failures).  The proved `d=1` pinch does not automatically
transfer: `C` scales with `d`, so the matching constant `2` may need to become
`2d`.  The computation says the actual accumulator is smaller than the crude
bound, and the same constant still pinches in this range.  The Lean theorem is
stated only for `d=1`.

### `3x+7`

Cycle `{5, 11, 20, 10}`.  The never-dropper is `5`: corona heavy (`k=2, a=2`),
`T^2(5)=20>5`.  The point `11` is strongly light and drops to `5`.

Empirically the same as `3x+5`: 2733 strongly light coronas on `n=2..4000`,
0 drop failures.  Same caveat: Lean proves the pinch for `3x+1` only.

### `expStep`

Fails both halves of the device, as required.  See above.

---

## First theorems (LEAN_PROVED, no `sorry`)

| theorem | statement |
|---|---|
| `corona_highPart` | `highPart(κ(n), n) = 1` |
| `corona_orbit` | `T^{κ(n)}(n) = 3^a + T^{κ(n)}(mantissa(n))` |
| `expansion_localizes` | non-drop through the corona ⇒ `2^κ + m ≤ 3^a + T^κ(m)` |
| `stronglyLight_of_mantissa` | lightness is a mantissa property; the *scale* is not |
| `light_window_drops` | `n ≥ 2^k` and strongly light ⇒ `T^k(n) < n` |
| `light_corona_drops` | that pinch at `k = κ(n)` |
| `light_pinch_drops` | that pinch at `k = π(n)` |
| `expStep_fails_corona_drop` | `n < expOrbit(κ(n), n)` for `n ≥ 2` |
| `saturated_not_strongly_light` | `a = k > 0` forbids strong lightness |

`corona_orbit` is `Density.accOrbit_two_pow_add` evaluated at the unique scale
where the high part is `1`.  The new content is the *choice* of that scale from
`|n|`, the localisation arrow, and the pinch.

---

## Decisive lemma (OPEN)

The pinch closes the strongly light coronas.  A hypothetical never-dropper is
therefore confined to **heavy coronas at every orbit point**:

    ∀ x ≥ n in the orbit of a never-dropper,  ¬ StronglyLight(x, κ(x)).

Equivalently, the mantissa of every such `x` has odd-density high enough that
`2 · 3^{a(x)} > 2^{κ(x)}`.

**Decisive lemma.**  An infinite sequence of heavy coronas, each landing at
`y = 3^{a} + T^{κ}(mantissa)` with `y ≥ x` and `κ(y) ≥ κ(x)`, cannot continue
indefinitely in the positive integers.

The intended mechanism: a heavy corona expands, so the next hybrid state is a
2-adic perturbation of a power of three (the landing sits at distance
`< 2·3^a` from `3^a` by `HighPart.offset_lt`).  The binary digits of `3^a` are
not a Mersenne block.  If that perturbation is forced into a strongly light
mantissa at the *next* corona, the pinch fires and the orbit drops, contradicting
never-drop.  If the perturbation stays heavy forever, the 2-adic itinerary of
the mantissas is a path in a proper closed subset of `ℤ₂` whose real sizes are
unbounded — and that subset should be shown empty, or shown to contain only
the 2-adic point `-1`, which is not a positive integer.

This lemma is **not proved**.  It is not Collatz.  It is the remaining arrow
"heavy localisation forces a later light corona".  The first arrow and the
light half of the second arrow are proved.

What would finish an excursion drop: show that a single heavy corona of an
odd start `n > 1` produces, within a bounded number of subsequent coronas, a
strongly light one whose pinch lands below `n`.  That statement, if true, is
stronger than "some numbers drop" and weaker than Collatz; it is the natural
target of this device.

---

## Current obstruction

Heavy mantissas.  The corona of `27` is heavy (`κ=4, a=3`) and grows to `47`.
The device as proved is silent there.  Closing the heavy case by a translate
clock is forbidden (those exist and do not rank).  Closing it by freezing a
longer window returns to Terras.  The only remaining move this geometry has is
the *next* corona of the landing `3^a + T^κ(m)`, whose scale has moved.

---

## Why this is not a renamed ranking, accumulator, or excursion clock

* It is not a ranking: `T^{κ(n)}(n)` is not claimed to drop for every `n`, and
  does not (`27`).
* It is not `affineC` under a new name: `affineC` is used as a bound inside
  the pinch, but the object is the pair `(κ(n), mantissa(n))`.
* It is not `v₂(n+1)` or `v₂(n+5)`: no integer translate is formed.  Odd-count
  of a dynamic window is a *block* statistic, not a single valuation.
* It is not OctaveOrder: that file compares octave *changes* to odd times and
  proves they cannot obstruct each other.  This file pairs the octave with the
  2-adic residue *at that octave* and proves a drop on a subset of residues.
* It is not Device 14's scale tower: that tower has frozen horizon length `k`
  and a drop window `[n, 2n)` in the reals.  Here `k` is chosen from `|n|`, and
  the obstruction is 2-adic lightness at that scale.

---

## Scorecard

| field | value |
|---|---|
| DEVICE | Dyadic corona pairing `S(n) = (n, n mod 2^{κ(n)})`, `κ(n)=⌊log₂ n⌋` |
| DEFINITION | Hybrid state at the unique scale where the high part is `1` |
| NEW INFORMATION CAPTURED | Window length locked to `|n|`; unit high part; corona-to-corona jump of one orbit |
| FIRST THEOREM | `light_corona_drops`: strongly light corona ⇒ `T^{κ(n)}(n) < n` |
| EXPSTEP TEST | Fails the drop (`expStep_fails_corona_drop`); never strongly light |
| `3x+d` TEST | Cycle minima have heavy coronas (survive).  Non-minima may pinch toward the min.  Empirically light coronas still drop for `d=5,7` on `n<4000`; Lean pinch is `d=1` only |
| CURRENT OBSTRUCTION | Heavy coronas (Mersenne-like mantissas).  Next-corona mixing not proved |
| DECISIVE LEMMA | An infinite heavy-corona itinerary cannot exist in the positive integers |
| LEAN STATUS | `DeviceHybrid.lean`: pinch, localisation, and expStep failure **PROVED**.  Decisive lemma **OPEN**.  No `sorry`.  No Collatz claim |
| MATHLIB STATUS | Not used.  Core `Nat` only |
