# Device: leftover-precision future cone

Agent 10 — information / entropy.  No Collatz claim.

`word_realizable` says every finite valuation word is the word of *some*
odd integer.  That quantifies over starts.  A single integer does not: the
excursion map is a function, so the actual forward orbit of a fixed `n` is a
singleton ray.  The object below keeps `n` fixed and records the symbolic
states that are still compatible with `n` once some of its 2-adic digits are
treated as unrevealed, together with the reverse-tree v-lifts of the same
landing.  Neither family is a singleton, and neither is the free shift.

## Why the orbit is the wrong cone

For odd `n` write `n + 1 = 2^v u` with `u` odd, and

```
W  = v₂(3^v u − 1),     e = (3^v u − 1) / 2^W.
```

`IsExcursion` pins `(v, u, W, e)` uniquely (`excursion_v_unique`,
`next_odd_unique`).  If `F_k(n)` were the length-`k` prefixes of this orbit,
then `|F_k(n)| = 1` for every `k`.  There is nothing to count.

## Realization coordinate `Q(n, prefix)`

The current odd integer is the whole constraint on the next letter.

- **Forward, full information.**  After a valuation prefix `ρ` that `n`
  actually realises, the landing `m` is a definite odd integer.  The next
  Syracuse letter is the unique `r` with `(3m + 1) mod 2^{r+1} = 2^r`
  (`val_iff_mod`).  The coordinate is `Q(n, ρ) = m`.  It determines the
  future completely — this is the singleton the device is not.
- **Forward, leftover precision `k`.**  Keep `n` (hence `v` and `u`) fixed,
  but spend only `k ≥ 1` further bits of `u`.  The coordinate is the pair

  ```
  Q(n, k) = (v, u mod 2^k).
  ```

  The next extra-halving letter `W'` is constrained by this pair, not by a
  search over starts: every lift is of *this* `n`, in the cylinder
  `n' = 2^v (u + t 2^k) − 1`.
- **Reverse.**  After a reverse prefix `ρ` from the fixed landing `n`, the
  current ancestor is `m`.  The coordinate is `Q(n, ρ) = m`.  The next
  reverse letter `(v, W)` is possible if and only if `3^v` divides
  `2^W m + 1` with odd cofactor — a property of `m` alone.

In all three readings, `Q` is the current integer (or its unspent 2-adic
window).  It is not a word, not an automaton state, and not a residue class
chosen to realise a prescribed word.

## The nested cone `F_k(n)` — W-lifts of a fixed start

**Definition.**  For odd `n` with excursion data `(v, u, W, e)` and budget
`k ≥ 1`, a value `W' ≥ 1` lies in `F_k(n)` when there exists `t ∈ ℕ` such
that the lift

```
u'  = u + t · 2^k,          n' = 2^v u' − 1
```

is an excursion start of the *same* run length `v` with extra-halving count
`W'`.  Equivalently: `W'` is a peak valuation realised by a 2-adic tail of
*this* `u`, not by a fresh integer chosen to match a word.

`v` is frozen because `u'` stays odd for `k ≥ 1`, so `v₂(n' + 1) = v`.
The only free data is the unrevealed tail of `u`.

**Nested.**  If `1 ≤ k ≤ k'` and `W' ∈ F_{k'}(n)`, then `W' ∈ F_k(n)`: a
congruence modulo `2^{k'}` is a congruence modulo `2^k`, and the same lift
rewrites as `t' · 2^{k'} = (t' · 2^{k'−k}) · 2^k`.  So

```
F_{k'}(n)  ⊆  F_k(n).
```

The family shrinks as more digits of *this* `n` are revealed.

**Not a singleton.**  The zero lift `t = 0` always contributes the true `W`,
so `W ∈ F_k(n)` for every `k`.  In addition:

- if `k < W`, the lift `t = 1` has peak valuation exactly `k` (ultrametric:
  `v₂(2^W e + 3^v 2^k) = k`), hence `k ∈ F_k(n)` and `k ≠ W`;
- if `k = W`, the lift `t = 1` raises the valuation strictly above `W`
  (`2^W(e + 3^v)` with `e + 3^v` even).

So `|F_k(n)| ≥ 2` whenever `k ≤ W`.

**Not the free shift.**  Every lift with budget `k ≤ W` has peak divisible
by `2^k`, so `W' ≥ k`.  Letters `1, …, k−1` are excluded.  For `k > W` the
second summand `t · 3^v · 2^k` has valuation `> W` and cannot cancel the
true peak, so `F_k(n) = {W}` — a singleton *after* the budget overruns the
true `W`, never the whole alphabet `{1, 2, 3, …}`.

The one-step picture, for this fixed `n`:

| budget | cone `F_k(n)` | width |
|---|---|---|
| `1 ≤ k ≤ W` | contains `{k, W}` and no letter `< k` | `≥ 2`, missing `{1,…,k−1}` |
| `k > W` | `{W}` | `1` |

That is a nested family of proper subsets of the extra-halving alphabet,
indexed by how many digits of *this* `n` have been spent.  It is the
information remaining in the even branch of one excursion, not a language
of many starts.

## Reverse-tree siblings — a second cone, finite rank

The W-tail above is a cone of *forward* extra-halving values.  The reverse
excursion tree of the same `n` is a cone of *symbolic parents*.

**Definition.**  A reverse letter of the fixed odd landing `n` is a pair
`(v, W)` for which some parent realises `IsExcursion parent v u W n`.
Write `R_1(n)` for that set of pairs, and `R_k(n)` for reverse words of
length `k` (nested by prefix: dropping the last letter of a word in
`R_{k+1}(n)` lands in `R_k(n)`).

This is not a forward orbit.  It is the set of reverse-tree siblings of `n`,
labelled by the excursion data that maps them onto `n`.

**Not the free shift.**  `3^v` must divide `2^W n + 1`.  In particular:

- if `3 ∣ n` then `2^W n + 1 ≡ 1 (mod 3)`, so `R_1(n)` is empty;
- `(v, W) = (1, 1)` fails at `n = 5`, since `3u = 11`;
- `n mod 3` forces the parity of `W`: odd `W` when `n ≡ 1 (mod 3)`, even
  `W` when `n ≡ 2 (mod 3)`.

**Not a singleton.**  The landing `13` has three `v`-lifts at `W = 1`:

```
17  --(v=1, W=1)-->  13
11  --(v=2, W=1)-->  13
 7  --(v=3, W=1)-->  13
```

These are `IsExcursion 17 1 9 1 13`, `IsExcursion 11 2 3 1 13`,
`IsExcursion 7 3 1 1 13`.  Rank `3` at one node, from one fixed `n`.

**Finite rank at a fixed `W`.**  A reverse letter `(v, W)` requires
`3^v ≤ 2^W n + 1`, so only finitely many `v` occur for each `(n, W)`.  The
`v`-lift rank of `(n, W)` is that finite number — the 3-adic content of the
reverse peak `2^W n + 1`, read as a branching factor.  At `n = 13`, `W = 1`
the peak is `27 = 3^3` and the rank is exactly `3`.

## Width, rank, entropy

Let `w_k(n) = |F_k(n)|` in the W-tail cone (a subset of `{1, 2, 3, …}`).

- For `k > W(n)`, `w_k(n) = 1` and the topological entropy of the tail is
  zero: every further bit of `u` is invisible to `W`.
- For `k ≤ W(n)`, `w_k(n) ≥ 2` and `w_k(n) = ∞` is possible (arbitrarily
  long cancellation against the true peak).  The *information deficit* is
  the remaining unresolved bits of `W`, namely `W(n) − k`.  Each revealed
  bit of `u` either pins a lower bound `W' ≥ k` or, once `k > W`, collapses
  the cone to a point.

Under the Haar (2-adic) measure on the unrevealed tail `t ∈ ℤ₂`, the
random variable `W'` is a truncated geometric on `{k, k+1, …}` while
`k ≤ W`, and is a Dirac at `W` once `k > W`.  Its Shannon entropy is
finite at every `k`, drops as `k` grows, and is zero for `k > W`.  That is
the entropy of *this* integer's even branch, not the entropy of the full
shift on valuations (which `word_realizable` already showed is unconstrained
as a language of many starts).

On the reverse side, let `ρ_W(n)` be the `v`-lift rank at letter `W`, and
let `G_k(n)` be the number of reverse words of length `k` (possibly
infinite if `W` is unbounded).  The growth rate

```
h(n)  =  limsup (1/k) log G_k(n)
```

is the topological entropy of the reverse sibling tree of this `n`.  It is
not the entropy of the free shift: the alphabet at each node is the finite
set of `v`-lifts of those `W` for which `3` divides `2^W n + 1`.  For
`n ≡ 0 (mod 3)` the tree is empty and the entropy is `−∞` by convention.
For `n = 1` the only reverse letter is `(v, W) = (1, 1)` (the trivial
cycle), so `h(1) = 0`.  For `n = 13` the first rank is already `3`.

None of these quantities is a statement about every positive integer.

## What this is not

- It is not a proof that every orbit drops, is bounded, or reaches `1`.
- It is not a forbidden-word argument on the forward valuation shift:
  `word_realizable` already killed those, *by varying the start*.
- It is not a residue sieve and not a new ranking on mixed light clocks.
- The W-tail cone of one `n` becoming a singleton for `k > W(n)` does not
  force later excursions of `n` to drop.  It only says that the even branch
  of *this* excursion has no remaining 2-adic ambiguity.

The device is an information count: how many future extra-halving letters
remain compatible with a fixed integer after `k` of its cofactor bits are
spent, and how many reverse `v`-lifts that same integer admits.  Both counts
are properties of one `n`.

## Formalised

`Collatz/Strategy/FutureCone.lean` proves the W-tail nesting, the two-point
lower bound for `k ≤ W`, the exclusion of letters `< k`, the collapse
`F_k = {W}` for `k > W`, the reverse-letter constraint (including emptiness
when `3 ∣ n` and the three `v`-lifts of `13`), and that `Q` — the current
odd integer after a reverse prefix — is exactly the constraint on the next
reverse letter.  Zero `sorry`.  No Collatz claim.
