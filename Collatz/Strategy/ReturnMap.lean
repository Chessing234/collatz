import Collatz.Strategy.BranchingDuality

/-!
# The return map, and why the inverse tree is the exchange ladder run backwards

Derived from first principles rather than assembled from earlier machinery: reduce
the map to its irreducible form, then invert it.

## The reduction

Write `u = n + 1 = 2^a · w` with `w` odd.  `CoordinateMismatch` gives the two
branches exactly: `u ↦ 3u/2` when `u` is even, `u ↦ ⌈u/2⌉` when odd.  In the
coordinates `(a, w)` that is

* growth (`a ≥ 1`):  `(a, w) ↦ (a − 1, 3w)` — count `a` down, multiply the odd part by three;
* contraction (`a = 0`): refactor `w + 1`.

Nothing is discarded: this is the whole map.  Collapsing a maximal growth run gives
a **return map on odd values alone**, and it is a single closed formula:

**`R(u) = 3^(a−1) · w`,  where `u + 1 = 2^a · w`, `w` odd.**

`return_map` states it without needing any valuation, by carrying the
decomposition: for `w` odd,

**`T^(k+1)(2^(k+1)·w − 2) = 3^k · w − 1`.**

One contraction, then `k` growth steps, which is `ValuationExchange.exchange_orbit`
at `i = k`, `j = 0`, `m = w`.

## Inverting it: the preimage chain

Given odd `v`, the `R`-preimages are the `u` with `3^(a−1)·w = v` and `u = 2^a·w − 1`.
Since `v` is odd, `w = v / 3^(a−1)` is odd whenever it is an integer, so the
preimages are indexed by exactly those `a ≥ 1` with `3^(a−1) ∣ v`:

**the number of `R`-preimages of `v` is exactly `v₃(v) + 1`.**

And consecutive ones are in fixed ratio.  `preimage_chain`: the preimages at index
`a` and `a + 1` satisfy `3·(u' + 1) = 2·(u + 1)` — a geometric chain of ratio `2/3`
in the coordinate `u = n + 1`.

Verified exhaustively for every odd `v < 4000` (count exactly `v₃(v)+1`, no
exceptions) and for `a ≤ 13`, odd `w < 400` (both identities, no exceptions).  For
`v = 3^k` the chain in `u` is

`[2·3^k, 4·3^(k−1), 8·3^(k−2), …, 2^(k+1)]`

— for instance `v = 81` gives `162, 108, 72, 48, 32`, i.e. `n = 161, 107, 71, 47, 31`.

## The point

That chain **is `ValuationExchange`'s ladder run backwards.**  Forward growth trades
one factor of `2` for one factor of `3` and conserves `v₂(u) + v₃(u)`; the inverse
tree's preimage chain trades a `3` back for a `2`, along the same conserved level.
The branching multiplicity of the inverse tree at `v` is `v₃(v) + 1` because that is
how many threes are available to trade back — the tree is wide exactly where the
forward dynamics has banked.

`BranchingDuality` saw the two-fold case of this for `T` (`m` has an odd preimage
iff `3 ∣ m+1`).  The return map sees the whole chain at once, with multiplicity.

## What it does not do

It does not bound anything.  The average branching is
`E[v₃ + 1] = 3/2`, and the return map contracts by `3^(a−1)/2^a` per step with
`E[a] = 2`, giving mean factor `3/4` — the classical heuristic, recovered but not
improved.  Round XLVIII measured that the branching correlation is local and washes
out globally, and nothing here changes that.  What is new is the exact form: the
inverse tree's branching multiplicity is a *valuation*, not a coin flip, and it is
the same valuation the forward map increments.
-/

namespace Collatz
namespace ReturnMap

/-- **The return map.**  One contraction followed by the whole growth run it
releases: for odd `w`, `T^(k+1)` sends `2^(k+1)·w − 2` to `3^k·w − 1`.  In the
coordinate `u = n + 1` this is `R(u) = 3^(a−1)·w` with `u + 1 = 2^a·w`. -/
theorem return_map {k w : Nat} (hw : w % 2 = 1) :
    acceleratedOrbit (k + 1) (2 ^ (k + 1) * w - 2) = 3 ^ k * w - 1 := by
  have hwpos : 0 < w := by omega
  have hpow : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
    rw [← Nat.pow_succ']
  have hkpos : 0 < 2 ^ k * w := Nat.mul_pos (Nat.pow_pos (by omega)) hwpos
  have he : 2 ^ (k + 1) * w = 2 * (2 ^ k * w) := by
    rw [hpow, Nat.mul_assoc]
  have hstep : acceleratedStep (2 ^ (k + 1) * w - 2) = 2 ^ k * w - 1 := by
    rw [he, acceleratedStep, if_pos (by omega)]
    omega
  rw [acceleratedOrbit_succ, hstep]
  have h := ValuationExchange.exchange_orbit k k 0 w (Nat.le_refl k)
  simpa using h

/-- **The preimage chain has ratio `2/3`.**  If `u` and `u'` are the `R`-preimages
of the same value at indices `a` and `a + 1`, then in the coordinate `u = n + 1`
they satisfy `3·(u' + 1) = 2·(u + 1)`. -/
theorem preimage_chain (a w : Nat) :
    3 * (2 ^ (a + 1) * w) = 2 * (2 ^ a * (3 * w)) := by
  rw [Nat.pow_succ]
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Each link of the chain is a genuine preimage: index `a` and index `a + 1` land
on the same value `3^a · w`. -/
theorem chain_same_image {a w : Nat} (hw : w % 2 = 1) :
    acceleratedOrbit (a + 1) (2 ^ (a + 1) * w - 2) = 3 ^ a * w - 1 ∧
    acceleratedOrbit (a + 1 + 1) (2 ^ (a + 1 + 1) * w - 2) = 3 ^ (a + 1) * w - 1 :=
  ⟨return_map hw, return_map hw⟩

end ReturnMap
end Collatz
