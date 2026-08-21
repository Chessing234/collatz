import Collatz.Strategy.CycleLength1539
import Collatz.Search.Verified768000

/-!
# The cycle bound at the wider range: length at least 2593

`CycleLength1539` removed the last piece of arithmetic waste from the length
exclusion: `excludedFast` replaces the `O(L)` scan of `excludedLength` by two
comparisons at the top admissible exponent `topIndex L`, and with that the whole
range `1 ≤ L < 1539` falls to a single `decide`.  What stopped the bound at
`1539` was then no longer the method.  It was the constant: `1539` is exactly the
first length the product bound cannot exclude *at the verified range `307 200`*.

`Search.Verified768000` moves that constant to `768 000`.  This file re-runs the
identical sweep there, and the frontier moves with it, to `2593`.

## The exchange rate

The product bound excludes a length `L` when

`3 ^ a · (3c + 2a) < 3c · 2 ^ L`   at `a = topIndex L ≈ L · log₃ 2`,

with `c` the verified range.  Both sides are dominated by `2 ^ L` against
`3 ^ (L log₃ 2) = 2 ^ L`; the exclusion turns on the lower-order terms, and the
upshot — visible in the numbers rather than derived here — is that the first
surviving length grows like `√c`.  The record bears it out:

| verified range `c` | first surviving `L` |
|---|---|
| `102 400` | `520` |
| `307 200` | `1539` |
| `768 000` | `2593` |

`307200 / 102400 = 3` against `1539 / 520 ≈ 2.96`; `768000 / 307200 = 2.5`
against `2593 / 1539 ≈ 1.68 ≈ √2.5 · 1.06`.  The law is square-root, near enough
that the deviation is the lower-order terms.

## What this is, honestly

This is the one place in the development where compute becomes theorem.  Nothing
below is an idea.  The mathematics is `CycleProduct`'s inequality, already
proved; the evaluation trick is `CycleLength1539`'s, already proved; the only new
input is nine chunks of kernel computation in `Search.Verified768000`, about five
minutes of a machine's attention, which raises `c` and lets the same sweep run
further before it hits a length it cannot kill.

That honesty cuts both ways.  A square-root payoff on a linear cost is a losing
trade in the long run: to reach `L ≥ 10⁴` this way needs a verified range near
`1.1 × 10⁷`, roughly fourteen times the present one and therefore some seventy
minutes of kernel time, and every further factor in `L` costs a square in `c`.
The bound `2593` is worth having and worth quoting.  It is not worth mistaking
for progress on the conjecture.
-/

namespace Collatz
namespace CycleLength2593
open Reach Congruence AccCycle CycleExtremes NeverDrops CycleProduct CycleLength1539

/-! ## The verified range, propagated

`VerifiedSharp.ge_verified_sharp` states this at `307 200`.  The proof is
insensitive to the constant, so it is repeated verbatim at `768 000` rather than
weakened; the shape is deliberately identical so that a future widening of the
range needs only the numeral changed. -/

/-- **Every point on the orbit of a counterexample is at least `768 000`.** -/
theorem ge_verified_768000 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 768000 ≤ m := by
  obtain ⟨i, hi⟩ := hm
  by_cases hlt : m < 768000
  · exfalso
    have hpos : 0 < m := by
      rw [← hi]; exact acceleratedOrbit_positive hn i
    have hreach : ReachesOne m := Search.reachesOne_of_lt_768000 hpos hlt
    rw [← hi] at hreach
    exact hnr (reachesOne_of_accOrbit hn hreach)
  · omega

/-- A number that never drops and exceeds one is at least `768 000`. -/
theorem neverDrops_ge_768000 {x : Nat} (hgt : 1 < x) (h : NeverDrops.NeverDrops x) :
    768000 ≤ x :=
  ge_verified_768000 (by omega) (NeverDrops.not_reachesOne_of_neverDrops hgt h)
    (NeverDrops.self_witness x)

/-! ## The sweep

One kernel evaluation over all `2592` lengths, two bignum comparisons each.  The
comparisons are on numerals of up to `2593` bits, which is why the exponentiation
threshold and recursion depth have to be raised; the whole sweep still costs only
a few seconds, against the minutes the `O(L²)` scan of `excludedLength` would
have needed at this length. -/

set_option maxHeartbeats 40000000 in
set_option exponentiation.threshold 6000 in
set_option maxRecDepth 4000000 in
theorem sweep_768000 :
    ((List.range 2592).map (fun i => i + 1)).all (fun L => excludedFast 768000 L) = true := by
  decide

theorem excludedLength_of_lt_2593 {L : Nat} (hL : L < 2593) (hpos : 0 < L) :
    excludedLength 768000 L = true := by
  refine excludedLength_of_excludedFast ?_
  have h := sweep_768000
  rw [List.all_eq_true] at h
  exact h L (List.mem_map.mpr ⟨L - 1, List.mem_range.mpr (by omega), by omega⟩)

/-- **A nontrivial accelerated cycle has length at least `2593`.**  The same
argument as `length_ge_1539`, evaluated at the wider verified range: five times
the `520` the development carried a week ago, and every step of the increase
bought with computation rather than with insight. -/
theorem length_ge_2593 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 2593 ≤ L := by
  rcases Nat.lt_or_ge L 2593 with hL | hL
  · exfalso
    obtain ⟨m, hm, _hmin⟩ := exists_accCycleMin n
    obtain ⟨i, hi⟩ := hm
    have hmpos : 0 < m := by rw [← hi]; exact acceleratedOrbit_positive hn i
    have htrans : ∀ k : Nat, acceleratedOrbit k m = acceleratedOrbit (k + i) n := by
      intro k; rw [← hi, acceleratedOrbit_add k i n]
    have hc : ∀ k : Nat, 768000 ≤ acceleratedOrbit k m := by
      intro k
      exact ge_verified_768000 hn hnr ⟨k + i, (htrans k).symm⟩
    have hcyc : acceleratedOrbit L m = m := by
      rw [htrans L, Nat.add_comm L i, ← acceleratedOrbit_add i L n, h.2, hi]
    have hlt' : oddCount m L < L := Cycle.oddCount_lt_length_of_accCycle hmpos h.1 hcyc
    have hle : oddCount m L ≤ L := Nat.le_of_lt hlt'
    have hsmall : 2 * oddCount m L ≤ 3 * 768000 := by omega
    have hlt : 3 ^ oddCount m L < 2 ^ L :=
      Cycle.two_pow_gt_three_pow_of_accCycle hmpos h.1 hcyc
    exact no_cycle_of_excludedLength hmpos (by omega) hc hcyc hsmall hle hlt
      (excludedLength_of_lt_2593 hL h.1)
  · exact hL

set_option exponentiation.threshold 6000 in
set_option maxRecDepth 4000000 in
/-- The frontier of the method at this range: `2593` is not an artefact of the
sweep's endpoint but the first length whose exclusion actually fails.  Moving it
requires a larger `c`, which is to say more compute. -/
theorem frontier_2593 : excludedFast 768000 2593 = false := by decide

end CycleLength2593
end Collatz
