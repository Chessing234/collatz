import Collatz.Strategy.HHLemmaFive

/-!
# What each wall costs

`HHLemmaFive` made the Halbeisen–Hungerbühler criterion unconditional, and then
showed it reproduces the repository's existing bound `6809` rather than beating
it.  That invites the operational question this file answers: **exactly how large
a verified range would each length cost?**

## The threshold

The criterion kills a length `L` when `hhMin L n L < (2 ^ L − 3 ^ n) · c` for
every admissible `n`.  Rearranged, `L` is killed exactly when

`c > hhMin L n L / (2 ^ L − 3 ^ n)`,

a rational **depending only on `L` and `n`** — the same separation
`ExclusionRatio` performs for the product bound.  `hhKills` is the test and
`hhKills_mono` is its monotonicity in the range.

Measured (exact rational arithmetic, at `n = nmax L`, the largest `n` with
`3 ^ n < 2 ^ L`; that `n` maximises the threshold — checked against *all*
admissible `n` for every `L < 60` and at `L = 485, 1539, 2593`, with no
exception):

| `L` | `n` | verified range needed |
|---|---|---|
| `485` | `306` | `72 059` |
| `1539` | `971` | `238 671` |
| `2593` | `1636` | `420 842` |
| `3647` | `2301` | `620 859` |
| `4701` | `2966` | `841 478` |
| `5755` | `3631` | **`1 086 055`** |
| `6809` | `4296` | **`1 358 718`** |
| `7863` | `4961` | `1 664 599` |
| `9971` | `6291` | `2 403 661` |
| `14187` | `8951` | `4 733 176` |
| `24727` | `15601` | `206 178 000` |

## Two things this makes visible

**The repository's verified range is tuned to the wall.**  `1 086 464` exceeds
the price of `5755` — `1 086 055` — by `409`, and falls short of `6809`'s price
by a factor of `1.2506`.  That is not a coincidence; it is the smallest round
range that clears the previous ladder step.

**The sharp criterion really is a better exchange rate**, which is what proving
Lemma 5 bought.  The product bound needs `c = 3 072 000` to reach `6809` and
`12 288 000` to reach `14187`; the sharp criterion needs `1 358 718` and
`4 733 176` — cheaper by `2.26×` and `2.60×`.  The gain is in the rate, not in
the current bound.

**So the next unconditional step is priced.**  Verifying Collatz to `1 358 718`
— a `1.2506×` extension of a range this repository has already widened twice —
moves the cycle-length bound from `6809` to `7863`.  That is arithmetic, not
insight, and it is written down here so the cost is known before it is paid.

## A claim checked and withdrawn

It was suggested that the wall sits where the entropy of the extremal gap
sequences, `log₂ C(a, L−a)`, crosses `log₂ G`.  There is no such crossing.  Along
the ladder the two run `295.2` vs `476`, `945.4` vs `1530`, … , `4199.7` vs
`6799` at the wall itself, `6152.7` vs `9961` after it — entropy stays below bit
length by a near-constant ratio `≈ 0.62` throughout, with nothing distinguishing
`6809`.  The comparison describes the whole ladder equally and explains no wall.
-/

namespace Collatz
namespace HHThreshold

open HalbeisenHungerbuhler

/-- The criterion's test at one `(L, n)`: does verified range `c` kill this
length?  This is `hh_criterion`'s hypothesis `hsmall`, made decidable. -/
def hhKills (c L n : Nat) : Bool :=
  decide (hhMin L n L < (2 ^ L - 3 ^ n) * c)

/-- **The test is monotone in the verified range.**  Widening the range never
loses a length. -/
theorem hhKills_mono {c c' L n : Nat} (hcc : c ≤ c') (h : hhKills c L n = true) :
    hhKills c' L n = true := by
  rw [hhKills, decide_eq_true_eq] at h ⊢
  exact Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left _ hcc)

/-- The criterion in threshold form: if the range kills `(L, n)` and the cycle
has that many odd steps, its minimum lies below the range. -/
theorem lt_of_hhKills {x L c : Nat} (hx : 0 < x) (hcyc : AccCycle.AccIsCycleOf x L)
    (hmin : ∀ k : Nat, x ≤ acceleratedOrbit k x)
    (hgap : 0 < 2 ^ L - 3 ^ oddCount x L)
    (h : hhKills c L (oddCount x L) = true) : x < c := by
  rw [hhKills, decide_eq_true_eq] at h
  exact HHBridge.hh_criterion' hx hcyc hmin hgap h

/-! ## The ladder, at its first two rungs

The prices in the table above, checked in the kernel where the numerals are
small enough to be worth checking.  `485` is killed at its stated price and not
one below it. -/

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
theorem kills_485 : hhKills 72059 485 306 = true := by decide

set_option exponentiation.threshold 1000 in
set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
theorem not_kills_485 : hhKills 72058 485 306 = false := by decide

end HHThreshold
end Collatz
