import Collatz.Search.Verified768000

/-!
# The verified range, extended to 1 086 464

`Search.Verified768000` clears `768 000` — `750` blocks of `1024`, checked fifty
blocks at a time, sixty-four surviving residues per block, fuel `200`.  This file
continues the same sweep by `311` more blocks, to `1061`, clearing `1 086 464`.

Nothing here is new mathematics and it would be dishonest to dress it as such.
The soundness theorem is `reachesOne_of_blocks`, unchanged; the block checker is
`checkBlock`, unchanged; the sieve modulus is `2 ^ 10`, unchanged; the fuel is
`200`, unchanged, so the old and new chunks aggregate into a single application
of `reachesOne_of_blocks`.  All that happens below is that seven more chunks are
handed to the kernel.

**Why exactly `1061` blocks.**  The realizability certificate of
`Strategy.RealizableBound` discharges the index `i` as long as

`G(i) = Bcap i / (2 ^ (⌊i log₂ 3⌋ + 1) − 3 ^ i) < c`,

`c` the verified range.  The record values of `G` in increasing order are

`… , G(2301) = 620 858 , G(2966) = 841 477 , G(3631) = 1 086 054 , G(4296) = 1 358 717 , …`

so the certificate's reach `A` is a step function of `c` with jumps exactly
there: `c = 768 000` gives `A = 2966` and the frontier `L ≥ 4701`; any
`c ≥ 841 478` gives `A = 3631` and `L ≥ 5755`; any `c ≥ 1 086 055` gives
`A = 4296` and `L ≥ 6809`.  `1061` blocks is the least multiple of `1024` past
`1 086 055`, so it is the cheapest range that buys the second jump; `822` blocks
(`841 728`) would have bought only the first.  Spending anything between the two
thresholds buys nothing at all, and this is the general shape of the trade: the
range is a staircase, and only the risers are worth paying for.

**The fuel.**  A direct scan of all `19 904` surviving residues in
`[768 000, 1 086 464)` finds that every one of them drops within `200`
accelerated steps.  The first block in this continuation that would need more is
`m = 1099` (`n = 1 126 015`, which needs `224`), safely past the endpoint — which
is why the fuel could be left alone and no monotonicity plumbing is required.

**The cost, measured.**  A fifty-block chunk costs about `35 s` of kernel time on
the machine this was compiled on; the six full chunks and one eleven-block tail
below run to a little over three and a half minutes.  Linear in blocks, as
before.  The payoff, by contrast, is the staircase above: `2.5×` the compute of
`Sieved` bought `768 000`, and `1.41×` that bought one more riser.  Compute is a
ladder whose rungs get further apart.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Seven more chunks

Blocks `750` through `1060`, at the same fuel `200` as the fifteen chunks of
`Sieved` and `Verified768000`. -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r15 : checkRange 750 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r16 : checkRange 800 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r17 : checkRange 850 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r18 : checkRange 900 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r19 : checkRange 950 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r20 : checkRange 1000 50 200 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r21 : checkRange 1050 11 200 = true := by decide

/-! ## Aggregation

The same case split as `Verified768000.drops_all_750`, continued: everything
below `750` is the old aggregate, everything above is one of the seven chunks. -/

/-- Every surviving residue in every block below `1061` drops within `200`
accelerated steps. -/
theorem drops_all_1061 {m r : Nat} (hm : m < 1061) (hr : r ∈ survivorsMod1024) :
    dropsWithin 200 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 750 with h | h
  · exact drops_all_750 h hr
  · rcases Nat.lt_or_ge m 950 with h1 | h1
    · rcases Nat.lt_or_ge m 850 with h2 | h2
      · rcases Nat.lt_or_ge m 800 with h3 | h3
        · exact drops_of_checkRange check_r15 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r16 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 900 with h3 | h3
        · exact drops_of_checkRange check_r17 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r18 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 1050 with h2 | h2
      · rcases Nat.lt_or_ge m 1000 with h3 | h3
        · exact drops_of_checkRange check_r19 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r20 (by omega) (by omega) hr
      · exact drops_of_checkRange check_r21 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `1 086 464` reaches `1`.**  The same argument as
`reachesOne_of_lt_768000` over `311` more blocks. -/
theorem reachesOne_of_lt_1086464 {n : Nat} (hn : 0 < n) (hlt : n < 1086464) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 1061) (fuel := 200)
    (fun m r hm hr => drops_all_1061 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 1061 = 1086464 := by decide
  omega

/-- A counterexample is at least `1 086 464`. -/
theorem counterexample_ge_1086464 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) :
    1086464 ≤ n := by
  by_cases hlt : n < 1086464
  · exact absurd (reachesOne_of_lt_1086464 hn hlt) h
  · omega

end Search
end Collatz
