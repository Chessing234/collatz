import Collatz.Search.VerifiedExtended
import Collatz.Search.FuelMonotone

/-!
# The verified range at the next riser: 1 358 848

`Search.VerifiedExtended` stopped at `1061` blocks because that is the first
multiple of `1024` past `G(3631) = 1 086 054`, the riser buying frontier `6809`.
The next riser is `G(4296) = 1 358 717`, and `1327` blocks (`1 358 848`) is the
first multiple of `1024` past it.  This file sweeps the `266` intervening blocks.

**The fuel.**  Fuel `200` does not survive this range: a direct scan of
`[1 086 464, 1 358 718)` shows the worst drop time is `224`, at `n = 1 126 015`
(block `1099`), which is exactly the block `VerifiedExtended` noted as lying just
past its endpoint.  So the sweep runs at fuel `224`.  The `1061` blocks already
done are lifted from fuel `200` to `224` by `Search.dropsWithin_mono` — no
recomputation, which is the whole point of `Search.FuelMonotone`.

Nothing here is new mathematics.  The soundness theorem `reachesOne_of_blocks`,
the block checker `checkBlock` and the sieve modulus `2 ^ 10` are all unchanged;
`266` more blocks are handed to the kernel at a fuel two dozen larger.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Six more chunks, at fuel `224` -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r22 : checkRange 1061 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r23 : checkRange 1111 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r24 : checkRange 1161 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r25 : checkRange 1211 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r26 : checkRange 1261 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r27 : checkRange 1311 16 224 = true := by decide

/-! ## Aggregation

Below `1061` the old sweep applies, lifted in fuel; above it, one of the six
chunks. -/

/-- Every surviving residue in every block below `1327` drops within `224`
accelerated steps. -/
theorem drops_all_1327 {m r : Nat} (hm : m < 1327) (hr : r ∈ survivorsMod1024) :
    dropsWithin 224 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 1061 with h | h
  · exact dropsWithin_mono (by omega) (drops_all_1061 h hr)
  · rcases Nat.lt_or_ge m 1211 with h1 | h1
    · rcases Nat.lt_or_ge m 1111 with h2 | h2
      · exact drops_of_checkRange check_r22 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 1161 with h3 | h3
        · exact drops_of_checkRange check_r23 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r24 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 1311 with h2 | h2
      · rcases Nat.lt_or_ge m 1261 with h3 | h3
        · exact drops_of_checkRange check_r25 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r26 (by omega) (by omega) hr
      · exact drops_of_checkRange check_r27 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `1 358 848` reaches `1`.** -/
theorem reachesOne_of_lt_1358848 {n : Nat} (hn : 0 < n) (hlt : n < 1358848) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 1327) (fuel := 224)
    (fun m r hm hr => drops_all_1327 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 1327 = 1358848 := by decide
  omega

/-- A counterexample is at least `1 358 848`. -/
theorem counterexample_ge_1358848 {n : Nat} (hn : 0 < n) (h : ¬ ReachesOne n) :
    1358848 ≤ n := by
  by_cases hlt : n < 1358848
  · exact absurd (reachesOne_of_lt_1358848 hn hlt) h
  · omega

end Search
end Collatz
