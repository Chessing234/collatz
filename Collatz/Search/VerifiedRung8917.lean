import Collatz.Search.VerifiedRung7863

/-!
# The verified range at the third riser: 1 665 024

`Search.VerifiedRung7863` reached `1 358 848`, the first multiple of `1024` past
`G(4296) = 1 358 717`.  The next riser is `G(4961) = 1 664 598`, and `1626`
blocks (`1 665 024`) is the first multiple of `1024` past it.  This file sweeps
the `299` intervening blocks.

**The fuel is unchanged at `224`.**  A direct scan of `[1 358 848, 1 665 024)`
puts the worst drop time there at `214`, at `n = 1 394 431` — below the `224`
already forced by `n = 1 126 015` in the previous range.  So the whole sweep,
old blocks and new, runs at one fuel and `Search.FuelMonotone` is needed only
for the `1061` blocks originally done at `200`.

Worth noting against the earlier trend: drop times are not monotone in the
range.  The previous extension needed the fuel raised, this one does not.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Six more chunks -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r28 : checkRange 1327 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r29 : checkRange 1377 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r30 : checkRange 1427 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r31 : checkRange 1477 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r32 : checkRange 1527 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_r33 : checkRange 1577 49 224 = true := by decide

/-! ## Aggregation -/

/-- Every surviving residue in every block below `1626` drops within `224`
accelerated steps. -/
theorem drops_all_1626 {m r : Nat} (hm : m < 1626) (hr : r ∈ survivorsMod1024) :
    dropsWithin 224 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 1327 with h | h
  · exact drops_all_1327 h hr
  · rcases Nat.lt_or_ge m 1477 with h1 | h1
    · rcases Nat.lt_or_ge m 1377 with h2 | h2
      · exact drops_of_checkRange check_r28 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 1427 with h3 | h3
        · exact drops_of_checkRange check_r29 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r30 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 1577 with h2 | h2
      · rcases Nat.lt_or_ge m 1527 with h3 | h3
        · exact drops_of_checkRange check_r31 (by omega) (by omega) hr
        · exact drops_of_checkRange check_r32 (by omega) (by omega) hr
      · exact drops_of_checkRange check_r33 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `1 665 024` reaches `1`.** -/
theorem reachesOne_of_lt_1665024 {n : Nat} (hn : 0 < n) (hlt : n < 1665024) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 1626) (fuel := 224)
    (fun m r hm hr => drops_all_1626 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 1626 = 1665024 := by decide
  omega

end Search
end Collatz
