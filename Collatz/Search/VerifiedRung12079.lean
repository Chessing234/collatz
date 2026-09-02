import Collatz.Search.VerifiedRung11025

/-!
# The verified range at the sixth riser: 2 856 960

`Search.VerifiedRung11025` reached `2 404 352`, past `G(6956) = 2 403 660`.  The
next riser on the `306 + 665k` staircase is `G(7621) = 2 855 819`, and `2790`
blocks (`2 856 960`) is the first multiple of `1024` past it.  This file sweeps
the `442` intervening blocks, `2348 … 2789`.

**The fuel is unchanged at `224`, with room again.**  A direct scan of
`[2 404 352, 2 856 960)` puts the worst drop time there at `221`, at
`n = 2 533 535`.  The previous extension *tied* the standing record of `224` (at
`n = 2 252 031`, the odd predecessor of twice the old record holder) and the note
there predicted the fuel would have to rise.  It did not: this range's worst case
is three below the record.  Drop times are not monotone in the range, and the
`224` set by `n = 1 126 015` still stands over everything below `2 856 960`.

## What this unlocks

`Strategy.PreCertified.cert_7621` and `pow_gap_7621` were banked against the
threshold `2 855 820`.  `2 856 960 ≥ 2 855 820`, so `Strategy.Frontier12079`
reads the next rung off this range with no new certificate work.  One banked rung
then remains: `13133` at `3 380 808`.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Nine more chunks -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u0 : checkRange 2348 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u1 : checkRange 2398 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u2 : checkRange 2448 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u3 : checkRange 2498 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u4 : checkRange 2548 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u5 : checkRange 2598 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u6 : checkRange 2648 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u7 : checkRange 2698 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_u8 : checkRange 2748 42 224 = true := by decide

/-! ## Aggregation -/

/-- Every surviving residue in every block below `2790` drops within `224`
accelerated steps. -/
theorem drops_all_2790 {m r : Nat} (hm : m < 2790) (hr : r ∈ survivorsMod1024) :
    dropsWithin 224 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 2348 with h | h
  · exact drops_all_2348 h hr
  · rcases Nat.lt_or_ge m 2548 with h1 | h1
    · rcases Nat.lt_or_ge m 2448 with h2 | h2
      · rcases Nat.lt_or_ge m 2398 with h3 | h3
        · exact drops_of_checkRange check_u0 (by omega) (by omega) hr
        · exact drops_of_checkRange check_u1 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 2498 with h3 | h3
        · exact drops_of_checkRange check_u2 (by omega) (by omega) hr
        · exact drops_of_checkRange check_u3 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 2698 with h2 | h2
      · rcases Nat.lt_or_ge m 2598 with h3 | h3
        · exact drops_of_checkRange check_u4 (by omega) (by omega) hr
        · rcases Nat.lt_or_ge m 2648 with h4 | h4
          · exact drops_of_checkRange check_u5 (by omega) (by omega) hr
          · exact drops_of_checkRange check_u6 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 2748 with h3 | h3
        · exact drops_of_checkRange check_u7 (by omega) (by omega) hr
        · exact drops_of_checkRange check_u8 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `2 856 960` reaches `1`.** -/
theorem reachesOne_of_lt_2856960 {n : Nat} (hn : 0 < n) (hlt : n < 2856960) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 2790) (fuel := 224)
    (fun m r hm hr => drops_all_2790 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 2790 = 2856960 := by decide
  omega

end Search
end Collatz
