import Collatz.Search.VerifiedRung12079

/-!
# The verified range at the seventh riser: 3 382 272

`Search.VerifiedRung12079` reached `2 856 960`, past `G(7621) = 2 855 819`.  The
next riser is `G(8286) = 3 380 807`, and `3303` blocks (`3 382 272`) is the first
multiple of `1024` past it.  This file sweeps the `513` intervening blocks,
`2790 … 3302`.

**The fuel is unchanged at `224`, with more room than ever.**  A direct scan of
`[2 856 960, 3 382 272)` puts the worst drop time there at `195`, at
`n = 3 137 471` — twenty-nine below the standing record.  Three consecutive
extensions have now left `224` alone, and the record still belongs to
`n = 1 126 015`, inside the first million and a factor of three below the current
range.  Whatever drives large drop times, it is not proximity to the frontier.

## What this unlocks

`Strategy.PreCertified.cert_8286` and `pow_gap_8286` were the last entries banked
in that file.  `3 382 272 ≥ 3 380 808`, so `Strategy.Frontier13133` reads the
final banked rung off this range, and **the whole `PreCertified` table becomes
unconditional**.  Anything beyond it needs a new certificate as well as a new
range — and `Strategy.RouteCap` prices both.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Eleven more chunks -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v0 : checkRange 2790 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v1 : checkRange 2840 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v2 : checkRange 2890 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v3 : checkRange 2940 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v4 : checkRange 2990 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v5 : checkRange 3040 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v6 : checkRange 3090 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v7 : checkRange 3140 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v8 : checkRange 3190 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v9 : checkRange 3240 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_v10 : checkRange 3290 13 224 = true := by decide

/-! ## Aggregation -/

/-- Every surviving residue in every block below `3303` drops within `224`
accelerated steps. -/
theorem drops_all_3303 {m r : Nat} (hm : m < 3303) (hr : r ∈ survivorsMod1024) :
    dropsWithin 224 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 2790 with h | h
  · exact drops_all_2790 h hr
  · rcases Nat.lt_or_ge m 3040 with h1 | h1
    · rcases Nat.lt_or_ge m 2890 with h2 | h2
      · rcases Nat.lt_or_ge m 2840 with h3 | h3
        · exact drops_of_checkRange check_v0 (by omega) (by omega) hr
        · exact drops_of_checkRange check_v1 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 2990 with h3 | h3
        · rcases Nat.lt_or_ge m 2940 with h4 | h4
          · exact drops_of_checkRange check_v2 (by omega) (by omega) hr
          · exact drops_of_checkRange check_v3 (by omega) (by omega) hr
        · exact drops_of_checkRange check_v4 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 3190 with h2 | h2
      · rcases Nat.lt_or_ge m 3090 with h3 | h3
        · exact drops_of_checkRange check_v5 (by omega) (by omega) hr
        · rcases Nat.lt_or_ge m 3140 with h4 | h4
          · exact drops_of_checkRange check_v6 (by omega) (by omega) hr
          · exact drops_of_checkRange check_v7 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 3240 with h3 | h3
        · exact drops_of_checkRange check_v8 (by omega) (by omega) hr
        · rcases Nat.lt_or_ge m 3290 with h4 | h4
          · exact drops_of_checkRange check_v9 (by omega) (by omega) hr
          · exact drops_of_checkRange check_v10 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `3 382 272` reaches `1`.** -/
theorem reachesOne_of_lt_3382272 {n : Nat} (hn : 0 < n) (hlt : n < 3382272) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 3303) (fuel := 224)
    (fun m r hm hr => drops_all_3303 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 3303 = 3382272 := by decide
  omega

end Search
end Collatz
