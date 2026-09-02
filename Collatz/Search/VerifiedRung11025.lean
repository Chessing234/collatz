import Collatz.Search.VerifiedRung9971

/-!
# The verified range at the fifth riser: 2 404 352

`Search.VerifiedRung9971` reached `2 011 136`, the first multiple of `1024` past
`G(6291) = 2 010 159`.  The next riser on the `306 + 665k` staircase is
`G(6956) = 2 403 660`, and `2348` blocks (`2 404 352`) is the first multiple of
`1024` past it.  This file sweeps the `384` intervening blocks, `1964 … 2347`.

**The fuel is unchanged at `224`, and this time only just.**  A direct scan of
`[2 011 136, 2 404 352)` puts the worst drop time there at exactly `224`, at
`n = 2 252 031` — equal to the standing record set by `n = 1 126 015`, not below
it.  Note `2 252 031 = 2 · 1 126 015 + 1`: the new worst case is the *odd
predecessor* of twice the old one, so it is the same orbit reached one
accelerated step earlier, and the record is tied rather than genuinely met a
second time.  The next extension should expect to raise the fuel.

## What this unlocks

`Strategy.PreCertified.cert_6956` and `pow_gap_6956` were banked against the
threshold `2 403 661`.  `2 404 352 ≥ 2 403 661`, so `Strategy.Frontier11025`
reads the next rung off this range with no new certificate work.

`Strategy.RouteCap.cert_reach_le` caps what that can ever be worth: the reach is
at most `6c`, so this range can never support a frontier past
`fexp (14 426 112) + 1`, and no range supports them all.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Eight more chunks -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_t0 : checkRange 1964 48 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_t1 : checkRange 2012 48 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_t2 : checkRange 2060 48 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_t3 : checkRange 2108 48 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_t4 : checkRange 2156 48 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_t5 : checkRange 2204 48 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_t6 : checkRange 2252 48 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_t7 : checkRange 2300 48 224 = true := by decide

/-! ## Aggregation -/

/-- Every surviving residue in every block below `2348` drops within `224`
accelerated steps. -/
theorem drops_all_2348 {m r : Nat} (hm : m < 2348) (hr : r ∈ survivorsMod1024) :
    dropsWithin 224 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 1964 with h | h
  · exact drops_all_1964 h hr
  · rcases Nat.lt_or_ge m 2156 with h1 | h1
    · rcases Nat.lt_or_ge m 2060 with h2 | h2
      · rcases Nat.lt_or_ge m 2012 with h3 | h3
        · exact drops_of_checkRange check_t0 (by omega) (by omega) hr
        · exact drops_of_checkRange check_t1 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 2108 with h3 | h3
        · exact drops_of_checkRange check_t2 (by omega) (by omega) hr
        · exact drops_of_checkRange check_t3 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 2252 with h2 | h2
      · rcases Nat.lt_or_ge m 2204 with h3 | h3
        · exact drops_of_checkRange check_t4 (by omega) (by omega) hr
        · exact drops_of_checkRange check_t5 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 2300 with h3 | h3
        · exact drops_of_checkRange check_t6 (by omega) (by omega) hr
        · exact drops_of_checkRange check_t7 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `2 404 352` reaches `1`.** -/
theorem reachesOne_of_lt_2404352 {n : Nat} (hn : 0 < n) (hlt : n < 2404352) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 2348) (fuel := 224)
    (fun m r hm hr => drops_all_2348 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 2348 = 2404352 := by decide
  omega

end Search
end Collatz
