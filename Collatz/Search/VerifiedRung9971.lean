import Collatz.Search.VerifiedRung8917

/-!
# The verified range at the fourth riser: 2 011 136

`Search.VerifiedRung8917` reached `1 665 024`, the first multiple of `1024` past
`G(5626) = 1 664 598`.  The next riser on the `306 + 665k` staircase is
`G(6291) = 2 010 159`, and `1964` blocks (`2 011 136`) is the first multiple of
`1024` past it.  This file sweeps the `338` intervening blocks, `1626 … 1963`.

**The fuel is unchanged at `224`.**  A direct scan of `[1 665 024, 2 011 136)`
puts the worst drop time there at `222`, at `n = 1 689 023` — still below the
`224` forced by `n = 1 126 015` two ranges back.  So the whole sweep runs at one
fuel, and `Search.FuelMonotone` is needed only for the `1061` blocks originally
done at `200`.

Two extensions in a row have now left the fuel alone while the range grew by a
factor of `1.85`.  The worst drop time is not tracking the range; it is a local
maximum of a heavy-tailed statistic, and the `224` record still stands from a
point well inside the first million.

## What this unlocks

`Strategy.PreCertified.cert_6291` and `pow_gap_6291` were banked against exactly
the threshold `2 010 160`.  `2 011 136 ≥ 2 010 160`, so
`Strategy.Frontier9971` reads the next rung of the ladder off this range with no
new certificate work.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Seven more chunks -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_s0 : checkRange 1626 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_s1 : checkRange 1676 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_s2 : checkRange 1726 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_s3 : checkRange 1776 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_s4 : checkRange 1826 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_s5 : checkRange 1876 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_s6 : checkRange 1926 38 224 = true := by decide

/-! ## Aggregation -/

/-- Every surviving residue in every block below `1964` drops within `224`
accelerated steps. -/
theorem drops_all_1964 {m r : Nat} (hm : m < 1964) (hr : r ∈ survivorsMod1024) :
    dropsWithin 224 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 1626 with h | h
  · exact drops_all_1626 h hr
  · rcases Nat.lt_or_ge m 1826 with h1 | h1
    · rcases Nat.lt_or_ge m 1726 with h2 | h2
      · rcases Nat.lt_or_ge m 1676 with h3 | h3
        · exact drops_of_checkRange check_s0 (by omega) (by omega) hr
        · exact drops_of_checkRange check_s1 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 1776 with h3 | h3
        · exact drops_of_checkRange check_s2 (by omega) (by omega) hr
        · exact drops_of_checkRange check_s3 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 1876 with h2 | h2
      · exact drops_of_checkRange check_s4 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 1926 with h3 | h3
        · exact drops_of_checkRange check_s5 (by omega) (by omega) hr
        · exact drops_of_checkRange check_s6 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `2 011 136` reaches `1`.** -/
theorem reachesOne_of_lt_2011136 {n : Nat} (hn : 0 < n) (hlt : n < 2011136) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 1964) (fuel := 224)
    (fun m r hm hr => drops_all_1964 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 1964 = 2011136 := by decide
  omega

end Search
end Collatz
