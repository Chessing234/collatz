import Collatz.Search.VerifiedRung13133

/-!
# The verified range at the eighth riser: 3 998 720

`Search.VerifiedRung13133` reached `3 382 272`, past `G(8286) = 3 380 807`, and
exhausted the rungs `PreCertified` had banked.  Round LXXV.14 banked the next one:
`cert_8951` at threshold `3 997 765`, frontier `14187`.  This file supplies its
range, sweeping the `602` blocks `3303 … 3904` — `[3 382 272, 3 998 720)`.

**The fuel is unchanged at `224`, a fourth time.**  Worst drop time in the new
interval is `188`, at `n = 3 428 767` — thirty-six below the standing record.
Four consecutive extensions have now left `224` alone while the range grew from
`1 665 024` to `3 998 720`, and the record still belongs to `n = 1 126 015`.  At
this point the constancy looks structural rather than lucky: whatever produces a
drop time near `224` is a feature of small numbers, not of the frontier.
-/

namespace Collatz
namespace Search

open Reach Congruence Strategy

/-! ## Thirteen more chunks -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w0 : checkRange 3303 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w1 : checkRange 3353 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w2 : checkRange 3403 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w3 : checkRange 3453 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w4 : checkRange 3503 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w5 : checkRange 3553 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w6 : checkRange 3603 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w7 : checkRange 3653 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w8 : checkRange 3703 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w9 : checkRange 3753 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w10 : checkRange 3803 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w11 : checkRange 3853 50 224 = true := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem check_w12 : checkRange 3903 2 224 = true := by decide


/-! ## Aggregation -/

/-- Every surviving residue in every block below `3905` drops within `224`
accelerated steps. -/
theorem drops_all_3905 {m r : Nat} (hm : m < 3905) (hr : r ∈ survivorsMod1024) :
    dropsWithin 224 (2 ^ 10 * m + r) = true := by
  rcases Nat.lt_or_ge m 3303 with h | h
  · exact drops_all_3303 h hr
  · rcases Nat.lt_or_ge m 3603 with hb1 | hb1
    · rcases Nat.lt_or_ge m 3453 with hb2 | hb2
      · rcases Nat.lt_or_ge m 3353 with hb3 | hb3
        · exact drops_of_checkRange check_w0 (by omega) (by omega) hr
        · rcases Nat.lt_or_ge m 3403 with hb4 | hb4
          · exact drops_of_checkRange check_w1 (by omega) (by omega) hr
          · exact drops_of_checkRange check_w2 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 3503 with hb3 | hb3
        · exact drops_of_checkRange check_w3 (by omega) (by omega) hr
        · rcases Nat.lt_or_ge m 3553 with hb4 | hb4
          · exact drops_of_checkRange check_w4 (by omega) (by omega) hr
          · exact drops_of_checkRange check_w5 (by omega) (by omega) hr
    · rcases Nat.lt_or_ge m 3753 with hb2 | hb2
      · rcases Nat.lt_or_ge m 3653 with hb3 | hb3
        · exact drops_of_checkRange check_w6 (by omega) (by omega) hr
        · rcases Nat.lt_or_ge m 3703 with hb4 | hb4
          · exact drops_of_checkRange check_w7 (by omega) (by omega) hr
          · exact drops_of_checkRange check_w8 (by omega) (by omega) hr
      · rcases Nat.lt_or_ge m 3853 with hb3 | hb3
        · rcases Nat.lt_or_ge m 3803 with hb4 | hb4
          · exact drops_of_checkRange check_w9 (by omega) (by omega) hr
          · exact drops_of_checkRange check_w10 (by omega) (by omega) hr
        · rcases Nat.lt_or_ge m 3903 with hb4 | hb4
          · exact drops_of_checkRange check_w11 (by omega) (by omega) hr
          · exact drops_of_checkRange check_w12 (by omega) (by omega) hr

/-! ## The new range -/

/-- **Every positive `n` below `3 998 720` reaches `1`.** -/
theorem reachesOne_of_lt_3998720 {n : Nat} (hn : 0 < n) (hlt : n < 3998720) :
    ReachesOne n := by
  refine reachesOne_of_blocks (M := 3905) (fuel := 224)
    (fun m r hm hr => drops_all_3905 hm hr) n hn ?_
  have hpow : (2:Nat) ^ 10 * 3905 = 3998720 := by decide
  omega

end Search
end Collatz
