import Collatz.Strategy.Frontier13133
import Collatz.Search.VerifiedRung14187

/-!
# The frontier at the eighth rung: no nontrivial cycle shorter than 14187

Round LXXV.12 exhausted the rungs `PreCertified` had banked; Round LXXV.14 banked
`cert_8951` at threshold `3 997 765`; this file supplies its range.
`Search.VerifiedRung14187` reaches `3 998 720`, past `G(8951) = 3 997 764`.

## What the number is worth

`RouteCap.cert_reach_le` proves the certificate's reach obeys `A ≤ 6c` for every
verified range `c`, and `RouteCap.route_misses_a_length` exhibits, for each `c`, a
cycle length this route cannot reach.  So the rung count is a measurement of
effort spent, not of distance remaining.  The marginal rate is visible in the
table: this rung cost `616 448` of verified range for `1054` of frontier, and
`StairLower.range_gt_492286389612` prices the point where that rate collapses —
a reach past `190537` needs a range above `4.9 · 10¹¹`.
-/

namespace Collatz
namespace Frontier14187

open Reach Search VerifiedRange AccCycle FrontierParametric RealizableBound

theorem verified_3998720 : VerifiedBelow 3998720 :=
  fun _ hn hlt => reachesOne_of_lt_3998720 hn hlt

theorem ge_verified_3997765 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 3997765 ≤ m :=
  ge_verified_of (verifiedBelow_mono (by omega) verified_3998720) hn hnr hm

/-- **Every nontrivial accelerated cycle has length at least `14187`.**
Unconditional. -/
theorem length_ge_14187 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 14187 ≤ L :=
  FrontierParametric.length_ge_14187_of_verified
    (fun hn' hnr' hm => ge_verified_3997765 hn' hnr' hm) hn h hnr

/-! ## Heaviness at the extended range -/

/-- A never-dropper above `3 997 765` is heavy while its odd-count is below
`8951`. -/
theorem heavy_of_neverDrops {m j : Nat} (hc : 3997765 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : oddCount m j < 8951) :
    2 ^ j ≤ 3 ^ oddCount m j :=
  Frontier8917.heavy_of_neverDrops_cert (by omega) hc PreCertified.bank_8951 hnd hA

/-- **The heavy window for a counterexample, at the eighth rung.**  Window
`j ≤ 8950`. -/
theorem heavy_window_8950 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 8950) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  have hbig : 3997765 ≤ m := ge_verified_3997765 hn hnr hm
  have hle : oddCount m j ≤ j := AffineExact.oddCount_le_self m j
  exact heavy_of_neverDrops hbig hnd (by omega)

/-- **A counterexample's orbit minimum takes more than `5635` odd steps in its
first `8950`.**  Same `17/27` from `RunAlgebra.heavy_even_bound`. -/
theorem odd_steps_8950 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    5635 < oddCount m 8950 := by
  have hheavy := heavy_window_8950 hn hnr hm hnd (j := 8950) (by omega)
  have hle : oddCount m 8950 ≤ 8950 := AffineExact.oddCount_le_self m 8950
  rcases Nat.lt_or_ge (oddCount m 8950) 8950 with hlt | hge
  · have := RunAlgebra.heavy_even_bound hheavy (by omega)
    omega
  · omega

end Frontier14187
end Collatz
