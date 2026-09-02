import Collatz.Strategy.Frontier11025
import Collatz.Search.VerifiedRung12079

/-!
# The frontier at the sixth rung: no nontrivial cycle shorter than 12079

`PreCertified.cert_7621` and `pow_gap_7621` were banked against the threshold
`2 855 820`; `Search.VerifiedRung12079` supplies the range `2 856 960`, past
`G(7621) = 2 855 819`.

One banked rung remains conditional: `13133` at `3 380 808`.

## Read with `Strategy.RouteCap` and `Strategy.StairLower`

`RouteCap.cert_reach_le` caps the certificate's reach at `6c` for every verified
range `c`, and `StairLower.range_gt_492286389612` prices the level-3 cliff: a
reach past `6291`… past `190537` would need a range above `4.9 · 10¹¹`.  The
number below measures how far the ladder has been climbed, not progress toward
excluding cycles in general.
-/

namespace Collatz
namespace Frontier12079

open Reach Search VerifiedRange AccCycle FrontierParametric RealizableBound

theorem verified_2856960 : VerifiedBelow 2856960 :=
  fun _ hn hlt => reachesOne_of_lt_2856960 hn hlt

theorem ge_verified_2855820 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 2855820 ≤ m :=
  ge_verified_of (verifiedBelow_mono (by omega) verified_2856960) hn hnr hm

/-- **Every nontrivial accelerated cycle has length at least `12079`.**
Unconditional. -/
theorem length_ge_12079 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 12079 ≤ L :=
  FrontierParametric.length_ge_12079_of_verified
    (fun hn' hnr' hm => ge_verified_2855820 hn' hnr' hm) hn h hnr

/-! ## Heaviness at the extended range -/

/-- A never-dropper above `2 855 820` is heavy while its odd-count is below
`7621`. -/
theorem heavy_of_neverDrops {m j : Nat} (hc : 2855820 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : oddCount m j < 7621) :
    2 ^ j ≤ 3 ^ oddCount m j :=
  Frontier8917.heavy_of_neverDrops_cert (by omega) hc PreCertified.bank_7621 hnd hA

/-- **The heavy window for a counterexample, at the sixth rung.**  Window
`j ≤ 7620`, against `6955` at the previous range. -/
theorem heavy_window_7620 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 7620) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  have hbig : 2855820 ≤ m := ge_verified_2855820 hn hnr hm
  have hle : oddCount m j ≤ j := AffineExact.oddCount_le_self m j
  exact heavy_of_neverDrops hbig hnd (by omega)

/-- **A counterexample's orbit minimum takes more than `4797` odd steps in its
first `7620`.**  The ratio is the same `17/27` from
`RunAlgebra.heavy_even_bound`. -/
theorem odd_steps_7620 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    4797 < oddCount m 7620 := by
  have hheavy := heavy_window_7620 hn hnr hm hnd (j := 7620) (by omega)
  have hle : oddCount m 7620 ≤ 7620 := AffineExact.oddCount_le_self m 7620
  rcases Nat.lt_or_ge (oddCount m 7620) 7620 with hlt | hge
  · have := RunAlgebra.heavy_even_bound hheavy (by omega)
    omega
  · omega

end Frontier12079
end Collatz
