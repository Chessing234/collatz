import Collatz.Strategy.Frontier9971
import Collatz.Search.VerifiedRung11025

/-!
# The frontier at the fifth rung: no nontrivial cycle shorter than 11025

`PreCertified.cert_6956` and `pow_gap_6956` were banked against the threshold
`2 403 661`; `Search.VerifiedRung11025` supplies the range `2 404 352`, past
`G(6956) = 2 403 660`.

Two rungs remain banked and conditional: `12079` at `2 855 820` and `13133` at
`3 380 808`.

## Read this together with `Strategy.RouteCap`

`RouteCap.cert_reach_le` proves the certificate's reach obeys `A ≤ 6c`, so the
frontier this route yields is at most `fexp (6c) + 1` for *every* verified range
`c` — and `RouteCap.route_misses_a_length` names a length it cannot reach.  The
number below is therefore a measurement of how far the ladder has been climbed,
not progress toward excluding cycles in general.
-/

namespace Collatz
namespace Frontier11025

open Reach Search VerifiedRange AccCycle FrontierParametric RealizableBound

theorem verified_2404352 : VerifiedBelow 2404352 :=
  fun _ hn hlt => reachesOne_of_lt_2404352 hn hlt

theorem ge_verified_2403661 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 2403661 ≤ m :=
  ge_verified_of (verifiedBelow_mono (by omega) verified_2404352) hn hnr hm

/-- **Every nontrivial accelerated cycle has length at least `11025`.**
Unconditional. -/
theorem length_ge_11025 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 11025 ≤ L :=
  FrontierParametric.length_ge_11025_of_verified
    (fun hn' hnr' hm => ge_verified_2403661 hn' hnr' hm) hn h hnr

/-! ## Heaviness at the extended range -/

/-- A never-dropper above `2 403 661` is heavy while its odd-count is below
`6956`. -/
theorem heavy_of_neverDrops {m j : Nat} (hc : 2403661 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : oddCount m j < 6956) :
    2 ^ j ≤ 3 ^ oddCount m j :=
  Frontier8917.heavy_of_neverDrops_cert (by omega) hc PreCertified.bank_6956 hnd hA

/-- **The heavy window for a counterexample, at the fifth rung.**  Window
`j ≤ 6955`, against `6290` at the previous range. -/
theorem heavy_window_6955 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 6955) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  have hbig : 2403661 ≤ m := ge_verified_2403661 hn hnr hm
  have hle : oddCount m j ≤ j := AffineExact.oddCount_le_self m j
  exact heavy_of_neverDrops hbig hnd (by omega)

/-- **A counterexample's orbit minimum takes more than `4379` odd steps in its
first `6955`.**  The ratio is the same `17/27` from
`RunAlgebra.heavy_even_bound`. -/
theorem odd_steps_6955 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    4379 < oddCount m 6955 := by
  have hheavy := heavy_window_6955 hn hnr hm hnd (j := 6955) (by omega)
  have hle : oddCount m 6955 ≤ 6955 := AffineExact.oddCount_le_self m 6955
  rcases Nat.lt_or_ge (oddCount m 6955) 6955 with hlt | hge
  · have := RunAlgebra.heavy_even_bound hheavy (by omega)
    omega
  · omega

end Frontier11025
end Collatz
