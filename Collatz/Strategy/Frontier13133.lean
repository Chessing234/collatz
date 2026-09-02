import Collatz.Strategy.Frontier12079
import Collatz.Search.VerifiedRung13133

/-!
# The frontier at the seventh rung: no nontrivial cycle shorter than 13133

`PreCertified.cert_8286` and `pow_gap_8286` were the last entries banked in that
file; `Search.VerifiedRung13133` supplies the range `3 382 272`, past
`G(8286) = 3 380 807`.

**The banked ladder is now fully unconditional.**  Every rung of `PreCertified`'s
table — `6809`, `7863`, `8917`, `9971`, `11025`, `12079`, `13133` — has its
verified range.  Going further needs a new certificate *and* a new range, and
`Strategy.RouteCap` prices both: `cert_reach_le` caps the reach at `6c`, and the
cliff theorems put the range for a reach past `190537` above `4.9 · 10¹¹`.

So this file closes the ladder as a programme, not just as a table.  The number
`13133` is where the banked route ends, and `RouteCap.route_misses_a_length`
already proves no route of this shape reaches all lengths.
-/

namespace Collatz
namespace Frontier13133

open Reach Search VerifiedRange AccCycle FrontierParametric RealizableBound

theorem verified_3382272 : VerifiedBelow 3382272 :=
  fun _ hn hlt => reachesOne_of_lt_3382272 hn hlt

theorem ge_verified_3380808 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 3380808 ≤ m :=
  ge_verified_of (verifiedBelow_mono (by omega) verified_3382272) hn hnr hm

/-- **Every nontrivial accelerated cycle has length at least `13133`.**
Unconditional, and the last rung the banked certificates reach. -/
theorem length_ge_13133 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 13133 ≤ L :=
  FrontierParametric.length_ge_13133_of_verified
    (fun hn' hnr' hm => ge_verified_3380808 hn' hnr' hm) hn h hnr

/-! ## Heaviness at the final banked range -/

/-- A never-dropper above `3 380 808` is heavy while its odd-count is below
`8286`. -/
theorem heavy_of_neverDrops {m j : Nat} (hc : 3380808 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : oddCount m j < 8286) :
    2 ^ j ≤ 3 ^ oddCount m j :=
  Frontier8917.heavy_of_neverDrops_cert (by omega) hc PreCertified.bank_8286 hnd hA

/-- **The heavy window for a counterexample, at the last banked rung.**  Window
`j ≤ 8285`, against `2592` at the range where this device was introduced — more
than a threefold widening. -/
theorem heavy_window_8285 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 8285) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  have hbig : 3380808 ≤ m := ge_verified_3380808 hn hnr hm
  have hle : oddCount m j ≤ j := AffineExact.oddCount_le_self m j
  exact heavy_of_neverDrops hbig hnd (by omega)

/-- **A counterexample's orbit minimum takes more than `5216` odd steps in its
first `8285`.**  Same `17/27` from `RunAlgebra.heavy_even_bound`. -/
theorem odd_steps_8285 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    5216 < oddCount m 8285 := by
  have hheavy := heavy_window_8285 hn hnr hm hnd (j := 8285) (by omega)
  have hle : oddCount m 8285 ≤ 8285 := AffineExact.oddCount_le_self m 8285
  rcases Nat.lt_or_ge (oddCount m 8285) 8285 with hlt | hge
  · have := RunAlgebra.heavy_even_bound hheavy (by omega)
    omega
  · omega

end Frontier13133
end Collatz
