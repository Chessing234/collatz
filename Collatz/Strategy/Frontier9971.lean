import Collatz.Strategy.Frontier8917
import Collatz.Search.VerifiedRung9971

/-!
# The frontier at the fourth rung: no nontrivial cycle shorter than 9971

The same instantiation as `Strategy.Frontier8917`, one riser further up.
`PreCertified.cert_6291` and `pow_gap_6291` were banked in advance against the
threshold `2 010 160`; `Search.VerifiedRung9971` supplies the range
`2 011 136`, past `G(6291) = 2 010 159`.

This is the last banked rung whose range this development actually reaches.  The
remaining three (`6956`, `7621`, `8286`, frontiers `11025`, `12079`, `13133`)
need `2 403 661`, `2 855 820`, `3 380 808` and stay conditional.

## Where this sits against the acceptance criterion

It moves the unconditional cycle bound from `8917` to `9971`, and nothing else.
Round XLIV's conclusion is untouched: the verified range needed to kill the
`k`-th rung grows like `a_k · a_{k+1} / (6 ln 2)`, so no finite range excludes
all cycle lengths.  Climbing a rung buys one rung.
-/

namespace Collatz
namespace Frontier9971

open Reach Search VerifiedRange AccCycle FrontierParametric RealizableBound

theorem verified_2011136 : VerifiedBelow 2011136 :=
  fun _ hn hlt => reachesOne_of_lt_2011136 hn hlt

theorem ge_verified_2010160 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 2010160 ≤ m :=
  ge_verified_of (verifiedBelow_mono (by omega) verified_2011136) hn hnr hm

/-- **Every nontrivial accelerated cycle has length at least `9971`.**
Unconditional. -/
theorem length_ge_9971 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 9971 ≤ L :=
  FrontierParametric.length_ge_9971_of_verified
    (fun hn' hnr' hm => ge_verified_2010160 hn' hnr' hm) hn h hnr

/-! ## Heaviness at the extended range

The certificate now reaches `6291` odd steps, so the heavy window widens with
it.  These are the same three statements as in `Strategy.Frontier8917`, read off
the new range. -/

/-- A never-dropper above `2 010 160` is heavy while its odd-count is below
`6291`. -/
theorem heavy_of_neverDrops {m j : Nat} (hc : 2010160 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : oddCount m j < 6291) :
    2 ^ j ≤ 3 ^ oddCount m j :=
  Frontier8917.heavy_of_neverDrops_cert (by omega) hc PreCertified.bank_6291 hnd hA

/-- **The heavy window for a counterexample, at the fourth rung.**  Window
`j ≤ 6290`, against `5625` at the previous range. -/
theorem heavy_window_6290 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 6290) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  have hbig : 2010160 ≤ m := ge_verified_2010160 hn hnr hm
  have hle : oddCount m j ≤ j := AffineExact.oddCount_le_self m j
  exact heavy_of_neverDrops hbig hnd (by omega)

/-- **A counterexample's orbit minimum takes more than `3960` odd steps in its
first `6290`.**  Against `3541` of `5625` from the previous range; the ratio is
the same `17/27`, which is the content of `RunAlgebra.heavy_even_bound`. -/
theorem odd_steps_6290 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    3960 < oddCount m 6290 := by
  have hheavy := heavy_window_6290 hn hnr hm hnd (j := 6290) (by omega)
  have hle : oddCount m 6290 ≤ 6290 := AffineExact.oddCount_le_self m 6290
  rcases Nat.lt_or_ge (oddCount m 6290) 6290 with hlt | hge
  · have := RunAlgebra.heavy_even_bound hheavy (by omega)
    omega
  · omega

end Frontier9971
end Collatz
