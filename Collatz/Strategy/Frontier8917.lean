import Collatz.Strategy.FrontierParametric
import Collatz.Search.VerifiedRung8917
import Collatz.Search.VerifiedRange
import Collatz.Strategy.RunAlgebra

/-!
# The frontier at the third rung: no nontrivial cycle shorter than 8917

The same instantiation as `Strategy.Frontier7863`, one riser further up:
`PreCertified.cert_5626` and `pow_gap_5626` were banked in advance, and
`Search.VerifiedRung8917` supplies the range `1 665 024`, past
`G(4961) = 1 664 598`.
-/

namespace Collatz
namespace Frontier8917

open Reach Search VerifiedRange AccCycle FrontierParametric RealizableBound

theorem verified_1665024 : VerifiedBelow 1665024 :=
  fun _ hn hlt => reachesOne_of_lt_1665024 hn hlt

theorem ge_verified_1664599 {n m : Nat} (hn : 0 < n) (hnr : ¬ ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m) : 1664599 ≤ m :=
  ge_verified_of (verifiedBelow_mono (by omega) verified_1665024) hn hnr hm

/-- **Every nontrivial accelerated cycle has length at least `8917`.**
Unconditional. -/
theorem length_ge_8917 {n L : Nat} (hn : 0 < n) (h : AccIsCycleOf n L)
    (hnr : ¬ ReachesOne n) : 8917 ≤ L :=
  FrontierParametric.length_ge_8917_of_verified
    (fun hn' hnr' hm => ge_verified_1664599 hn' hnr' hm) hn h hnr

/-! ## Heaviness, for the rest of the repository

The repository has fifteen `*_of_heavy` theorems consuming
`2 ^ j ≤ 3 ^ oddCount n j` — `CoupledCycle.prefix_gap_of_heavy`,
`RunAlgebra.heavy_run_count`, `InfiniteWord.not_noAdjOdd_of_heavy` and the rest —
but nothing derived heaviness from never-dropping.  `no_light_window_of_cert` is
exactly that fact, stated as a contradiction; here it is in positive form, so the
certificate machinery feeds those consumers directly.

At the range this file establishes, a never-dropper is heavy for every window
whose odd-count stays below `5626`. -/

/-- **A never-dropper above the verified range is heavy**, as far as the
certificate reaches. -/
theorem heavy_of_neverDrops_cert {c A m j : Nat} (hcpos : 0 < c) (hc : c ≤ m)
    (hcert : ∀ i : Nat, i < A → Bcap i + 3 ^ i * c < 2 * 2 ^ fexp i * c)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : oddCount m j < A) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  rcases Nat.lt_or_ge (3 ^ oddCount m j) (2 ^ j) with hlt | hge
  · exact absurd (no_light_window_of_cert hcpos hc hcert hnd hlt hA) (by simp)
  · exact hge

/-- The instance at this file's range: a never-dropper above `1 664 599` is heavy
while its odd-count is below `5626`. -/
theorem heavy_of_neverDrops {m j : Nat} (hc : 1664599 ≤ m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) (hA : oddCount m j < 5626) :
    2 ^ j ≤ 3 ^ oddCount m j :=
  heavy_of_neverDrops_cert (by omega) hc PreCertified.bank_5626 hnd hA

/-! ## The heavy window, extended

`HeavyWord.heavy_window_of_counterexample_2592` gives the window `j ≤ 2592` at
range `768 000`.  The range here reaches `5626` in the odd-count, so the window
more than doubles, and with it the structural bound on a counterexample's first
steps. -/

/-- **The heavy window for a counterexample, at the extended range.**  More than
twice the reach of `HeavyWord.heavy_window_of_counterexample_2592`. -/
theorem heavy_window_5625 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) {j : Nat} (hj : j ≤ 5625) :
    2 ^ j ≤ 3 ^ oddCount m j := by
  have hbig : 1664599 ≤ m := ge_verified_1664599 hn hnr hm
  have hle : oddCount m j ≤ j := AffineExact.oddCount_le_self m j
  exact heavy_of_neverDrops hbig hnd (by omega)

/-- **A counterexample's orbit minimum takes more than `3541` odd steps in its
first `5625`.**  Against `1632` of `2592` from the previous range. -/
theorem odd_steps_5625 {n m : Nat} (hn : 0 < n) (hnr : ¬ Reach.ReachesOne n)
    (hm : ∃ i : Nat, acceleratedOrbit i n = m)
    (hnd : ∀ i : Nat, m ≤ acceleratedOrbit i m) :
    3541 < oddCount m 5625 := by
  have hheavy := heavy_window_5625 hn hnr hm hnd (j := 5625) (by omega)
  have hle : oddCount m 5625 ≤ 5625 := AffineExact.oddCount_le_self m 5625
  rcases Nat.lt_or_ge (oddCount m 5625) 5625 with hlt | hge
  · have := RunAlgebra.heavy_even_bound hheavy (by omega)
    omega
  · omega

end Frontier8917
end Collatz
