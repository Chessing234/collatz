import Collatz.Exploration.AllSourceTenThousand
import Collatz.Exploration.FiniteBeattyBarrier
import Collatz.Strategy.PreCertified

/-! Reuse the banked sharper accumulator certificate through horizon 14186.
Theorem statements retain crossing existence as a hypothesis. -/
namespace Collatz.Exploration.CertifiedFirstCrossing
open FirstLightDescent FirstLightConsequences

/-- The finite Beatty barrier extends exact crossing descent to every source. -/
theorem descent_at_first_light {n j : Nat} (hn : 1 < n) (hj : j ≤ 14186)
    (hf : FirstLight n j) : acceleratedOrbit j n < n := by
  by_cases hc : 3997765 ≤ n
  · exact FiniteBeattyBarrier.first_light_descent_through hc
      PreCertified.bank_8951 PreCertified.pow_gap_8951 hj hf
  · obtain ⟨k, _, hk, hd⟩ := AllSourceTenThousand.small_first_light hn (by omega)
    have he : j=k := first_light_unique hf hk
    simpa only [he] using hd

/-- The improved horizon can be passed to the existing stopping-time theory. -/
theorem exactThrough_14186 : ExactThrough 14186 :=
  fun _ _ hn hj hf => descent_at_first_light hn hj hf

/-- The two first-event predicates agree for every source greater than one. -/
theorem first_descent_iff_first_light {n j : Nat} (hn : 1 < n) (hj : j ≤ 14186) :
    FirstDescent n j ↔ FirstLight n j :=
  FirstLightConsequences.first_descent_iff_first_light exactThrough_14186 hn hj

/-- Any first-crossing discrepancy must occur strictly after this horizon. -/
theorem discrepancy_after_14186 {n j : Nat} (hn : 1 < n) (hf : FirstLight n j)
    (hfail : n ≤ acceleratedOrbit j n) : 14186 < j := by
  by_cases hj : j ≤ 14186
  · have := descent_at_first_light hn hj hf
    omega
  · omega

/-- Heavy prefixes characterize finite actual survival at the improved horizon. -/
theorem no_descent_iff_heavy (n : Nat) (hn : 1 < n) :
    (∀ j, j ≤ 14186 → n ≤ acceleratedOrbit j n) ↔
      (∀ j, j ≤ 14186 → 2 ^ j ≤ 3 ^ oddCount n j) :=
  FirstLightConsequences.no_descent_iff_heavy_prefix exactThrough_14186 hn

/-- The inherited extremal stopping witness is also an exact coefficient crossing. -/
theorem record_first_light : FirstLight 1126015 224 := by
  apply (first_descent_iff_first_light (by decide) (by decide)).mp
  obtain ⟨k, hk, hd⟩ := AssetA.drops_within_224 (n := 1126015) (by decide) (by decide)
  have he : k=224 := by
    by_cases hl : k ≤ 223
    · have := AssetA.sigma_1126015_ge k hl
      omega
    · omega
  refine ⟨?_, ?_⟩
  · simpa only [he] using hd
  · intro j hj
    exact AssetA.sigma_1126015_ge j (by omega)

end Collatz.Exploration.CertifiedFirstCrossing
