import Collatz.Strategy.AssetA
import Collatz.Strategy.FirstLightConsequences
import Collatz.Exploration.GapTenThousand

/-! Combining inherited bounded stopping certificates with the endpoint scan.
The first-crossing hypothesis is retained: this does not establish convergence. -/
namespace Collatz.Exploration.AllSourceTenThousand
open FirstLightDescent FirstLightConsequences

/-- The existing verified orbit range supplies all exceptional first crossings. -/
theorem small_first_light {n : Nat} (hn : 1 < n) (hN : n < 3998720) :
    ∃ k : Nat, k ≤ 224 ∧ FirstLight n k ∧ acceleratedOrbit k n < n := by
  obtain ⟨t, ht, hd⟩ := AssetA.drops_within_224 (by omega) (by omega : n < 3998720)
  obtain ⟨k, hk, hf⟩ := exists_first_light n t (AffineObstruction.light_of_drop hd)
  exact ⟨k, by omega, hf,
    FirstLightCertificates.descent_at_first_light_le_256 hn (by omega) hf⟩

/-- Every source above one descends at its first coefficient crossing by 10000. -/
theorem descent_at_first_light {n j : Nat} (hn : 1 < n) (hj : j ≤ 10000)
    (hf : FirstLight n j) : acceleratedOrbit j n < n := by
  by_cases hlarge : 3330950 ≤ n
  · exact GapTenThousand.descent_at_first_light hlarge hj hf
  · obtain ⟨k, _, hk, hd⟩ := small_first_light hn (by omega)
    have he : j = k := first_light_unique hf hk
    simpa only [he] using hd

/-- Interface to the existing finite-horizon stopping-time theory. -/
theorem exactThrough_ten_thousand : ExactThrough 10000 :=
  fun _ _ hn hj hf => descent_at_first_light hn hj hf

/-- Coefficient crossing and first actual descent agree throughout this horizon. -/
theorem first_descent_iff_first_light {n j : Nat} (hn : 1 < n) (hj : j ≤ 10000) :
    FirstDescent n j ↔ FirstLight n j :=
  FirstLightConsequences.first_descent_iff_first_light exactThrough_ten_thousand hn hj

/-- A failed first-crossing descent must lie strictly beyond the certified horizon. -/
theorem discrepancy_after_ten_thousand {n j : Nat} (hn : 1 < n)
    (hf : FirstLight n j) (hfail : n ≤ acceleratedOrbit j n) : 10000 < j := by
  by_cases hj : j ≤ 10000
  · have := descent_at_first_light hn hj hf
    omega
  · omega

end Collatz.Exploration.AllSourceTenThousand
