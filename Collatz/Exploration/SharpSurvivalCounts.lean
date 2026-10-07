import Collatz.Exploration.SharpFirstLightEventual
import Collatz.Strategy.FirstLightEventual

/-! Reduce the finite exceptional interval for shifted survival counts.
These finite bounds do not establish universal crossing or improve asymptotic density. -/
namespace Collatz.Exploration.SharpSurvivalCounts
open FirstLightEventual FirstLightCounting

def cutoff (H : Nat) : Nat := H*2^H/3-1

/-- Actual survival differs from the periodic Boolean test only in a finite interval. -/
theorem actual_iff_periodic_eventually (H n : Nat) (hn : cutoff H≤n) :
    ActualSurvival H n ↔ survives H n=true :=
  SharpFirstLightEventual.no_descent_iff_heavy_above_threshold (by
    unfold cutoff at hn
    omega)

/-- For every horizon, an arbitrary-cutoff actual count is bounded by the
periodic coefficient count plus the explicit exceptional interval. -/
theorem actual_count_upper (H N : Nat) :
    NaturalDensity.predicateCount (ActualSurvival H) N ≤
      cutoff H + NaturalDensity.predicateCount (fun n => survives H n=true) N :=
  NaturalDensity.predicateCount_eventual_mono (cutoff H) N
    (fun n hn => (actual_iff_periodic_eventually H n hn).mp)

/-- The reverse bound controls the count discrepancy in both directions. -/
theorem periodic_count_upper (H N : Nat) :
    NaturalDensity.predicateCount (fun n => survives H n=true) N ≤
      cutoff H + NaturalDensity.predicateCount (ActualSurvival H) N :=
  NaturalDensity.predicateCount_eventual_mono (cutoff H) N
    (fun n hn => (actual_iff_periodic_eventually H n hn).mpr)

/-- Actual finite-horizon survival has an all-cutoff upper bound at every H,
combining a finite exceptional interval and the existing heavy-residue estimate. -/
theorem actual_count_heavy_bound (H N : Nat) :
    NaturalDensity.predicateCount (ActualSurvival H) N ≤
      cutoff H + (N/2^H+1)*Density.heavyCount H := by
  have h := actual_count_upper H N
  rw [NaturalDensity.predicateCount_bool] at h
  exact Nat.le_trans h (Nat.add_le_add_left (survival_count_cutoff_bound H N) _)

end Collatz.Exploration.SharpSurvivalCounts
