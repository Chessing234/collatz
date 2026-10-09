import Collatz.Strategy.FirstLightEventual

/-! An exact crossing certificate removes the finite count exception completely.
These are finite-horizon statements and do not establish universal crossing. -/
namespace Collatz.Exploration.ExactSurvivalCounts
open FirstLightConsequences FirstLightCounting FirstLightEventual

/-- An exact horizon identifies actual survival at every shifted source. -/
theorem actual_iff_periodic {H n : Nat} (hc : ExactThrough H) :
    ActualSurvival H n ↔ survives H n=true := (survives_iff hc).symm

/-- The actual survival predicate itself is periodic on the shifted domain. -/
theorem actual_period {H n : Nat} (hc : ExactThrough H) :
    ActualSurvival H (n+2^H) ↔ ActualSurvival H n := by
  rw [actual_iff_periodic hc, actual_iff_periodic hc, survives_period]

/-- The actual count has no exceptional-input error at a certified horizon. -/
theorem actual_count_eq {H : Nat} (hc : ExactThrough H) (N : Nat) :
    NaturalDensity.predicateCount (ActualSurvival H) N =
      PeriodicCounting.countBelow (survives H) N := by
  have he : NaturalDensity.predicateCount (ActualSurvival H) N =
      NaturalDensity.predicateCount (fun n => survives H n=true) N :=
    Nat.le_antisymm
      (NaturalDensity.predicateCount_mono (fun _ => (actual_iff_periodic hc).mp) N)
      (NaturalDensity.predicateCount_mono (fun _ => (actual_iff_periodic hc).mpr) N)
  rw [he, NaturalDensity.predicateCount_bool]

/-- Exact full-period and remainder decomposition for actual orbit survival. -/
theorem actual_count_div_mod {H : Nat} (hc : ExactThrough H) (N : Nat) :
    NaturalDensity.predicateCount (ActualSurvival H) N =
      (N/2^H)*PeriodicCounting.countBelow (survives H) (2^H) +
        PeriodicCounting.countBelow (survives H) (N%2^H) := by
  rw [actual_count_eq hc]
  exact survival_count_div_mod H N

/-- Both finite count bounds hold with no additive source cutoff. -/
theorem actual_count_bounds {H : Nat} (hc : ExactThrough H) (N : Nat) :
    (N/2^H)*PeriodicCounting.countBelow (survives H) (2^H) ≤
      NaturalDensity.predicateCount (ActualSurvival H) N ∧
    NaturalDensity.predicateCount (ActualSurvival H) N ≤
      (N/2^H+1)*PeriodicCounting.countBelow (survives H) (2^H) := by
  rw [actual_count_eq hc]
  exact survival_count_bounds H N

end Collatz.Exploration.ExactSurvivalCounts
