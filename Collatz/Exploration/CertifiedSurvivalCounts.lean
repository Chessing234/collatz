import Collatz.Exploration.ExactSurvivalCounts
import Collatz.Exploration.CertifiedFirstCrossing

/-! Apply the exact transfer to every horizon through the certified limit. -/
namespace Collatz.Exploration.CertifiedSurvivalCounts
open FirstLightConsequences FirstLightCounting FirstLightEventual

/-- Actual survival counts are exactly coefficient counts through horizon 14186. -/
theorem actual_count_eq {H : Nat} (hH : H≤14186) (N : Nat) :
    NaturalDensity.predicateCount (ActualSurvival H) N =
      PeriodicCounting.countBelow (survives H) N :=
  ExactSurvivalCounts.actual_count_eq
    (exactThrough_mono CertifiedFirstCrossing.exactThrough_14186 hH) N

/-- Exact decomposition, with no finite exceptional-source correction. -/
theorem actual_count_div_mod {H : Nat} (hH : H≤14186) (N : Nat) :
    NaturalDensity.predicateCount (ActualSurvival H) N =
      (N/2^H)*PeriodicCounting.countBelow (survives H) (2^H) +
        PeriodicCounting.countBelow (survives H) (N%2^H) :=
  ExactSurvivalCounts.actual_count_div_mod
    (exactThrough_mono CertifiedFirstCrossing.exactThrough_14186 hH) N

end Collatz.Exploration.CertifiedSurvivalCounts
