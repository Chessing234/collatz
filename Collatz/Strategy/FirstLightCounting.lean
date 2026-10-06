import Collatz.Strategy.FirstLightPeriodicity
import Collatz.Structure.PeriodicCounting

/-!
# Counting certified no-descent classes

The heavy-prefix test is periodic at every finite horizon, independently of
any descent certificate. A certificate identifies its value with actual
no-descent for starts greater than 1. Counting shifted inputs n+2 removes
those two exceptional base inputs while preserving the same period.
-/
namespace Collatz.FirstLightCounting
open FirstLightDescent FirstLightConsequences FirstLightPeriodicity PeriodicCounting

/-- Check that no coefficient prefix is light through H, including index zero. -/
def heavyCheck (H n : Nat) : Bool :=
  (List.range (H+1)).all fun j => decide (2^j ≤ 3^oddCount n j)

/-- Exact logical meaning of the finite Boolean test. -/
theorem heavyCheck_iff (H n : Nat) : heavyCheck H n = true ↔
    ∀ j, j≤H → 2^j ≤ 3^oddCount n j := by
  simp only [heavyCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h j hj; exact h j (by omega)
  · intro h j hj; exact h j (by omega)

/-- The test depends only on the binary residue at the stated horizon. -/
theorem heavyCheck_congr {H n m : Nat} (hmod : n%2^H=m%2^H) :
    heavyCheck H n = heavyCheck H m := by
  apply Bool.eq_iff_iff.mpr
  rw [heavyCheck_iff, heavyCheck_iff]
  constructor
  · intro h j hj
    simpa only [oddCount_congr hj hmod] using h j hj
  · intro h j hj
    simpa only [oddCount_congr hj hmod.symm] using h j hj

/-- No coefficient or orbit assumptions are needed for this periodicity. -/
theorem heavyCheck_period (H n : Nat) :
    heavyCheck H (n+2^H) = heavyCheck H n := by
  apply heavyCheck_congr
  simp

/-- Above the base inputs, a descent certificate gives an exact orbit test. -/
theorem heavyCheck_iff_noDescent {H n : Nat} (hc : ExactThrough H) (hn : 1<n) :
    heavyCheck H n = true ↔ ∀ j, j≤H → n≤acceleratedOrbit j n := by
  rw [heavyCheck_iff, no_descent_iff_heavy_prefix hc hn]

/-- Membership test for the inputs 2,3,..., so every tested start is above 1. -/
def survives (H n : Nat) : Bool := heavyCheck H (n+2)

/-- Membership is actual finite-horizon survival whenever H is certified. -/
theorem survives_iff {H n : Nat} (hc : ExactThrough H) : survives H n = true ↔
    ∀ j, j≤H → n+2≤acceleratedOrbit j (n+2) :=
  heavyCheck_iff_noDescent hc (by omega)

/-- Shifting the domain preserves the period. -/
theorem survives_period (H n : Nat) : survives H (n+2^H) = survives H n := by
  unfold survives
  have he : n+2^H+2 = n+2+2^H := by omega
  rw [he, heavyCheck_period]

/-- Exact count of surviving starts in [2,N+2), once H is certified. The
arithmetic identity itself holds for coefficient survival at every H. -/
theorem survival_count_div_mod (H N : Nat) :
    countBelow (survives H) N =
      (N/2^H)*countBelow (survives H) (2^H) +
        countBelow (survives H) (N%2^H) :=
  count_div_mod (survives H) (2^H) N (survives_period H)

/-- At most one period's successful residue classes remain after the full periods. -/
theorem survival_count_bounds (H N : Nat) :
    (N/2^H)*countBelow (survives H) (2^H) ≤ countBelow (survives H) N ∧
    countBelow (survives H) N ≤ (N/2^H+1)*countBelow (survives H) (2^H) :=
  periodic_count_bounds (survives H) (2^H) N (Nat.pow_pos (by decide))
    (survives_period H)

/-- Increasing the horizon can only remove surviving inputs. -/
theorem survives_mono {H K n : Nat} (hHK : H≤K) (h : survives K n=true) :
    survives H n=true := by
  apply (heavyCheck_iff H (n+2)).mpr
  have hk := (heavyCheck_iff K (n+2)).mp h
  intro j hj
  exact hk j (by omega)

end Collatz.FirstLightCounting
