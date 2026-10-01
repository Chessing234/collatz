import Collatz.Strategy.FirstLightCounting
import Collatz.Structure.CofiniteNaturalDensity
import Collatz.Structure.NaturalDensityCounting
import Collatz.Strategy.FirstLightDensityBound

/-!
# Eventual first-crossing descent at every finite horizon

The accumulator failure bound supplies a coarse explicit exceptional interval
at every horizon H: starts above H*3^H descend at a first coefficient crossing
by H. Unlike the sharper finite certificates, this does not classify the small
starts. It establishes eventual periodicity of actual finite-horizon survival
without imposing a fixed upper bound on H. No existence of a crossing is proved.
-/
namespace Collatz.FirstLightEventual
open FirstLightDescent FirstLightConsequences FirstLightCounting

/-- A coarse threshold removes every possible failure of a crossing by H. -/
theorem descent_above_threshold {H n k : Nat} (hk : k≤H)
    (hn : H*3^H<n) (hf : FirstLight n k) : acceleratedOrbit k n<n := by
  by_cases hd : acceleratedOrbit k n<n
  · exact hd
  · have hfail := failure_bound hf (by omega)
    have ha : oddCount n k≤H := Nat.le_trans (AffineExact.oddCount_le_self n k) hk
    have hp : (3:Nat)^(oddCount n k)≤3^H := Nat.pow_le_pow_right (by decide) ha
    have hnum := Nat.mul_le_mul ha hp
    have hgap : 1≤3*(2^k-3^oddCount n k) := by have := hf.1; omega
    have hlo := Nat.mul_le_mul_right n hgap
    simp only [Nat.one_mul] at hlo
    omega

/-- Any light prefix in the window guarantees a descent for starts above the threshold. -/
theorem descent_by_light_above_threshold {H n k : Nat} (hk : k≤H)
    (hn : H*3^H<n) (hl : 3^oddCount n k<2^k) :
    ∃ j, j≤k ∧ acceleratedOrbit j n<n := by
  obtain ⟨j, hj, hf⟩ := exists_first_light n k hl
  exact ⟨j, hj, descent_above_threshold (by omega) hn hf⟩

/-- Every finite horizon has an exact coefficient classification beyond an explicit cutoff. -/
theorem no_descent_iff_heavy_above_threshold {H n : Nat} (hn : H*3^H<n) :
    (∀ j, j≤H → n≤acceleratedOrbit j n) ↔ heavyCheck H n=true := by
  rw [heavyCheck_iff]
  constructor
  · intro h j hj
    by_cases hl : 3^oddCount n j<2^j
    · obtain ⟨i, hi, hd⟩ := descent_by_light_above_threshold hj hn hl
      have := h i (by omega)
      omega
    · omega
  · intro h j hj
    by_cases hd : acceleratedOrbit j n<n
    · have hl := AffineObstruction.light_of_drop hd
      have := h j hj
      omega
    · omega

/-- Above the cutoff, the first actual descent and first coefficient crossing agree. -/
theorem first_descent_iff_first_light_above_threshold {H n k : Nat}
    (hn : H*3^H<n) (hk : k≤H) : FirstDescent n k ↔ FirstLight n k := by
  constructor
  · intro hd
    refine ⟨AffineObstruction.light_of_drop hd.1, ?_⟩
    intro j hj
    by_cases hl : 3^oddCount n j<2^j
    · obtain ⟨i, hi, hdrop⟩ := descent_by_light_above_threshold (by omega : j≤H) hn hl
      have := hd.2 i (by omega)
      omega
    · omega
  · intro hf
    exact ⟨descent_above_threshold hk hn hf, no_descent_before_first_light hf⟩

/-- At every finite horizon, first stopping times are eventually periodic. -/
theorem first_descent_congr_above_threshold {H n m k : Nat}
    (hn : H*3^H<n) (hm : H*3^H<m) (hk : k≤H)
    (hmod : n%2^H=m%2^H) : FirstDescent n k ↔ FirstDescent m k := by
  rw [first_descent_iff_first_light_above_threshold hn hk,
    first_descent_iff_first_light_above_threshold hm hk]
  exact FirstLightPeriodicity.firstLight_congr hk hmod

/-- Actual orbit survival on the shifted inputs 2,3,... . -/
def ActualSurvival (H n : Nat) : Prop :=
  ∀ j, j≤H → n+2≤acceleratedOrbit j (n+2)

/-- Actual survival differs from the periodic Boolean test only in a finite interval. -/
theorem actual_iff_periodic_eventually (H n : Nat) (hn : H*3^H≤n) :
    ActualSurvival H n ↔ survives H n=true :=
  no_descent_iff_heavy_above_threshold (by omega)

/-- For every horizon, an arbitrary-cutoff actual count is bounded by the
periodic coefficient count plus the explicit exceptional interval. -/
theorem actual_count_upper (H N : Nat) :
    NaturalDensity.predicateCount (ActualSurvival H) N ≤
      H*3^H + NaturalDensity.predicateCount (fun n => survives H n=true) N :=
  NaturalDensity.predicateCount_eventual_mono (H*3^H) N
    (fun n hn => (actual_iff_periodic_eventually H n hn).mp)

/-- The reverse bound controls the count discrepancy in both directions. -/
theorem periodic_count_upper (H N : Nat) :
    NaturalDensity.predicateCount (fun n => survives H n=true) N ≤
      H*3^H + NaturalDensity.predicateCount (ActualSurvival H) N :=
  NaturalDensity.predicateCount_eventual_mono (H*3^H) N
    (fun n hn => (actual_iff_periodic_eventually H n hn).mpr)

/-- Actual finite-horizon survival has an all-cutoff upper bound at every H,
combining a finite exceptional interval and the existing heavy-residue estimate. -/
theorem actual_count_heavy_bound (H N : Nat) :
    NaturalDensity.predicateCount (ActualSurvival H) N ≤
      H*3^H + (N/2^H+1)*Density.heavyCount H := by
  have h := actual_count_upper H N
  rw [NaturalDensity.predicateCount_bool] at h
  exact Nat.le_trans h (Nat.add_le_add_left (survival_count_cutoff_bound H N) _)

end Collatz.FirstLightEventual
