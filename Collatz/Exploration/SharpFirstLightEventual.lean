import Collatz.Exploration.CoefficientGapThreshold
import Collatz.Strategy.FirstLightCounting

/-! Propagate the sharper finite cutoff to survival and first-stopping periodicity.
The proofs reuse existing residue results; no universal crossing is assumed. -/
namespace Collatz.Exploration.SharpFirstLightEventual
open CoefficientGapThreshold FirstLightDescent FirstLightConsequences FirstLightCounting

/-- Any light prefix in the window guarantees a descent for starts above the threshold. -/
theorem descent_by_light_above_threshold {H n k : Nat} (hk : k≤H)
    (hn : H*2^H<3*n) (hl : 3^oddCount n k<2^k) :
    ∃ j, j≤k ∧ acceleratedOrbit j n<n := by
  obtain ⟨j, hj, hf⟩ := exists_first_light n k hl
  exact ⟨j, hj, first_light_below_horizon (by omega) hn hf⟩

/-- Every finite horizon has an exact coefficient classification beyond an explicit cutoff. -/
theorem no_descent_iff_heavy_above_threshold {H n : Nat} (hn : H*2^H<3*n) :
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
    (hn : H*2^H<3*n) (hk : k≤H) : FirstDescent n k ↔ FirstLight n k := by
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
    exact ⟨first_light_below_horizon hk hn hf, no_descent_before_first_light hf⟩

/-- At every finite horizon, first stopping times are eventually periodic. -/
theorem first_descent_congr_above_threshold {H n m k : Nat}
    (hn : H*2^H<3*n) (hm : H*2^H<3*m) (hk : k≤H)
    (hmod : n%2^H=m%2^H) : FirstDescent n k ↔ FirstDescent m k := by
  rw [first_descent_iff_first_light_above_threshold hn hk,
    first_descent_iff_first_light_above_threshold hm hk]
  exact FirstLightPeriodicity.firstLight_congr hk hmod


end Collatz.Exploration.SharpFirstLightEventual
