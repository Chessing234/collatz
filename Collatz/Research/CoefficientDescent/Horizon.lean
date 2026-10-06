import Collatz.Research.CoefficientDescent.Gap
import Collatz.Research.CoefficientDescent.SmallInputs

/-! The input n is unbounded. Only the assumed coefficient-crossing time is bounded. -/
namespace Collatz.Research.CoefficientDescent

open FirstLightDescent

/-- Every first coefficient crossing through 256 is a genuine descent, for all n>1. -/
theorem descent_at_firstLight_le_256 {n k : Nat} (hn : 1 < n) (hk : k ≤ 256)
    (hf : FirstLight n k) : acceleratedOrbit k n < n :=
  descent_of_gap_and_small gap_bound_256 small_inputs hn hk hf

/-- Equality of exact coefficient and actual stopping events through time 256. -/
theorem stopping_iff_firstLight_le_256 {n k : Nat} (hn : 1 < n) (hk : k ≤ 256) :
    stoppingTime n k ↔ FirstLight n k :=
  stopping_iff_firstLight_of_horizon
    (fun _ _ h hK hF => descent_at_firstLight_le_256 h hK hF) hn hk

/-- A hypothetical discrepancy must occur strictly after the checked horizon. -/
theorem discrepancy_after_256 {n k : Nat} (hn : 1 < n) (hf : FirstLight n k)
    (hfail : n ≤ acceleratedOrbit k n) : 256 < k := by
  apply Classical.byContradiction
  intro h
  have := descent_at_firstLight_le_256 hn (by omega) hf
  omega

/-- An actual first descent whose coefficient event differs must also be late. -/
theorem delayed_stopping_after_256 {n k : Nat} (hs : stoppingTime n k)
    (hf : ¬ FirstLight n k) : 256 < k := by
  apply Classical.byContradiction
  intro h
  exact hf ((stopping_iff_firstLight_le_256 (start_gt_one hs) (by omega)).mp hs)

end Collatz.Research.CoefficientDescent
