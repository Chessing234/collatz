import Collatz.Research.CoefficientDescent.Intervals

namespace Collatz.Research.CoefficientDescent

open FirstLightDescent DescentIntervals

set_option exponentiation.threshold 300

/-- At one the coefficient can cross without a strict descent. The n>1 premise is essential. -/
theorem one_exception : FirstLight 1 2 ∧ acceleratedOrbit 2 1 = 1 := by decide

/-- The zero representative excludes only the zero index in its one-step class. -/
theorem even_boundary : exactInterval 1 0 = ⟨1, none⟩ := by decide

/-- The one representative similarly excludes the fixed small input. -/
theorem one_boundary : exactInterval 2 1 = ⟨1, none⟩ := by decide

set_option maxRecDepth 20000 in
/-- The known long example is an exact-time ray, not a uniform bound for other inputs. -/
theorem ray_27 (m : Nat) : stoppingTime (2 ^ 59 * m + 27) 59 :=
  FirstDescentClass.stoppingTime_of_classCertificate (by decide) m

/-- Later actual descent need not be the first coefficient crossing. -/
theorem later_descent : acceleratedOrbit 5 3 < 3 ∧ ¬ FirstLight 3 5 := by decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
/-- An explicit input has no coefficient crossing anywhere in the checked horizon. -/
theorem no_crossing_256 : ∀ k : Fin 257,
    2 ^ k.val ≤ 3 ^ oddCount (2 ^ 257 - 1) k.val := by decide

/-- The conditional crossing theorem is not a claim that every input drops by 256. -/
theorem no_uniform_descent_256 :
    ∃ n, 1 < n ∧ ∀ k, k ≤ 256 → n ≤ acceleratedOrbit k n := by
  refine ⟨2 ^ 257 - 1, by decide, ?_⟩
  intro k hk
  exact no_drop_of_heavy (no_crossing_256 ⟨k, by omega⟩)

end Collatz.Research.CoefficientDescent
