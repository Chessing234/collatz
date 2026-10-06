import Collatz.Research.PassageAtlas.Small112

namespace Collatz.Research.PassageAtlas
open FirstLightDescent FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0

/-- Every exceptional input above one has a first-crossing descent by 164. -/
theorem small_starts_330588 : ∀ n : Fin 330588, 1 < n.val →
    ∃ k : Fin 165, FirstLight n.val k.val ∧ acceleratedOrbit k.val n.val < n.val := by
  intro n hn
  exact checkInterval_sound 164 0 330588 prefix_330588 n.val (by omega) n.isLt hn

/-- A witness attaining the small-input crossing horizon; it is not a counterexample. -/
theorem small_horizon_attained : FirstLight 270271 164 ∧ acceleratedOrbit 164 270271 < 270271 := by decide

end Collatz.Research.PassageAtlas
