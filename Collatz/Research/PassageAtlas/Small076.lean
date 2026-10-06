import Collatz.Research.PassageAtlas.Small075

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_076 : checkInterval 164 255378 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_257426 : checkInterval 164 0 257426 = true :=
  checkInterval_append 164 0 255378 2048
    prefix_255378 small_block_076

end Collatz.Research.PassageAtlas
