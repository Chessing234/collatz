import Collatz.Research.PassageAtlas.Small111

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_112 : checkInterval 164 329106 1482 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_330588 : checkInterval 164 0 330588 = true :=
  checkInterval_append 164 0 329106 1482
    prefix_329106 small_block_112

end Collatz.Research.PassageAtlas
