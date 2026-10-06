import Collatz.Research.PassageAtlas.Small037

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_038 : checkInterval 164 177554 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_179602 : checkInterval 164 0 179602 = true :=
  checkInterval_append 164 0 177554 2048
    prefix_177554 small_block_038

end Collatz.Research.PassageAtlas
