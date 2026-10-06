import Collatz.Research.PassageAtlas.Small069

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_070 : checkInterval 164 243090 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_245138 : checkInterval 164 0 245138 = true :=
  checkInterval_append 164 0 243090 2048
    prefix_243090 small_block_070

end Collatz.Research.PassageAtlas
