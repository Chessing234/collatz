import Collatz.Research.PassageAtlas.Small090

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_091 : checkInterval 164 286098 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_288146 : checkInterval 164 0 288146 = true :=
  checkInterval_append 164 0 286098 2048
    prefix_286098 small_block_091

end Collatz.Research.PassageAtlas
