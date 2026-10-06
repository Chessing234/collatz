import Collatz.Research.PassageAtlas.Small091

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_092 : checkInterval 164 288146 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_290194 : checkInterval 164 0 290194 = true :=
  checkInterval_append 164 0 288146 2048
    prefix_288146 small_block_092

end Collatz.Research.PassageAtlas
