import Collatz.Research.PassageAtlas.Small100

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_101 : checkInterval 164 306578 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_308626 : checkInterval 164 0 308626 = true :=
  checkInterval_append 164 0 306578 2048
    prefix_306578 small_block_101

end Collatz.Research.PassageAtlas
