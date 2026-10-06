import Collatz.Research.PassageAtlas.Small099

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_100 : checkInterval 164 304530 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_306578 : checkInterval 164 0 306578 = true :=
  checkInterval_append 164 0 304530 2048
    prefix_304530 small_block_100

end Collatz.Research.PassageAtlas
