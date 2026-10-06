import Collatz.Research.PassageAtlas.Small030

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_031 : checkInterval 164 163218 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_165266 : checkInterval 164 0 165266 = true :=
  checkInterval_append 164 0 163218 2048
    prefix_163218 small_block_031

end Collatz.Research.PassageAtlas
