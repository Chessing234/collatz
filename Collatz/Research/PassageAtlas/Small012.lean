import Collatz.Research.PassageAtlas.Small011

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_012 : checkInterval 164 124306 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_126354 : checkInterval 164 0 126354 = true :=
  checkInterval_append 164 0 124306 2048
    prefix_124306 small_block_012

end Collatz.Research.PassageAtlas
