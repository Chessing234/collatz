import Collatz.Research.PassageAtlas.Small014

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_015 : checkInterval 164 130450 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_132498 : checkInterval 164 0 132498 = true :=
  checkInterval_append 164 0 130450 2048
    prefix_130450 small_block_015

end Collatz.Research.PassageAtlas
