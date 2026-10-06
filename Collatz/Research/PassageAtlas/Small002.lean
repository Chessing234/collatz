import Collatz.Research.PassageAtlas.Small001

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_002 : checkInterval 164 103826 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_105874 : checkInterval 164 0 105874 = true :=
  checkInterval_append 164 0 103826 2048
    prefix_103826 small_block_002

end Collatz.Research.PassageAtlas
