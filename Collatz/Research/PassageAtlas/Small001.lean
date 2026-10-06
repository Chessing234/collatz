import Collatz.Research.PassageAtlas.Small000

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_001 : checkInterval 164 101778 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_103826 : checkInterval 164 0 103826 = true :=
  checkInterval_append 164 0 101778 2048
    prefix_101778 small_block_001

end Collatz.Research.PassageAtlas
