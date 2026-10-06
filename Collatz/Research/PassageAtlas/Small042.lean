import Collatz.Research.PassageAtlas.Small041

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_042 : checkInterval 164 185746 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_187794 : checkInterval 164 0 187794 = true :=
  checkInterval_append 164 0 185746 2048
    prefix_185746 small_block_042

end Collatz.Research.PassageAtlas
