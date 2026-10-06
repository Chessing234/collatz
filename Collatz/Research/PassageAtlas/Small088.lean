import Collatz.Research.PassageAtlas.Small087

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_088 : checkInterval 164 279954 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_282002 : checkInterval 164 0 282002 = true :=
  checkInterval_append 164 0 279954 2048
    prefix_279954 small_block_088

end Collatz.Research.PassageAtlas
