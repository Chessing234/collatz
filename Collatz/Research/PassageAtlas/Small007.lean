import Collatz.Research.PassageAtlas.Small006

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_007 : checkInterval 164 114066 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_116114 : checkInterval 164 0 116114 = true :=
  checkInterval_append 164 0 114066 2048
    prefix_114066 small_block_007

end Collatz.Research.PassageAtlas
