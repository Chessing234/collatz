import Collatz.Research.PassageAtlas.Small029

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_030 : checkInterval 164 161170 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_163218 : checkInterval 164 0 163218 = true :=
  checkInterval_append 164 0 161170 2048
    prefix_161170 small_block_030

end Collatz.Research.PassageAtlas
