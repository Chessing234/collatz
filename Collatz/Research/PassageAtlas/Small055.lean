import Collatz.Research.PassageAtlas.Small054

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_055 : checkInterval 164 212370 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_214418 : checkInterval 164 0 214418 = true :=
  checkInterval_append 164 0 212370 2048
    prefix_212370 small_block_055

end Collatz.Research.PassageAtlas
