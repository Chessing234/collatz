import Collatz.Research.PassageAtlas.Small009

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_010 : checkInterval 164 120210 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_122258 : checkInterval 164 0 122258 = true :=
  checkInterval_append 164 0 120210 2048
    prefix_120210 small_block_010

end Collatz.Research.PassageAtlas
