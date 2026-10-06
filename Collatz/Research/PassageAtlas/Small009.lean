import Collatz.Research.PassageAtlas.Small008

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_009 : checkInterval 164 118162 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_120210 : checkInterval 164 0 120210 = true :=
  checkInterval_append 164 0 118162 2048
    prefix_118162 small_block_009

end Collatz.Research.PassageAtlas
