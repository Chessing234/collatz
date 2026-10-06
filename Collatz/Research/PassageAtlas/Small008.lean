import Collatz.Research.PassageAtlas.Small007

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_008 : checkInterval 164 116114 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_118162 : checkInterval 164 0 118162 = true :=
  checkInterval_append 164 0 116114 2048
    prefix_116114 small_block_008

end Collatz.Research.PassageAtlas
