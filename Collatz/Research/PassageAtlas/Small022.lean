import Collatz.Research.PassageAtlas.Small021

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_022 : checkInterval 164 144786 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_146834 : checkInterval 164 0 146834 = true :=
  checkInterval_append 164 0 144786 2048
    prefix_144786 small_block_022

end Collatz.Research.PassageAtlas
