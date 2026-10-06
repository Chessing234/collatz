import Collatz.Research.PassageAtlas.Small022

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_023 : checkInterval 164 146834 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_148882 : checkInterval 164 0 148882 = true :=
  checkInterval_append 164 0 146834 2048
    prefix_146834 small_block_023

end Collatz.Research.PassageAtlas
