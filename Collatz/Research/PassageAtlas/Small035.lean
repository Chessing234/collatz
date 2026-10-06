import Collatz.Research.PassageAtlas.Small034

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_035 : checkInterval 164 171410 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_173458 : checkInterval 164 0 173458 = true :=
  checkInterval_append 164 0 171410 2048
    prefix_171410 small_block_035

end Collatz.Research.PassageAtlas
