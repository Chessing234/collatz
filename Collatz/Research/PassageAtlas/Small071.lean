import Collatz.Research.PassageAtlas.Small070

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_071 : checkInterval 164 245138 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_247186 : checkInterval 164 0 247186 = true :=
  checkInterval_append 164 0 245138 2048
    prefix_245138 small_block_071

end Collatz.Research.PassageAtlas
