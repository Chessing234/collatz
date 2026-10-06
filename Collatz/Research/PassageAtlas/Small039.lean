import Collatz.Research.PassageAtlas.Small038

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_039 : checkInterval 164 179602 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_181650 : checkInterval 164 0 181650 = true :=
  checkInterval_append 164 0 179602 2048
    prefix_179602 small_block_039

end Collatz.Research.PassageAtlas
