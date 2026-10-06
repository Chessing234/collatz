import Collatz.Research.PassageAtlas.Small085

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_086 : checkInterval 164 275858 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_277906 : checkInterval 164 0 277906 = true :=
  checkInterval_append 164 0 275858 2048
    prefix_275858 small_block_086

end Collatz.Research.PassageAtlas
