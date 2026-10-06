import Collatz.Research.PassageAtlas.Small013

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_014 : checkInterval 164 128402 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_130450 : checkInterval 164 0 130450 = true :=
  checkInterval_append 164 0 128402 2048
    prefix_128402 small_block_014

end Collatz.Research.PassageAtlas
