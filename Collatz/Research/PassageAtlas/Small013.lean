import Collatz.Research.PassageAtlas.Small012

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_013 : checkInterval 164 126354 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_128402 : checkInterval 164 0 128402 = true :=
  checkInterval_append 164 0 126354 2048
    prefix_126354 small_block_013

end Collatz.Research.PassageAtlas
