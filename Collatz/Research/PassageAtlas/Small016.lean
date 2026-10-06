import Collatz.Research.PassageAtlas.Small015

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_016 : checkInterval 164 132498 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_134546 : checkInterval 164 0 134546 = true :=
  checkInterval_append 164 0 132498 2048
    prefix_132498 small_block_016

end Collatz.Research.PassageAtlas
