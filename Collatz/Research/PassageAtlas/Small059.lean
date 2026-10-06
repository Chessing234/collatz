import Collatz.Research.PassageAtlas.Small058

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_059 : checkInterval 164 220562 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_222610 : checkInterval 164 0 222610 = true :=
  checkInterval_append 164 0 220562 2048
    prefix_220562 small_block_059

end Collatz.Research.PassageAtlas
