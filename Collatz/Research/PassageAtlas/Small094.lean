import Collatz.Research.PassageAtlas.Small093

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_094 : checkInterval 164 292242 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_294290 : checkInterval 164 0 294290 = true :=
  checkInterval_append 164 0 292242 2048
    prefix_292242 small_block_094

end Collatz.Research.PassageAtlas
