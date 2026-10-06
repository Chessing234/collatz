import Collatz.Research.PassageAtlas.Small072

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_073 : checkInterval 164 249234 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_251282 : checkInterval 164 0 251282 = true :=
  checkInterval_append 164 0 249234 2048
    prefix_249234 small_block_073

end Collatz.Research.PassageAtlas
