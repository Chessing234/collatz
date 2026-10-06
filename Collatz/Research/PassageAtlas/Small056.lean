import Collatz.Research.PassageAtlas.Small055

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_056 : checkInterval 164 214418 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_216466 : checkInterval 164 0 216466 = true :=
  checkInterval_append 164 0 214418 2048
    prefix_214418 small_block_056

end Collatz.Research.PassageAtlas
