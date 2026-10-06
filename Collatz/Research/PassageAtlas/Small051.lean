import Collatz.Research.PassageAtlas.Small050

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_051 : checkInterval 164 204178 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_206226 : checkInterval 164 0 206226 = true :=
  checkInterval_append 164 0 204178 2048
    prefix_204178 small_block_051

end Collatz.Research.PassageAtlas
