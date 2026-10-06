import Collatz.Research.PassageAtlas.Small051

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_052 : checkInterval 164 206226 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_208274 : checkInterval 164 0 208274 = true :=
  checkInterval_append 164 0 206226 2048
    prefix_206226 small_block_052

end Collatz.Research.PassageAtlas
