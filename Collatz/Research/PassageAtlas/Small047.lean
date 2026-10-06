import Collatz.Research.PassageAtlas.Small046

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_047 : checkInterval 164 195986 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_198034 : checkInterval 164 0 198034 = true :=
  checkInterval_append 164 0 195986 2048
    prefix_195986 small_block_047

end Collatz.Research.PassageAtlas
