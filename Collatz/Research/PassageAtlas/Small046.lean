import Collatz.Research.PassageAtlas.Small045

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_046 : checkInterval 164 193938 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_195986 : checkInterval 164 0 195986 = true :=
  checkInterval_append 164 0 193938 2048
    prefix_193938 small_block_046

end Collatz.Research.PassageAtlas
