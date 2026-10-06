import Collatz.Research.PassageAtlas.Small016

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_017 : checkInterval 164 134546 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_136594 : checkInterval 164 0 136594 = true :=
  checkInterval_append 164 0 134546 2048
    prefix_134546 small_block_017

end Collatz.Research.PassageAtlas
