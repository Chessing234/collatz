import Collatz.Research.PassageAtlas.Small035

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_036 : checkInterval 164 173458 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_175506 : checkInterval 164 0 175506 = true :=
  checkInterval_append 164 0 173458 2048
    prefix_173458 small_block_036

end Collatz.Research.PassageAtlas
