import Collatz.Research.PassageAtlas.Small036

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_037 : checkInterval 164 175506 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_177554 : checkInterval 164 0 177554 = true :=
  checkInterval_append 164 0 175506 2048
    prefix_175506 small_block_037

end Collatz.Research.PassageAtlas
