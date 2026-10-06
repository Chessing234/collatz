import Collatz.Research.PassageAtlas.Small082

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_083 : checkInterval 164 269714 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_271762 : checkInterval 164 0 271762 = true :=
  checkInterval_append 164 0 269714 2048
    prefix_269714 small_block_083

end Collatz.Research.PassageAtlas
