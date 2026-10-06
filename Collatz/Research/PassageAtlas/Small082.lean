import Collatz.Research.PassageAtlas.Small081

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_082 : checkInterval 164 267666 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_269714 : checkInterval 164 0 269714 = true :=
  checkInterval_append 164 0 267666 2048
    prefix_267666 small_block_082

end Collatz.Research.PassageAtlas
