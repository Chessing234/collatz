import Collatz.Research.PassageAtlas.Small028

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_029 : checkInterval 164 159122 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_161170 : checkInterval 164 0 161170 = true :=
  checkInterval_append 164 0 159122 2048
    prefix_159122 small_block_029

end Collatz.Research.PassageAtlas
