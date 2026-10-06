import Collatz.Research.PassageAtlas.Small101

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_102 : checkInterval 164 308626 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_310674 : checkInterval 164 0 310674 = true :=
  checkInterval_append 164 0 308626 2048
    prefix_308626 small_block_102

end Collatz.Research.PassageAtlas
