import Collatz.Research.PassageAtlas.Small102

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_103 : checkInterval 164 310674 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_312722 : checkInterval 164 0 312722 = true :=
  checkInterval_append 164 0 310674 2048
    prefix_310674 small_block_103

end Collatz.Research.PassageAtlas
