import Collatz.Research.PassageAtlas.Small103

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_104 : checkInterval 164 312722 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_314770 : checkInterval 164 0 314770 = true :=
  checkInterval_append 164 0 312722 2048
    prefix_312722 small_block_104

end Collatz.Research.PassageAtlas
