import Collatz.Research.PassageAtlas.Small104

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_105 : checkInterval 164 314770 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_316818 : checkInterval 164 0 316818 = true :=
  checkInterval_append 164 0 314770 2048
    prefix_314770 small_block_105

end Collatz.Research.PassageAtlas
