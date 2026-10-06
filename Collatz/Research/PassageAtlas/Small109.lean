import Collatz.Research.PassageAtlas.Small108

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_109 : checkInterval 164 322962 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_325010 : checkInterval 164 0 325010 = true :=
  checkInterval_append 164 0 322962 2048
    prefix_322962 small_block_109

end Collatz.Research.PassageAtlas
