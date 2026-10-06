import Collatz.Research.PassageAtlas.Small109

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_110 : checkInterval 164 325010 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_327058 : checkInterval 164 0 327058 = true :=
  checkInterval_append 164 0 325010 2048
    prefix_325010 small_block_110

end Collatz.Research.PassageAtlas
