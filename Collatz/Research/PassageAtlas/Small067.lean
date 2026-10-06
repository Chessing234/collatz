import Collatz.Research.PassageAtlas.Small066

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_067 : checkInterval 164 236946 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_238994 : checkInterval 164 0 238994 = true :=
  checkInterval_append 164 0 236946 2048
    prefix_236946 small_block_067

end Collatz.Research.PassageAtlas
