import Collatz.Research.PassageAtlas.Small067

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_068 : checkInterval 164 238994 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_241042 : checkInterval 164 0 241042 = true :=
  checkInterval_append 164 0 238994 2048
    prefix_238994 small_block_068

end Collatz.Research.PassageAtlas
