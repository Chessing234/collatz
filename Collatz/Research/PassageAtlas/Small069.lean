import Collatz.Research.PassageAtlas.Small068

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_069 : checkInterval 164 241042 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_243090 : checkInterval 164 0 243090 = true :=
  checkInterval_append 164 0 241042 2048
    prefix_241042 small_block_069

end Collatz.Research.PassageAtlas
