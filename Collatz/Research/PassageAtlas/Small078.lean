import Collatz.Research.PassageAtlas.Small077

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_078 : checkInterval 164 259474 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_261522 : checkInterval 164 0 261522 = true :=
  checkInterval_append 164 0 259474 2048
    prefix_259474 small_block_078

end Collatz.Research.PassageAtlas
