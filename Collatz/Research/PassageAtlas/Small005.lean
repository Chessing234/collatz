import Collatz.Research.PassageAtlas.Small004

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_005 : checkInterval 164 109970 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_112018 : checkInterval 164 0 112018 = true :=
  checkInterval_append 164 0 109970 2048
    prefix_109970 small_block_005

end Collatz.Research.PassageAtlas
