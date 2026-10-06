import Collatz.Research.PassageAtlas.Small105

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_106 : checkInterval 164 316818 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_318866 : checkInterval 164 0 318866 = true :=
  checkInterval_append 164 0 316818 2048
    prefix_316818 small_block_106

end Collatz.Research.PassageAtlas
