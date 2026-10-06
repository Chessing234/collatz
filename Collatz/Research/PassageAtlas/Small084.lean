import Collatz.Research.PassageAtlas.Small083

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_084 : checkInterval 164 271762 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_273810 : checkInterval 164 0 273810 = true :=
  checkInterval_append 164 0 271762 2048
    prefix_271762 small_block_084

end Collatz.Research.PassageAtlas
