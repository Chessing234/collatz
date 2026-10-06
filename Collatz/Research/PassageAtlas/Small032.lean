import Collatz.Research.PassageAtlas.Small031

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_032 : checkInterval 164 165266 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_167314 : checkInterval 164 0 167314 = true :=
  checkInterval_append 164 0 165266 2048
    prefix_165266 small_block_032

end Collatz.Research.PassageAtlas
