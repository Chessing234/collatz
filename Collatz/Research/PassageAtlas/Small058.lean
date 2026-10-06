import Collatz.Research.PassageAtlas.Small057

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_058 : checkInterval 164 218514 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_220562 : checkInterval 164 0 220562 = true :=
  checkInterval_append 164 0 218514 2048
    prefix_218514 small_block_058

end Collatz.Research.PassageAtlas
