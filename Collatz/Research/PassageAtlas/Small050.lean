import Collatz.Research.PassageAtlas.Small049

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_050 : checkInterval 164 202130 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_204178 : checkInterval 164 0 204178 = true :=
  checkInterval_append 164 0 202130 2048
    prefix_202130 small_block_050

end Collatz.Research.PassageAtlas
