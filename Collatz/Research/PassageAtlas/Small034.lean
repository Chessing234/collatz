import Collatz.Research.PassageAtlas.Small033

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_034 : checkInterval 164 169362 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_171410 : checkInterval 164 0 171410 = true :=
  checkInterval_append 164 0 169362 2048
    prefix_169362 small_block_034

end Collatz.Research.PassageAtlas
