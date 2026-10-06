import Collatz.Research.PassageAtlas.Small059

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_060 : checkInterval 164 222610 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_224658 : checkInterval 164 0 224658 = true :=
  checkInterval_append 164 0 222610 2048
    prefix_222610 small_block_060

end Collatz.Research.PassageAtlas
