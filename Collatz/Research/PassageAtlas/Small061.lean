import Collatz.Research.PassageAtlas.Small060

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_061 : checkInterval 164 224658 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_226706 : checkInterval 164 0 226706 = true :=
  checkInterval_append 164 0 224658 2048
    prefix_224658 small_block_061

end Collatz.Research.PassageAtlas
