import Collatz.Research.PassageAtlas.Small061

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_062 : checkInterval 164 226706 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_228754 : checkInterval 164 0 228754 = true :=
  checkInterval_append 164 0 226706 2048
    prefix_226706 small_block_062

end Collatz.Research.PassageAtlas
