import Collatz.Research.PassageAtlas.Small110

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_111 : checkInterval 164 327058 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_329106 : checkInterval 164 0 329106 = true :=
  checkInterval_append 164 0 327058 2048
    prefix_327058 small_block_111

end Collatz.Research.PassageAtlas
