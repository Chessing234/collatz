import Collatz.Research.PassageAtlas.Small042

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_043 : checkInterval 164 187794 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_189842 : checkInterval 164 0 189842 = true :=
  checkInterval_append 164 0 187794 2048
    prefix_187794 small_block_043

end Collatz.Research.PassageAtlas
