import Collatz.Research.PassageAtlas.Small010

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_011 : checkInterval 164 122258 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_124306 : checkInterval 164 0 124306 = true :=
  checkInterval_append 164 0 122258 2048
    prefix_122258 small_block_011

end Collatz.Research.PassageAtlas
