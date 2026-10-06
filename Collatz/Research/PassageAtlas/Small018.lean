import Collatz.Research.PassageAtlas.Small017

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_018 : checkInterval 164 136594 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_138642 : checkInterval 164 0 138642 = true :=
  checkInterval_append 164 0 136594 2048
    prefix_136594 small_block_018

end Collatz.Research.PassageAtlas
