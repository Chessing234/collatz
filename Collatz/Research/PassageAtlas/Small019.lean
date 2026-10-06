import Collatz.Research.PassageAtlas.Small018

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_019 : checkInterval 164 138642 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_140690 : checkInterval 164 0 140690 = true :=
  checkInterval_append 164 0 138642 2048
    prefix_138642 small_block_019

end Collatz.Research.PassageAtlas
