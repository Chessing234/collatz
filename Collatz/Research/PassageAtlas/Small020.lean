import Collatz.Research.PassageAtlas.Small019

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_020 : checkInterval 164 140690 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_142738 : checkInterval 164 0 142738 = true :=
  checkInterval_append 164 0 140690 2048
    prefix_140690 small_block_020

end Collatz.Research.PassageAtlas
