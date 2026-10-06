import Collatz.Research.PassageAtlas.Small020

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_021 : checkInterval 164 142738 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_144786 : checkInterval 164 0 144786 = true :=
  checkInterval_append 164 0 142738 2048
    prefix_142738 small_block_021

end Collatz.Research.PassageAtlas
