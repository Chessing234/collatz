import Collatz.Research.PassageAtlas.Small024

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_025 : checkInterval 164 150930 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_152978 : checkInterval 164 0 152978 = true :=
  checkInterval_append 164 0 150930 2048
    prefix_150930 small_block_025

end Collatz.Research.PassageAtlas
