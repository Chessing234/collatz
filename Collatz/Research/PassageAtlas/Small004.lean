import Collatz.Research.PassageAtlas.Small003

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_004 : checkInterval 164 107922 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_109970 : checkInterval 164 0 109970 = true :=
  checkInterval_append 164 0 107922 2048
    prefix_107922 small_block_004

end Collatz.Research.PassageAtlas
