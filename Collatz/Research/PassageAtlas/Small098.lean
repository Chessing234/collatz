import Collatz.Research.PassageAtlas.Small097

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_098 : checkInterval 164 300434 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_302482 : checkInterval 164 0 302482 = true :=
  checkInterval_append 164 0 300434 2048
    prefix_300434 small_block_098

end Collatz.Research.PassageAtlas
