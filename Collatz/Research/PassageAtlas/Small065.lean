import Collatz.Research.PassageAtlas.Small064

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_065 : checkInterval 164 232850 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_234898 : checkInterval 164 0 234898 = true :=
  checkInterval_append 164 0 232850 2048
    prefix_232850 small_block_065

end Collatz.Research.PassageAtlas
