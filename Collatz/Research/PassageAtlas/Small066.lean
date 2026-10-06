import Collatz.Research.PassageAtlas.Small065

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_066 : checkInterval 164 234898 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_236946 : checkInterval 164 0 236946 = true :=
  checkInterval_append 164 0 234898 2048
    prefix_234898 small_block_066

end Collatz.Research.PassageAtlas
