import Collatz.Research.PassageAtlas.Small107

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_108 : checkInterval 164 320914 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_322962 : checkInterval 164 0 322962 = true :=
  checkInterval_append 164 0 320914 2048
    prefix_320914 small_block_108

end Collatz.Research.PassageAtlas
