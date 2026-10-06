import Collatz.Research.PassageAtlas.Small026

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_027 : checkInterval 164 155026 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_157074 : checkInterval 164 0 157074 = true :=
  checkInterval_append 164 0 155026 2048
    prefix_155026 small_block_027

end Collatz.Research.PassageAtlas
