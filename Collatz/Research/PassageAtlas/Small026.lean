import Collatz.Research.PassageAtlas.Small025

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_026 : checkInterval 164 152978 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_155026 : checkInterval 164 0 155026 = true :=
  checkInterval_append 164 0 152978 2048
    prefix_152978 small_block_026

end Collatz.Research.PassageAtlas
