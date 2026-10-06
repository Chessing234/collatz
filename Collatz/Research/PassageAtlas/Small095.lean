import Collatz.Research.PassageAtlas.Small094

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_095 : checkInterval 164 294290 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_296338 : checkInterval 164 0 296338 = true :=
  checkInterval_append 164 0 294290 2048
    prefix_294290 small_block_095

end Collatz.Research.PassageAtlas
