import Collatz.Research.PassageAtlas.Small086

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_087 : checkInterval 164 277906 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_279954 : checkInterval 164 0 279954 = true :=
  checkInterval_append 164 0 277906 2048
    prefix_277906 small_block_087

end Collatz.Research.PassageAtlas
