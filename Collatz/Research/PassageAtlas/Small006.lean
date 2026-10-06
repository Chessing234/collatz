import Collatz.Research.PassageAtlas.Small005

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_006 : checkInterval 164 112018 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_114066 : checkInterval 164 0 114066 = true :=
  checkInterval_append 164 0 112018 2048
    prefix_112018 small_block_006

end Collatz.Research.PassageAtlas
