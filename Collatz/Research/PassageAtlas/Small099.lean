import Collatz.Research.PassageAtlas.Small098

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_099 : checkInterval 164 302482 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_304530 : checkInterval 164 0 304530 = true :=
  checkInterval_append 164 0 302482 2048
    prefix_302482 small_block_099

end Collatz.Research.PassageAtlas
