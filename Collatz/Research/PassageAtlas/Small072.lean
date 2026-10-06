import Collatz.Research.PassageAtlas.Small071

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_072 : checkInterval 164 247186 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_249234 : checkInterval 164 0 249234 = true :=
  checkInterval_append 164 0 247186 2048
    prefix_247186 small_block_072

end Collatz.Research.PassageAtlas
