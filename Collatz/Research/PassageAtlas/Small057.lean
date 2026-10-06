import Collatz.Research.PassageAtlas.Small056

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_057 : checkInterval 164 216466 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_218514 : checkInterval 164 0 218514 = true :=
  checkInterval_append 164 0 216466 2048
    prefix_216466 small_block_057

end Collatz.Research.PassageAtlas
