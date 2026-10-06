import Collatz.Research.PassageAtlas.Small096

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_097 : checkInterval 164 298386 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_300434 : checkInterval 164 0 300434 = true :=
  checkInterval_append 164 0 298386 2048
    prefix_298386 small_block_097

end Collatz.Research.PassageAtlas
