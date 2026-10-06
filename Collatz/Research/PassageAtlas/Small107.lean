import Collatz.Research.PassageAtlas.Small106

namespace Collatz.Research.PassageAtlas
open FirstLightScan
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Checked trajectories in a new, disjoint exceptional-input block. -/
theorem small_block_107 : checkInterval 164 318866 2048 = true := by decide

/-- Compose blocks through the sound interval API. -/
theorem prefix_320914 : checkInterval 164 0 320914 = true :=
  checkInterval_append 164 0 318866 2048
    prefix_318866 small_block_107

end Collatz.Research.PassageAtlas
